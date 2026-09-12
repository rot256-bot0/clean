"""Exact-case controls replay real exported cases, not made-up executions."""
from collections import Counter
from pathlib import Path
import copy
import json
import sys
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
import run_methods as runner


def exported_cases():
    reference=ROOT/'artifacts/methods/bundle/reference.json'
    if not reference.exists():
        raise unittest.SkipTest('run test_methods_pipeline.py to create real exports')
    cases=json.loads(reference.read_text())
    fixtures=json.loads((ROOT/'artifacts/u64/u64-tests.json').read_text())['fixtures']
    return cases+[dict(x,mode='u64') for x in fixtures]


class IndependentCurveCasesTests(unittest.TestCase):
    def test_curve_api_multiset_and_independent_arithmetic(self):
        cases=runner.required_cases()
        by_program={name:[c for c in cases if c['program']==name]
                    for name in {c['program'] for c in cases}}
        for name,count in {'secp_mixed_fields':7,'curve_eq':25,'curve_msm':8,
                           'curve_msm_constructed':5,'curve_const_generator':1,
                           'curve_const_identity':1}.items():
            self.assertEqual(len(by_program.get(name,[])),count,name)
        self.assertEqual([c['inputs'] for c in by_program['secp_mixed_fields']],
                         [[str(s),str(t)] for s,t in [(0,0),(1,1),(1,0),(2,3),
                          (runner.N-1,1),(2**200+7,2**129+9),(17,19)]])
        self.assertIsNone(runner.expected_independent({'program':'secp_mixed_fields','inputs':['1','0']}))
        self.assertEqual(runner.expected_independent({'program':'curve_msm','inputs':[[]]}),{'infinity':True})
        self.assertIs(runner.expected_independent({'program':'curve_eq','inputs':['00','00']}),True)
        self.assertEqual(runner.expected_independent({'program':'curve_const_generator','inputs':[]}),
                         runner.point_reference(runner.G))


class ExactCoverageTests(unittest.TestCase):
    def check_coverage(self,cases):
        self.assertTrue(callable(getattr(runner,'validate_case_coverage',None)),
                        'independent exact multiset gate is missing')
        return runner.validate_case_coverage(cases)

    def test_source_prescribed_multiset_includes_intentional_duplicates(self):
        cases=exported_cases()
        self.check_coverage(cases)
        counts=Counter((c['program'],json.dumps(c['inputs'])) for c in cases)
        specified=Counter((c['program'],json.dumps(c['inputs'])) for c in runner.required_cases())
        self.assertEqual(counts,specified)
        self.assertEqual(len(cases),sum(specified.values()))
        self.assertEqual(len(counts),len(specified))
        self.assertEqual(sum(n-1 for n in counts.values()),sum(n-1 for n in specified.values()))
        self.assertGreater(sum(n-1 for n in counts.values()),0)
        self.check_coverage(list(reversed(cases)))

    def test_replacing_required_cases_preserves_old_gates_but_fails(self):
        original=exported_cases()
        controls=[('secp_mixed_fields',['1','0']),('curve_eq',['00','00']),
                  ('curve_msm',[[]]),('curve_msm_constructed',['0','04'+format(runner.G[0],'064x')+format(runner.G[1],'064x')]),
                  ('secp_from_affine',[['0','0']]),
                  ('secp_from_affine',[['1','1']]),
                  ('secp_to_affine',['00']),
                  ('secp_affine_roundtrip',['00']),
                  ('field_0_u64_methods',[str(int(runner.FIELD_MODULI[0])-1)]*2),
                  ('field.1.mul',[str(int(runner.FIELD_MODULI[1])-1)]*2),
                  ('field.2.square',['0'])]
        for name,inputs in controls:
            with self.subTest(program=name,inputs=inputs):
                cases=copy.deepcopy(original)
                index=next(i for i,c in enumerate(cases) if c['program']==name and c['inputs']==inputs)
                replacement=next(c for c in cases if c['program']==name and c['inputs']!=inputs)
                cases[index]=copy.deepcopy(replacement)
                self.assertEqual(Counter(c['program'] for c in cases),Counter(c['program'] for c in original))
                with self.assertRaisesRegex(ValueError,'case multiset mismatch'):
                    self.check_coverage(cases)

    def test_dropping_one_intentional_duplicate_fails(self):
        cases=exported_cases()
        negative_g='04'+format(runner.G[0],'064x')+format((-runner.G[1])%runner.P,'064x')
        i=next(i for i,c in enumerate(cases) if c['program']=='secp_to_affine' and c['inputs']==[negative_g])
        del cases[i]
        with self.assertRaisesRegex(ValueError,'case multiset mismatch'):
            self.check_coverage(cases)


def exported_output_types():
    result={}
    for file in (ROOT/'artifacts/methods/bundle').glob('*.json'):
        module=json.loads(file.read_text())
        if isinstance(module,dict) and 'output' in module:
            result[module['name']]=module['output']
    shared=json.loads((ROOT/'artifacts/u64/u64-shared.json').read_text())
    result.update((p['name'],p['output']) for p in shared['programs'])
    return result


class ExecutedAssertionTests(unittest.TestCase):
    def replay(self):
        cases=exported_cases()
        path=ROOT/'artifacts/methods/native-results.jsonl'
        if not path.exists():
            raise unittest.SkipTest('run methods pipeline for real native results')
        results=[json.loads(line) for line in path.read_text().splitlines()]
        self.assertTrue(callable(getattr(runner,'validate_results',None)),
                        'identified execution assertions are missing')
        return cases,results,exported_output_types()

    def test_flags_are_backed_by_identified_raw_executions(self):
        cases,results,types=self.replay()
        records=runner.validate_results(cases,results,types)
        assertions=runner.semantic_assertions(records)
        self.assertEqual(set(assertions),{'affine_invalid_rejected','infinity_explicit'})
        self.assertEqual([len(v) for v in assertions.values()],[2,2])
        for checks in assertions.values():
            for check in checks:
                self.assertTrue(check['passed'])
                self.assertEqual(records[check['case_index']]['result'],{'ok':None})

    def test_missing_affine_and_identity_assertions_fail_without_coverage_gate(self):
        cases,results,types=self.replay()
        records=runner.validate_results(cases,results,types)
        for name,inputs in [('secp_from_affine',[['0','0']]),
                            ('secp_from_affine',[['1','1']]),
                            ('secp_to_affine',['00']),('secp_affine_roundtrip',['00'])]:
            with self.subTest(name=name,inputs=inputs):
                filtered=[r for r in records if not (r['case']['program']==name and r['case']['inputs']==inputs)]
                with self.assertRaisesRegex(ValueError,'semantic assertion'):
                    runner.semantic_assertions(filtered)

    def test_result_tampering_and_modulus_repair_fail(self):
        cases,results,types=self.replay()
        for name,inputs in [('secp_from_affine',[['0','0']]),
                            ('secp_to_affine',['00']),('field_0_native',['0','0'])]:
            with self.subTest(name=name):
                index=next(i for i,c in enumerate(cases) if c['program']==name and c['inputs']==inputs)
                altered=copy.deepcopy(results)
                altered[index]={'ok':str(int(results[index]['ok'])+int(runner.FIELD_MODULI[0]))} if name.startswith('field_') else {'ok':'00'}
                with self.assertRaises(ValueError):
                    runner.validate_results(cases,altered,types)


class NestedOptionComparatorTests(unittest.TestCase):
    def test_recursive_list_pair_options_validate_leaves_and_keep_null_tags(self):
        field={'field':0,'modulus':runner.FIELD_MODULI[0]}
        ty={'list':{'option':{'option':{'pair':[field,{'list':field}]}}}}
        good=[None,{'some':None},{'some':['7',['0','17']]}]
        self.assertEqual(runner.normalize(ty,good),good)
        for bad in (None,{},[[]],[{'some':['7',[runner.FIELD_MODULI[0]]]}],
                    [{'some':['7',['01']]}],[{'some':['7',None]}],
                    [{'some':['7',[]],'extra':0}]):
            with self.subTest(bad=bad),self.assertRaises(ValueError):
                runner.normalize(ty,bad)
        point={'point':{'id':'secp256k1','base':{'field':1,'modulus':runner.FIELD_MODULI[1]},
                        'scalar':{'field':2,'modulus':runner.FIELD_MODULI[2]},
                        'weierstrass':['0','0','0','0','7']}}
        self.assertEqual(runner.normalize({'list':{'option':point}},[None,'00']),
                         [None,{'infinity':True}])

    def test_bool_outputs_do_not_accept_integer_aliases(self):
        self.assertIs(runner.normalize('bool',True),True)
        for bad in (0,1,'true',None):
            with self.subTest(bad=bad),self.assertRaises(ValueError):
                runner.normalize('bool',bad)

    def test_nested_tags_remain_distinct(self):
        field={'field':0,'modulus':runner.FIELD_MODULI[0]}
        nested={'option':{'option':field}}
        for value in [None,{'some':None},{'some':'7'}]:
            with self.subTest(value=value):
                self.assertEqual(runner.normalize(nested,value),value)
        triple={'option':nested}
        for value in [None,{'some':None},{'some':{'some':None}},{'some':{'some':'7'}}]:
            self.assertEqual(runner.normalize(triple,value),value)

    def test_nested_tags_are_exact_and_fields_stay_canonical(self):
        nested={'option':{'option':{'field':0,'modulus':runner.FIELD_MODULI[0]}}}
        for value in ['7',{}, {'some':'7','extra':0},{'some':runner.FIELD_MODULI[0]}]:
            with self.subTest(value=value),self.assertRaises(ValueError):
                runner.normalize(nested,value)


if __name__=='__main__':
    unittest.main()
