"""Functional record updates must not overwrite the original bound value."""
import copy
from pathlib import Path
import subprocess
import sys
import unittest
from test_native_emitter import QUAD

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from emit_rust import emit_module, EmitError


def fixture():
    return {'version':1,'name':'generate','domain':'field17',
            'inputs':[{'name':'old','type':QUAD},{'name':'value','type':'scalar'}],
            'output':QUAD,'body':{
                'tag':'let','op':'record.set','args':[0,1],'regions':[],
                'static':{'index':1},'result':QUAD,'next':{
                    'tag':'let','op':'record.get','args':[1],'regions':[],
                    'static':{'index':1},'result':'scalar','next':{
                        'tag':'let','op':'record.get','args':[1],'regions':[],
                        'static':{'index':1},'result':'scalar','next':{
                            'tag':'let','op':'record.make','args':[1,0],'regions':[],
                            'result':QUAD,'next':{'tag':'ret','ref':0}}}}}}


class StructSetTests(unittest.TestCase):
    def test_set_preserves_original_and_updates_only_requested_field(self):
        try: code=emit_module(fixture())
        except EmitError as e: self.fail(str(e))
        path=ROOT/'backend/src/bin/emitter_struct_set.rs'
        path.write_text(code+'''\nfn main() {
    let old=QuadWitness { square: witgen_native::F17::from(3), output: witgen_native::F17::from(8) };
    let out=generate(old.clone(),witgen_native::F17::from(11)).unwrap();
    assert_eq!(witgen_native::f17_to_u64(old.output),8);
    assert_eq!(witgen_native::f17_to_u64(out.square),8);
    assert_eq!(witgen_native::f17_to_u64(out.output),11);
}\n''')
        r=subprocess.run(['cargo','run','--quiet','--locked','--manifest-path','backend/Cargo.toml',
                          '--bin','emitter_struct_set'],cwd=ROOT,text=True,capture_output=True,timeout=90)
        self.assertEqual(r.returncode,0,r.stdout+r.stderr)

    def test_set_rejects_bad_index_value_and_result_types(self):
        good=fixture()
        emit_module(good)
        for index in [-1,2,True,'1']:
            bad=copy.deepcopy(good);bad['body']['static']['index']=index
            with self.assertRaises(EmitError):emit_module(bad)
        bad=copy.deepcopy(good);bad['inputs'][1]['type']='bool'
        with self.assertRaises(EmitError):emit_module(bad)
        bad=copy.deepcopy(good);bad['body']['result']='scalar'
        with self.assertRaises(EmitError):emit_module(bad)

if __name__=='__main__':unittest.main()
