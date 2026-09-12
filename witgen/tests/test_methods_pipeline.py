"""Real typed field/call/U64/curve programs are replayed end to end."""
from pathlib import Path
import subprocess
import json
import os
import hashlib
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]

class MethodsPipelineTests(unittest.TestCase):
    def test_actual_methods_pipeline_and_shared_u64_bodies(self):
        runner = ROOT/'tools/run_methods.py'
        self.assertTrue(runner.exists(), 'typed methods pipeline is missing')
        # Keep the isolated target as replay evidence; never let a default binary
        # make a redirected Cargo build appear to have executed the new artifact.
        (ROOT/'artifacts').mkdir(exist_ok=True)
        target = Path(tempfile.mkdtemp(prefix='methods-target-', dir=ROOT/'artifacts'))
        default = ROOT/'backend/target/debug/witgen-methods'
        saved = target/'saved-default-binary'
        if default.exists():
            default.rename(saved)
        try:
            self.assertFalse(default.exists())
            result = subprocess.run(['python3',str(runner)],cwd=ROOT,text=True,
                capture_output=True,timeout=600,
                env={**os.environ, 'CARGO_TARGET_DIR':str(target), 'CARGO_NET_OFFLINE':'true'})
            (target/'pipeline.log').write_text(result.stdout+result.stderr)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            report=json.loads((ROOT/'artifacts/methods/verification.json').read_text())
            executable=Path(report['executed_binary']['path'])
            self.assertTrue(executable.is_relative_to(target))
            self.assertFalse(default.exists())
            self.assertEqual(report['executed_binary']['sha256'],
                hashlib.sha256(executable.read_bytes()).hexdigest())
            self.assertEqual(report['build']['environment']['CARGO_TARGET_DIR'],str(target))
            events=[json.loads(line) for line in (ROOT/'artifacts/methods/cargo-artifacts.jsonl').read_text().splitlines()]
            artifacts=[e for e in events if e.get('reason')=='compiler-artifact'
                and e['target']['name']=='witgen-methods' and e.get('executable')]
            self.assertEqual([e['executable'] for e in artifacts],[str(executable)])
            executions=[c['argv'][0] for c in report['commands'] if c['log'] in
                ('native-results.jsonl','negative-results.jsonl')]
            self.assertEqual(executions,[str(executable),str(executable)])
        finally:
            if saved.exists():
                saved.rename(default)
        self.assertEqual(report['status'],'PASS')
        self.assertEqual(report['u64_generic_bodies'],3)
        self.assertTrue(report['calls_retained'])
        self.assertTrue(report['no_u64_bigint_field_arithmetic'])
        self.assertTrue(report['affine_invalid_rejected'])
        self.assertTrue(report['infinity_explicit'])
        self.assertGreater(report['native_cases'],100)
        self.assertEqual(report['curve_backend'],'arkworks')
        for name in ('u64-tests.json','u64-shared.json'):
            for directory in ('artifacts/u64','artifacts/methods'):
                path=f'{directory}/{name}'
                self.assertIn(path,report['artifact_hashes'])
        for name in ('native-requests.jsonl','case-results.jsonl',
                     'negative-requests.jsonl','negative-case-results.jsonl',
                     'source-config.json','required-cases.json'):
            self.assertIn('artifacts/methods/'+name,report['artifact_hashes'])
        records=[json.loads(line) for line in (ROOT/'artifacts/methods/case-results.jsonl').read_text().splitlines()]
        requests=[json.loads(line) for line in (ROOT/'artifacts/methods/native-requests.jsonl').read_text().splitlines()]
        results=[json.loads(line) for line in (ROOT/'artifacts/methods/native-results.jsonl').read_text().splitlines()]
        self.assertEqual(len(records),408)
        self.assertEqual(len(requests),len(records))
        for i,record in enumerate(records):
            self.assertEqual(record['case_index'],i)
            self.assertEqual(requests[i],{k:record['case'][k] for k in ('program','inputs')})
            self.assertEqual(record['result'],results[i])
            self.assertEqual(record['normalized'],record['independent_expected'])
        self.assertEqual(report['case_coverage'],{'total':408,'unique':391,'intentional_duplicates':17})
        self.assertIn('configuration_hashes',report['build'])
        self.assertIn('rustc_version',report['build'])
        self.assertIn('cargo_version',report['build'])

if __name__=='__main__': unittest.main()
