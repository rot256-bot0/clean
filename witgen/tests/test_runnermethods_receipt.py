"""Failure cleanup and artifact parser controls; no simulated native output."""
from pathlib import Path
import copy
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
import run_methods as runner


class FailureCleanupTests(unittest.TestCase):
    def test_missing_source_preflight_removes_stale_pass(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);art=root/'artifacts/methods';art.mkdir(parents=True)
            stale=art/'verification.json';stale.write_text('{"status":"PASS"}')
            with patch.object(runner,'ROOT',root),patch.object(runner,'ART',art):
                with self.assertRaises(FileNotFoundError):
                    runner.run_all()
            self.assertFalse(stale.exists())

    def test_import_preflight_removes_stale_pass(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);tools=root/'tools';tools.mkdir()
            shutil.copyfile(ROOT/'tools/run_methods.py',tools/'run_methods.py')
            art=root/'artifacts/methods';art.mkdir(parents=True)
            stale=art/'verification.json';stale.write_text('{"status":"PASS"}')
            # Missing project imports are a real preflight failure before run_all.
            result=subprocess.run([sys.executable,'-I',str(tools/'run_methods.py')],
                                  text=True,capture_output=True,cwd=root)
            self.assertNotEqual(result.returncode,0)
            self.assertIn('ModuleNotFoundError',result.stderr)
            self.assertFalse(stale.exists(),'project import failure retained stale PASS')


class CargoArtifactTests(unittest.TestCase):
    def events(self):
        path=ROOT/'artifacts/methods/cargo-artifacts.jsonl'
        if not path.exists():
            raise unittest.SkipTest('run methods pipeline to record a real Cargo build')
        return path.read_text()

    def test_select_real_artifact_and_fail_on_missing_or_duplicate(self):
        text=self.events()
        event=runner.cargo_executable(text)
        self.assertEqual(event['target']['name'],'witgen-methods')
        self.assertTrue(Path(event['executable']).is_file())
        with self.assertRaisesRegex(ValueError,'exactly one Cargo'):
            runner.cargo_executable('')
        with self.assertRaisesRegex(ValueError,'exactly one Cargo'):
            runner.cargo_executable(text.rstrip()+'\n'+json.dumps(event))
        missing=[line for line in text.splitlines() if json.loads(line)!=event]
        with self.assertRaisesRegex(ValueError,'exactly one Cargo'):
            runner.cargo_executable('\n'.join(missing))


class HistoricalReceiptTests(unittest.TestCase):
    def receipt(self):
        self.assertTrue(callable(getattr(runner,'validate_historical_receipt',None)),
                        'historical receipt integrity validation is missing')
        receipt=ROOT/'artifacts/methods/verification.json'
        if not receipt.exists():
            raise unittest.SkipTest('run the actual methods pipeline to create a PASS receipt')
        return receipt

    def test_real_receipt_replays_complete_records(self):
        report=runner.validate_historical_receipt(self.receipt())
        self.assertEqual(report['status'],'PASS')
        self.assertEqual(report['native_cases'],len(runner.required_cases()))

    def test_every_consumed_u64_copy_and_execution_artifact_is_bound(self):
        receipt=self.receipt()
        report=runner.validate_historical_receipt(receipt)
        paths=[ROOT/directory/name for directory in ('artifacts/u64','artifacts/methods')
               for name in ('u64-tests.json','u64-shared.json')]
        paths += [ROOT/'artifacts/methods'/name for name in ('bundle/reference.json',
            'native-requests.jsonl','native-results.jsonl','case-results.jsonl',
            'negative-requests.jsonl','negative-case-results.jsonl','source-config.json','required-cases.json')]
        manifest=json.loads((ROOT/'artifacts/methods/bundle/manifest.json').read_text())
        paths += [ROOT/'artifacts/methods/bundle'/(entry['name']+'.json') for entry in manifest['programs']]
        paths.append(Path(report['executed_binary']['path']))
        for path in paths:
            with self.subTest(path=str(path)):
                data=path.read_bytes()
                try:
                    path.write_bytes(data+b'\n')
                    with self.assertRaisesRegex(ValueError,'hash mismatch'):
                        runner.validate_historical_receipt(receipt)
                finally:
                    path.write_bytes(data)
        runner.validate_historical_receipt(receipt)

    def test_old_or_incomplete_receipt_cannot_be_accepted(self):
        path=self.receipt();report=json.loads(path.read_text())
        with tempfile.TemporaryDirectory(dir=ROOT/'artifacts') as directory:
            altered=Path(directory)/'verification.json'
            for key in ('schema','artifact_hashes','executed_binary','source_hashes'):
                with self.subTest(key=key):
                    bad=dict(report);bad.pop(key)
                    altered.write_text(json.dumps(bad))
                    with self.assertRaises(ValueError):
                        runner.validate_historical_receipt(altered)
            bad=copy.deepcopy(report)
            bad['artifact_hashes'].pop('artifacts/u64/u64-tests.json')
            altered.write_text(json.dumps(bad))
            with self.assertRaises(ValueError):
                runner.validate_historical_receipt(altered)


if __name__=='__main__':
    unittest.main()
