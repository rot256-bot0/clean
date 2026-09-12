"""Receipt lifecycle/provenance controls; never simulate arithmetic execution."""
from pathlib import Path
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import run_extended as runner


class PreimportCleanupTests(unittest.TestCase):
    def check_preflight(self, relative, receipt_relative, export=None, library=False):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            script = root / relative
            script.parent.mkdir(parents=True)
            shutil.copyfile(ROOT / relative, script)
            default = root / receipt_relative
            target = root / 'chosen' / 'verification.json' if export else default
            sentinels = {default, target, root / 'artifacts/methods/verification.json',
                         root / 'unrelated/verification.json'}
            sentinel = b'{"status":"PASS","test_only_prior_receipt_sentinel":true}\n'
            for path in sentinels:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(sentinel)
            args = []
            if export == 'relative':
                args = ['--export', 'chosen']
            elif export == 'absolute':
                args = ['--export=' + str(target.parent)]
            elif export == 'repeated':
                args = ['--export', 'not-chosen', '--export', 'chosen']
            if library:
                command = [sys.executable, '-I', '-c',
                           'import sys,runpy;sys.path.insert(0,sys.argv[1]);'
                           'runpy.run_path(sys.argv[2],run_name="receipt_library")',
                           str(ROOT / 'tools'), str(script), *args]
            else:
                command = [sys.executable, '-I', str(script), *args]
            result = subprocess.run(command, cwd=root, text=True, capture_output=True, timeout=15)
            if library:
                self.assertEqual(result.returncode, 0, result.stderr)
            else:
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('ModuleNotFoundError', result.stderr)
                self.assertFalse(target.exists(), 'project import failure retained stale PASS')
            for path in sentinels - (set() if library else {target}):
                self.assertEqual(path.read_bytes(), sentinel, str(path))

    def test_extended_missing_project_import_cleans_only_its_receipt(self):
        self.check_preflight('tools/run_extended.py', 'artifacts/extended/verification.json')

    def test_extended_library_import_preserves_receipts(self):
        self.check_preflight('tools/run_extended.py', 'artifacts/extended/verification.json', library=True)

    def test_u64_missing_project_import_cleans_actual_export_target(self):
        for export in (None, 'relative', 'absolute', 'repeated'):
            with self.subTest(export=export):
                self.check_preflight('Witgen/U64/check.py', 'Witgen/U64/evidence/verification.json', export)

    def test_u64_library_import_preserves_receipts(self):
        self.check_preflight('Witgen/U64/check.py', 'Witgen/U64/evidence/verification.json', 'relative', library=True)


class ArtifactBindingTests(unittest.TestCase):
    def test_count_preserving_export_mutations_block_publication(self):
        self.assertTrue(callable(getattr(runner, 'load_artifact', None)), 'consumed JSON binding missing')
        self.assertTrue(callable(getattr(runner, 'artifact_manifest', None)), 'publication recheck missing')
        from unittest.mock import patch
        # Metadata-only documents: these controls never fabricate arithmetic results.
        documents = {'manifest.json': {'programs': [{'name': 'metadata-only'}]},
                     'reference.json': {'cases': [{'test_only_metadata': True}]},
                     'module.json': {'test_only_metadata': ['unchanged']}}
        with tempfile.TemporaryDirectory() as directory, patch.object(runner, 'ROOT', Path(directory)):
            root = Path(directory)
            for name, document in documents.items():
                with self.subTest(artifact=name):
                    path = root / name
                    data = json.dumps(document).encode()
                    path.write_bytes(data)
                    consumed = {}
                    self.assertEqual(runner.load_artifact(path, consumed), document)
                    self.assertEqual(consumed[path], hashlib.sha256(data).hexdigest())
                    self.assertEqual(runner.artifact_manifest([path], consumed),
                                     {name: hashlib.sha256(data).hexdigest()})
                    # JSON and all program/case counts remain identical; bytes drift.
                    path.write_bytes(data + b'\n')
                    self.assertEqual(json.loads(path.read_bytes()), document)
                    receipt = root / 'verification.json'
                    with self.assertRaisesRegex(ValueError, 'consumed artifact changed'):
                        manifest = runner.artifact_manifest([path], consumed)
                        runner.save(receipt, {'test_only_metadata': True, 'artifacts': manifest})
                    self.assertFalse(receipt.exists())
                    with self.assertRaisesRegex(ValueError, 'consumed artifact changed'):
                        runner.load_artifact(path, consumed)

    def test_receipt_publication_is_atomic_and_cleans_failed_temporary(self):
        from unittest.mock import patch
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            receipt = root / 'verification.json'
            with patch.object(runner.os, 'replace', side_effect=OSError('test-only publication failure')):
                with self.assertRaisesRegex(OSError, 'test-only publication failure'):
                    runner.save(receipt, {'test_only_metadata': True})
            self.assertFalse(receipt.exists())
            self.assertEqual(list(root.iterdir()), [])
            runner.save(receipt, {'test_only_metadata': True})
            self.assertEqual(json.loads(receipt.read_bytes()), {'test_only_metadata': True})


if __name__ == '__main__':
    unittest.main()
