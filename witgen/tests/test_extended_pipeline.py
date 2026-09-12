from pathlib import Path
import subprocess
import json
import unittest
ROOT=Path(__file__).resolve().parents[1]

class ExtendedPipeline(unittest.TestCase):
    def test_field_inverse_and_named_branches_execute(self):
        run=subprocess.run(['python3','tools/run_extended.py'],cwd=ROOT,text=True,capture_output=True,timeout=300)
        self.assertEqual(run.returncode,0,run.stdout+run.stderr)
        report=json.loads((ROOT/'artifacts/extended/verification.json').read_text())
        self.assertEqual(report['status'],'PASS')
        self.assertEqual(report['cases'],report['independent_cases'])
        self.assertTrue(report['native_and_nat_inverse'])
        self.assertTrue(report['both_if_branches'])
        self.assertTrue(report['both_option_branches'])
        self.assertTrue(report['u64_rejection_proved'])

if __name__=='__main__':unittest.main()
