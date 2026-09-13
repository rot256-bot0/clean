from pathlib import Path
import subprocess
import unittest

from tools.axiom_audit import check_axioms
from tools.rsa4096.audit import RSA_AUDIT

ROOT = Path(__file__).resolve().parents[1]


class Rsa4096AuditTests(unittest.TestCase):
    def test_real_model_inventory_is_exact_and_choice_free(self):
        build = subprocess.run(['lake', 'build', 'Witgen.Examples.RSA4096.ProgramTests'],
                               cwd=ROOT, capture_output=True, text=True, timeout=100)
        self.assertEqual(build.returncode, 0, build.stdout + build.stderr)
        proc = subprocess.run(['lake', 'env', 'lean', '-DwarningAsError=true',
                               'Witgen/RsaAudit.lean'], cwd=ROOT, capture_output=True,
                              text=True, timeout=60)
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        self.assertEqual(set(check_axioms(proc.stdout, RSA_AUDIT)), {'propext', 'Quot.sound'})
        with self.assertRaises(ValueError):
            check_axioms('', RSA_AUDIT)
        with self.assertRaises(ValueError):
            check_axioms('\n'.join(proc.stdout.splitlines()[1:]), RSA_AUDIT)
        with self.assertRaises(ValueError):
            check_axioms(proc.stdout.replace('propext', 'Classical.choice'), RSA_AUDIT)


if __name__ == '__main__':
    unittest.main()
