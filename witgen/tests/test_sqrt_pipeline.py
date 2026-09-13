"""Independent square-root oracle and raw optional-result controls."""
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import run_extended as runner


class SquareRootOracleTests(unittest.TestCase):
    def test_cipolla_oracle_matches_exhaustive_small_prime_roots(self):
        oracle = getattr(runner, 'canonical_sqrt', None)
        self.assertTrue(callable(oracle), 'independent modular square-root oracle missing')
        for p in (3, 5, 7, 11, 13, 17, 41, 97):
            for x in range(p):
                roots = [r for r in range(p) if r * r % p == x]
                self.assertEqual(oracle(x, p), min(roots) if roots else None, (p, x))


class SquareRootOutputTests(unittest.TestCase):
    def test_optional_results_are_checked_without_normalization(self):
        check = getattr(runner, 'validate_output', None)
        self.assertTrue(callable(check), 'raw optional-result checker missing')
        p = int(runner.FIELD_MODULI[0])
        square = {'program': 'field_0_sqrt_native', 'inputs': ['4'], 'expected': '2'}
        nonsquare = {'program': 'field_0_sqrt_nat', 'inputs': ['5'], 'expected': None}
        check(square, '2')
        check(nonsquare, None)
        for bad in (None, 2, '02', str(p + 2), str(p - 2), {'some': '2'}):
            with self.subTest(bad=bad), self.assertRaises(AssertionError):
                check(square, bad)
        with self.assertRaises(AssertionError):
            check(nonsquare, '0')
        ordinary = {'program': 'field_0_inv_native', 'inputs': ['0'], 'expected': '0'}
        with self.assertRaises(AssertionError):
            check(ordinary, None)


class SquareRootPipelineTests(unittest.TestCase):
    def test_real_lean_native_and_nat_square_roots(self):
        import json
        import subprocess
        run = subprocess.run([sys.executable, '-B', 'tools/run_extended.py'], cwd=ROOT,
                             capture_output=True, text=True, timeout=300)
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
        report = json.loads((ROOT / 'artifacts/extended/verification.json').read_text())
        self.assertTrue(report.get('native_and_nat_sqrt'), 'actual square-root programs missing')
        self.assertTrue(report['native_and_nat_sub'])
        self.assertTrue(report['sqrt_some_and_none_all_fields'])
        self.assertTrue(report['sqrt_match_both_branches'])
        self.assertTrue(report['sqrt_square_canonical'])
        self.assertEqual(report['cases'], len(runner.independent_cases()))
        for relative, expected in report['artifacts'].items():
            self.assertEqual(runner.digest(ROOT / relative), expected, relative)
        self.assertEqual(runner.digest(report['executable']), report['executable_sha256'])


if __name__ == '__main__':
    unittest.main()
