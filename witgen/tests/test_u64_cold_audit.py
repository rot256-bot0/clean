import importlib.util
from pathlib import Path
import sys
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from run_methods import U64_AUDIT, check_axioms

class ColdAuditTests(unittest.TestCase):
    def test_real_u64_inventory_preserves_choice_free_boundary(self):
        import subprocess

        built=subprocess.run(['lake','build','Witgen.U64.Audit'],cwd=ROOT,
            text=True,capture_output=True,timeout=180)
        self.assertEqual(built.returncode,0,built.stdout+'\n'+built.stderr)
        audit=subprocess.run(['lake','env','lean','-DwarningAsError=true',
            'Witgen/U64/Audit.lean'],cwd=ROOT,text=True,capture_output=True,timeout=60)
        self.assertEqual(audit.returncode,0,audit.stdout+'\n'+audit.stderr)
        # Use the strict default whitelist, not the broader field/curve inventory.
        self.assertEqual(check_axioms(audit.stdout+'\n'+audit.stderr,U64_AUDIT),
                         ['Quot.sound','propext'])

    def test_cold_checker_requires_exact_nonempty_inventory(self):
        spec=importlib.util.spec_from_file_location('cold_u64',ROOT/'Witgen/U64/check.py')
        assert spec is not None and spec.loader is not None
        module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
        self.assertTrue(hasattr(module,'verify_axioms'))
        good='\n'.join(f"'{name}' depends on axioms: [propext, Quot.sound]" for name in U64_AUDIT)
        self.assertEqual(module.verify_axioms(good,list(U64_AUDIT)),['Quot.sound','propext'])
        for log,inventory in [('',[]),('',list(U64_AUDIT)),(good,list(U64_AUDIT[:-1]))]:
            with self.assertRaises(ValueError):module.verify_axioms(log,inventory)

if __name__=='__main__':unittest.main()
