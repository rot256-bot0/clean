#!/usr/bin/env python3
"""Fresh, bounded, dependency-free Lean verification for the U64 import closure."""
import argparse
import hashlib
import json
import os
import re
from pathlib import Path
import subprocess
import tempfile
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools'))
from axiom_audit import check_axioms
from run_methods import U64_AUDIT


def verify_axioms(log, expected):
    if tuple(expected) != U64_AUDIT:
        raise ValueError('U64 audit inventory differs from its independent fixed list')
    return check_axioms(log, expected)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--export', default='Witgen/U64/evidence')
    opts = parser.parse_args()
    order, seen = [], set()

    def visit(module):
        if module in seen:
            return
        seen.add(module)
        source = ROOT / (module.replace('.', '/') + '.lean')
        for line in source.read_text().splitlines():
            if line.startswith('import '):
                for dep in line.removeprefix('import ').split():
                    if dep.startswith('Witgen.'):
                        visit(dep)
                    elif dep.split('.')[0] not in {'Std', 'Lean', 'Init'}:
                        raise RuntimeError(f'unexpected external import: {dep}')
        order.append((module, source))

    visit('Witgen.U64.Audit')
    visit('MainU64')
    hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for _, p in order}
    output = (ROOT / opts.export).resolve()
    output.mkdir(parents=True, exist_ok=True)
    (output / 'verification.json').unlink(missing_ok=True)
    with tempfile.TemporaryDirectory(prefix='witgen-u64-lean-') as build:
        env = dict(os.environ, LEAN_PATH=build)
        logs = []
        for module, source in order:
            target = Path(build) / (module.replace('.', '/') + '.olean')
            target.parent.mkdir(parents=True, exist_ok=True)
            result = subprocess.run(['lean', '-DwarningAsError=true', '-o', str(target), str(source)],
                                    cwd=ROOT, env=env, capture_output=True, text=True, timeout=90)
            logs.append(result.stdout + result.stderr)
            print(f'{module}: {result.returncode}', flush=True)
            if result.returncode:
                raise RuntimeError(logs[-1])
        result = subprocess.run(['lean', '--run', 'MainU64.lean', 'export', str(output)],
                                cwd=ROOT, env=env, capture_output=True, text=True, timeout=180)
        print(result.stdout, end='', flush=True)
        if result.returncode:
            raise RuntimeError(result.stdout + result.stderr)
        for _, p in order:
            if hashlib.sha256(p.read_bytes()).hexdigest() != hashes[str(p.relative_to(ROOT))]:
                raise RuntimeError(f'concurrent source change during verification: {p}')
        audit = ''.join(logs)
        (output / 'axioms.txt').write_text(audit)
        expected = [line.split('#print axioms ', 1)[1].strip()
                    for line in (ROOT / 'Witgen/U64/Audit.lean').read_text().splitlines()
                    if line.startswith('#print axioms ')]
        axioms = verify_axioms(audit, expected)
        bundle = json.loads((output / 'u64-shared.json').read_text())
        names = [m['name'] for m in bundle['methods']]
        assert len(names) == len(set(names)) == 12
        assert len(bundle['programs']) == 9
        assert all(p['body']['op'] == 'method.call' and p['body']['next']['tag'] == 'ret'
                   for p in bundle['programs'])
        assert names[:3] == ['u64.field.add', 'u64.field.mul', 'u64.field.square']
        loops, calls = [], []

        def walk(node):
            if isinstance(node, dict):
                if node.get('op') == 'u64.repeat':
                    loops.append(node['static']['count'])
                if node.get('op') == 'method.call':
                    calls.append(node['static']['name'])
                for v in node.values():
                    walk(v)
            elif isinstance(node, list):
                for v in node:
                    walk(v)
        walk(bundle)
        assert loops == [256]
        report = json.loads((output / 'u64-tests.json').read_text())
        assert report['status'] == 'pass'
        assert report['field_caller_checks'] == len(report['fixtures'])
        unique_cases, wide_products = set(), 0
        # Independent Python big-integer model, outside the executable word target.
        for row in report['fixtures']:
            p = int(row['modulus'])
            inputs = list(map(int, row['inputs']))
            op = row['program'].split('.')[-1]
            unique_cases.add((row['program'], tuple(inputs)))
            assert all(0 <= x < p for x in inputs)
            if op == 'mul' and (inputs[0] * inputs[1]).bit_length() == 512:
                wide_products += 1
            expected_value = ((sum(inputs) if op == 'add' else
                               inputs[0] * (inputs[1] if op == 'mul' else inputs[0])) % p)
            decoded = sum(int(x) << (64*i) for i, x in enumerate(row['limbs']))
            assert 0 <= decoded < p
            assert decoded == int(row['actual']) == int(row['expected']) == expected_value
        receipt = {'source_sha256': hashes, 'direct_lean_modules': len(order),
                   'axiom_endpoints': len(expected), 'axioms': sorted(axioms), 'shared_methods': len(names),
                   'callers': len(bundle['programs']), 'loop_bounds': loops,
                   'call_sites': len(calls), 'python_reference_checks': len(report['fixtures']),
                   'unique_field_caller_cases': len(unique_cases), 'full_512_bit_products': wide_products}
        (output / 'verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
        print(json.dumps({k: v for k, v in receipt.items() if k != 'source_sha256'}, sort_keys=True))


if __name__ == '__main__':
    main()
