"""Render explicit radix-16 Lucas certificates from untrusted generated data.
Every factorization, prime child, digit, residue and exponent is checked in Lean.
"""
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]

def trace(a, exponent, modulus):
    value = 1 % modulus
    steps = []
    for char in format(exponent, 'x'):
        digit = int(char, 16)
        value = (pow(value, 16, modulus) * pow(a, digit, modulus)) % modulus
        steps.append((digit, value))
    return steps


def tuple_proof(items, final='by simp'):
    if not items:
        return final
    return f'(List.forall_mem_cons.mpr ⟨{items[0]}, {tuple_proof(items[1:], final)}⟩)'


def render(data):
    parts = ['import Witgen.Primality\n\nnamespace Witgen.PrimeCertificates\nopen Witgen.Primality\n']
    for node in data['nodes']:
        p = int(node['prime'])
        if node.get('small'):
            parts.append(f'theorem prime_{p} : Nat.Prime {p} := by decide\n')
            continue
        a = int(node['generator'])
        primes = [int(q) for q, _ in node['factors']]
        factors = [int(q) for q,e in node['factors'] for _ in range(e)]
        def power(suffix, exponent, neq):
            steps = trace(a, exponent, p)
            value = steps[-1][1]
            name = f'trace_{p}_{suffix}'
            literal = ',\n  '.join(f'({d}, {r})' for d,r in steps)
            parts.append(f'private def {name} : List PowStep := [\n  {literal}]\n')
            theorem = f'power_{p}_{suffix}'
            if neq:
                parts.append(f'private theorem {theorem} : ({a} : ZMod {p}) ^ {exponent} ≠ 1 :=\n'
                             f'  trace_power_ne_one {p} {a} {exponent} {value} {name}\n'
                             f'    (by decide) (by decide) (by decide) (by decide)\n')
            else:
                assert value == 1
                parts.append(f'private theorem {theorem} : ({a} : ZMod {p}) ^ {exponent} = 1 :=\n'
                             f'  trace_power {p} {a} {exponent} 1 {name}\n'
                             f'    (by decide) (by decide) (by decide)\n')
            return theorem
        main = power('full', p-1, False)
        neq_names = {q:power(str(q), (p-1)//q, True) for q in primes}
        fac_literal = '['+', '.join(map(str,factors))+']'
        hpr = tuple_proof([f'prime_{q}' for q in factors])
        hpows = tuple_proof([f'(show ({a} : ZMod {p}) ^ (({p} - 1) / {q}) ≠ 1 from {neq_names[q]})' for q in factors])
        parts.append(f'theorem prime_{p} : Nat.Prime {p} := by\n'
                     f'  let factors : List Nat := {fac_literal}\n'
                     f'  have hf : factors.prod = {p} - 1 := by decide\n'
                     f'  have hpr : ∀ q ∈ factors, Nat.Prime q := {hpr}\n'
                     f'  have hn : ∀ q ∈ factors, ({a} : ZMod {p}) ^ (({p} - 1) / q) ≠ 1 := {hpows}\n'
                     f'  apply lucas_primality {p} ({a} : ZMod {p}) {main}\n'
                     f'  intro q hq hd\n'
                     f'  exact hn q (prime_mem_factors q hq factors hpr (by simpa only [hf] using hd))\n')
    parts.append(f'theorem secpBase_prime : Nat.Prime {data["base"]} := prime_{data["base"]}\n')
    parts.append(f'theorem secpScalar_prime : Nat.Prime {data["scalar"]} := prime_{data["scalar"]}\n')
    parts.append('end Witgen.PrimeCertificates\n')
    return '\n'.join(parts)


if __name__ == '__main__':
    data = json.loads((ROOT/'artifacts/secp-prime-certificate-data.json').read_text())
    output = ROOT/'Witgen/PrimeCertificates.lean'
    output.write_text(render(data))
    print(output)
