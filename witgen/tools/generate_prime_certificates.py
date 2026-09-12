"""Generate auditable Lucas certificate data; Lean checks each arithmetic fact."""
from sage.all import ZZ
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'artifacts/secp-prime-certificate-data.json'
P = ZZ(2)**256 - ZZ(2)**32 - 977
N = ZZ('FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141', 16)
BN254 = ZZ('21888242871839275222246405745257275088548364400416034343698204186575808495617')
seen = {}

def certificate(p):
    key = str(p)
    if key in seen:
        return
    if p <= 100:
        assert p.is_prime(proof=True)
        seen[key] = {'prime':key,'small':True}
        return
    assert p.is_prime(proof=True)
    factors = list((p-1).factor(proof=True))
    print('factor',p,'=>',factors,flush=True)
    for q, _ in factors:
        certificate(q)
    generator = next(ZZ(a) for a in range(2, 1000)
                     if pow(ZZ(a),p-1,p)==1 and all(pow(ZZ(a),(p-1)//q,p)!=1 for q,_ in factors))
    seen[key] = {'prime':key, 'generator':str(generator),
                 'factors':[[str(q),int(e)] for q,e in factors]}

certificate(P)
certificate(N)
certificate(BN254)
OUT.parent.mkdir(exist_ok=True)
OUT.write_text(json.dumps({'base':str(P),'scalar':str(N),'bn254':str(BN254),'nodes':list(seen.values())},indent=2)+'\n')
print('nodes',len(seen),'output',OUT,flush=True)
