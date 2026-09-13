#!/usr/bin/env python3
"""Actual Lean programs, native/GMP execution, and exact independent branch cases."""
from pathlib import Path
from collections import Counter
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parents[1]
ART=ROOT/'artifacts/extended'
# CLI preflight includes project imports; library imports must not delete receipts.
if __name__=='__main__':
    (ART/'verification.json').unlink(missing_ok=True)

from emit_methods import emit_module, FIELD_MODULI

AUDIT={
'Witgen.PrimeCertificates.bn254Scalar_prime','Witgen.Typed.modulus_prime',
'Witgen.Typed.Residue.inv_zero','Witgen.Typed.Residue.add_neg','Witgen.Typed.Residue.mul_inv_of_prime',
'Witgen.Typed.Residue.mul_inv','Witgen.Typed.NatMethods.handler_respects',
'Witgen.Program.eval_mapHandler?_related','Witgen.PartialCertifiedLowering.ofHandler',
'Witgen.U64.compile_accepted','Witgen.U64.lower_respects','Witgen.U64.certified','Witgen.U64.caller_correct',
'Witgen.BranchOp.eval_true','Witgen.BranchOp.eval_false','Witgen.Branching.conditional_true',
'Witgen.Branching.conditional_false','Witgen.Branching.match_none','Witgen.Branching.match_some',
'Witgen.Typed.FieldSqrt.sqrt_sound',
'Witgen.Typed.FieldSqrt.sqrt_none_iff',
'Witgen.Typed.FieldSqrt.canonical_unique',
'Witgen.Typed.FieldSqrt.sqrt_eq_some_iff',
'Witgen.Typed.FieldSqrt.sqrt_square',
'Witgen.Typed.FieldSqrt.sqrt_zero',
'Witgen.Typed.FieldSqrt.sqrt_of_candidate',
'Witgen.Typed.FieldSqrt.sqrt_none_of_euler',
'Witgen.Typed.Residue.sqrt_eq_some_iff',
'Witgen.Typed.Residue.sqrt_sound',
'Witgen.Typed.Residue.sqrt_none_iff',
'Witgen.Typed.Residue.sqrt_canonical_unique',
'Witgen.Typed.Residue.sqrt_zero',
'Witgen.Typed.Residue.sqrt_square',
'Witgen.Typed.Residue.sqrt_nat_rel',
'Witgen.Typed.sqrtNat_mod',
'Witgen.Typed.Residue.sub_eq_add_neg',
'Witgen.Typed.Residue.sub_val',
'Witgen.Typed.Residue.sub_self',
'Witgen.Typed.FieldSubTests.lowering_correct',
'Witgen.Typed.squareFallback_respects'}

def canonical(value): return json.dumps(value,sort_keys=True,separators=(',',':'))
def digest(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def save(path,value):
    temporary=None
    try:
        with tempfile.NamedTemporaryFile(mode='w',dir=path.parent,prefix=path.name+'.',delete=False) as stream:
            temporary=Path(stream.name)
            stream.write(json.dumps(value,indent=2,sort_keys=True)+'\n')
        os.replace(temporary,path)
    finally:
        if temporary is not None:temporary.unlink(missing_ok=True)

def load_artifact(path,consumed):
    data=path.read_bytes();hashed=hashlib.sha256(data).hexdigest()
    if path in consumed and consumed[path]!=hashed:
        raise ValueError('consumed artifact changed during verification: '+str(path))
    consumed[path]=hashed
    return json.loads(data)

def artifact_manifest(paths,consumed):
    hashes={str(path.relative_to(ROOT)):digest(path) for path in paths}
    for path,hashed in consumed.items():
        if hashes.get(str(path.relative_to(ROOT)))!=hashed:
            raise ValueError('consumed artifact changed during verification: '+str(path))
    return hashes

def run(args,label,timeout=180,input=None):
    result=subprocess.run(args,cwd=ROOT,text=True,input=input,capture_output=True,timeout=timeout)
    (ART/(label+'.log')).write_text(result.stdout+result.stderr)
    if result.returncode:raise RuntimeError(f'{label} failed; see {ART/(label+".log")}\n{result.stderr[-2500:]}')
    return result.stdout

def sources():
    pending=['MainExtended.lean','Witgen/ExtendedAudit.lean'];seen=set()
    while pending:
        name=pending.pop()
        if name in seen:continue
        seen.add(name);text=(ROOT/name).read_text()
        for line in text.splitlines():
            if line.startswith('import '):
                for module in line[7:].split():
                    if module.startswith('Witgen.'):
                        pending.append(module.replace('.','/')+'.lean')
    seen.update(['tools/run_extended.py','tools/emit_methods.py','backend/Cargo.toml','backend/Cargo.lock',
                 'lakefile.toml','lake-manifest.json','lean-toolchain'])
    for path in (ROOT/'backend/src').glob('*.rs'):seen.add(str(path.relative_to(ROOT)))
    return {name:digest(ROOT/name) for name in sorted(seen)}

def canonical_sqrt(x, p):
    """Independent Cipolla oracle for the configured odd prime fields."""
    x %= p
    if x == 0:
        return 0
    if pow(x, (p - 1) // 2, p) != 1:
        return None
    a = 0
    while pow((a * a - x) % p, (p - 1) // 2, p) != p - 1:
        a += 1
    w = (a * a - x) % p
    def multiply(u, v):
        return ((u[0] * v[0] + w * u[1] * v[1]) % p,
                (u[0] * v[1] + u[1] * v[0]) % p)
    acc, base, exponent = (1, 0), (a, 1), (p + 1) // 2
    while exponent:
        if exponent & 1:
            acc = multiply(acc, base)
        base = multiply(base, base)
        exponent >>= 1
    r, imaginary = acc
    if imaginary != 0 or r * r % p != x:
        raise AssertionError('Cipolla oracle did not produce a root')
    return min(r, (-r) % p)


def independent_cases():
    rows=[]
    def add(name,inputs,value):
        rows.append({'program':name,'inputs':inputs,'expected':None if value is None else str(value)})
    for f,p in enumerate(FIELD_MODULI):
        p=int(p);stem=f'field_{f}'
        vals=list(dict.fromkeys(x%p for x in [0,1,2,p-1,p-2,2**200+17]))
        for op in ['neg','inv']:
            for x in vals:
                value=(-x)%p if op=='neg' else (0 if x==0 else pow(x,-1,p))
                for mode in ['native','nat']:add(f'{stem}_{op}_{mode}',[str(x)],value)
        for a in vals:
            for b in vals:
                for mode in ['native','nat']:
                    add(f'{stem}_sub_{mode}',[str(a),str(b)],(a-b)%p)
        sqrt_values=list(dict.fromkeys(x%p for x in
            [*range(16),p-1,p-2,2**128+17,2**200+17,(p-1)//2,(2**200+17)**2]))
        for x in sqrt_values:
            root=canonical_sqrt(x,p)
            square_root=canonical_sqrt(x*x%p,p)
            if square_root!=min(x,(-x)%p):raise AssertionError('oracle canonical-square law')
            for mode in ['native','nat']:
                add(f'{stem}_sqrt_{mode}',[str(x)],root)
                add(f'{stem}_sqrt_square_{mode}',[str(x)],square_root)
            add(stem+'_sqrt_match',[str(x)],0 if root is None else x)
        pairs=[(0,0),(0,1),(1,0),(1,1),(p-1,p-1),(p-1,1),(2**128+17,2**200+3)]
        for flag in [False,True]:
            for a,b in pairs:
                a%=p;b%=p
                add(stem+'_conditional',[flag,str(a),str(b)],(a*b if flag else a+b)%p)
        for x in [None,0,1,p-1,2**200+17]:
            for y in [0,1,p-1,2**128+9]:
                y%=p
                value=(-y)%p if x is None else (0 if x%p==0 else pow(x%p,-1,p))
                add(stem+'_match',[None if x is None else str(x%p),str(y)],value)
    return rows

def audit(log):
    pairs=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log)
    pure=re.findall(r"'([^']+)' does not depend on any axioms",log)
    names=[name for name,_ in pairs]+pure
    if Counter(names)!=Counter(AUDIT):raise AssertionError({'audit_expected':sorted(AUDIT),'actual':names})
    out={name:[x.strip() for x in axes.split(',') if x.strip()] for name,axes in pairs}
    out.update({name:[] for name in pure})
    for axes in out.values():
        if not set(axes)<={'propext','Classical.choice','Quot.sound'}:raise AssertionError(axes)
    return out

def validate_output(row, value):
    """Check raw ABI values before equality; never repair or normalize them."""
    f = int(row['program'].split('_')[1])
    p = int(FIELD_MODULI[f])
    optional = row['program'].endswith(('_sqrt_native', '_sqrt_nat',
                                         '_sqrt_square_native', '_sqrt_square_nat'))
    if value is None:
        if not optional:
            raise AssertionError({'unexpected_none': row})
    elif not isinstance(value, str) or not re.fullmatch(r'0|[1-9][0-9]*', value) or not int(value) < p:
        raise AssertionError({'noncanonical_native': value, 'case': row})
    if value != row['expected']:
        raise AssertionError({'expected': row, 'native': value})


def main():
    ART.mkdir(parents=True,exist_ok=True)
    receipt=ART/'verification.json';receipt.unlink(missing_ok=True)
    before=sources();consumed={}
    run(['lake','build','Witgen.ExtendedAudit'],'build')
    audited=audit(run(['lake','env','lean','Witgen/ExtendedAudit.lean'],'audit'))
    run(['lake','env','lean','--run','MainExtended.lean','export',str(ART/'bundle')],'export')
    manifest=load_artifact(ART/'bundle/manifest.json',consumed)['programs']
    rows=load_artifact(ART/'bundle/reference.json',consumed)['cases'];expected=independent_cases()
    if Counter(map(canonical,rows))!=Counter(map(canonical,expected)):raise AssertionError('exact independent case multiset mismatch')
    names=[entry['name'] for entry in manifest]
    if len(names)!=len(set(names)) or set(names)!={row['program'] for row in expected}:raise AssertionError('module manifest mismatch')
    gen=ROOT/'backend/src/generated_extended';gen.mkdir(parents=True,exist_ok=True)
    code=[];arms=[]
    for i,entry in enumerate(manifest):
        module=load_artifact(ART/'bundle'/f'{entry["name"]}.json',consumed)
        text=emit_module(module,entry['mode']);(gen/f'module_{i}.rs').write_text(text)
        code.append(f'#[path = "../generated_extended/module_{i}.rs"] mod module_{i};')
        arms.append(f'{json.dumps(entry["name"])} => module_{i}::run_json(inputs),')
    code.append('use std::io::{self,BufRead};\nuse serde_json::{json,Value};\nfn main(){for line in io::stdin().lock().lines(){let response:Value=(||->witgen_native::Result<Value>{let text=line?;let req:Value=serde_json::from_str(&text)?;let name=req.get("program").and_then(Value::as_str).ok_or(witgen_native::Error::MissingField("program"))?;let inputs=req.get("inputs").ok_or(witgen_native::Error::MissingField("inputs"))?.as_array().ok_or(witgen_native::Error::InvalidInputType{expected:"inputs array"})?;match name{'+''.join(arms)+'_=>Err(witgen_native::Error::UnknownProgram(name.to_owned()))}})().unwrap_or_else(|e|json!({"error":e.to_string()}));println!("{}",response);}}')
    binpath=ROOT/'backend/src/bin/witgen-extended.rs';binpath.parent.mkdir(exist_ok=True);binpath.write_text('\n'.join(code)+'\n')
    cargo=run(['cargo','build','--locked','--manifest-path','backend/Cargo.toml','--bin','witgen-extended','--message-format=json-render-diagnostics'],'cargo')
    artifacts=[]
    for line in cargo.splitlines():
        event=json.loads(line)
        if event.get('reason')=='compiler-artifact' and event.get('target',{}).get('name')=='witgen-extended' and event.get('executable'):
            artifacts.append(event)
    if len(artifacts)!=1:raise AssertionError('missing or ambiguous Cargo executable')
    executable=Path(artifacts[0]['executable']).resolve();exehash=digest(executable)
    requests=''.join(canonical({'program':row['program'],'inputs':row['inputs']})+'\n' for row in rows)
    (ART/'requests.jsonl').write_text(requests)
    results=run([str(executable)],'native',input=requests).splitlines()
    if len(results)!=len(rows):raise AssertionError('native result count mismatch')
    outcomes=[]
    for row,line in zip(rows,results):
        value=json.loads(line)
        validate_output(row,value)
        outcomes.append({**row,'actual':value})
    save(ART/'cases.json',outcomes)
    flags={row['inputs'][0] for row in rows if row['program'].endswith('_conditional')}
    option_cases={row['inputs'][0] is None for row in rows if row['program'].endswith('_match')}
    modes={row['program'].rsplit('_',1)[1] for row in rows if '_inv_' in row['program']}
    if flags!={False,True} or option_cases!={False,True} or modes!={'native','nat'}:raise AssertionError('missing semantic coverage')
    for f,p in enumerate(FIELD_MODULI):
        p=int(p)
        for mode in ['native','nat']:
            differences=[row for row in outcomes if row['program']==f'field_{f}_sub_{mode}']
            if {int(row['inputs'][0])<int(row['inputs'][1]) for row in differences}!={False,True}:
                raise AssertionError('missing modular subtraction wrap coverage')
            if not any(row['inputs'][0]==row['inputs'][1] and row['actual']=='0' for row in differences):
                raise AssertionError('missing subtraction self-zero coverage')
            direct=[row for row in outcomes if row['program']==f'field_{f}_sqrt_{mode}']
            if {row['actual'] is None for row in direct}!={False,True}:
                raise AssertionError('missing square/nonsquare coverage')
            if not any(row['inputs']==['0'] and row['actual']=='0' for row in direct):
                raise AssertionError('missing square-root zero coverage')
            squares=[row for row in outcomes if row['program']==f'field_{f}_sqrt_square_{mode}']
            if not squares or not all(row['actual']==str(min(int(row['inputs'][0]),(-int(row['inputs'][0]))%p)) for row in squares):
                raise AssertionError('sqrt-square canonical sign mismatch')
            if {int(row['inputs'][0])>p//2 for row in squares}!={False,True}:
                raise AssertionError('missing both input signs')
        matches=[row for row in outcomes if row['program']==f'field_{f}_sqrt_match']
        if {canonical_sqrt(int(row['inputs'][0]),p) is None for row in matches}!={False,True}:
            raise AssertionError('missing sqrt Option-match branch')
    if sources()!=before:raise AssertionError('consumed sources changed during execution')
    generated=[*gen.glob('*.rs'),binpath,* (ART/'bundle').glob('*.json'),ART/'requests.jsonl',ART/'cases.json',ART/'native.log']
    report={'status':'PASS','cases':len(rows),'independent_cases':len(expected),'programs':len(names),
            'native_and_nat_inverse':True,'both_if_branches':True,'both_option_branches':True,
            'native_and_nat_sub':True,'native_and_nat_sqrt':True,'sqrt_some_and_none_all_fields':True,
            'sqrt_match_both_branches':True,'sqrt_square_canonical':True,
            'u64_rejection_proved':True,'audit':audited,'sources':before,
            'artifacts':artifact_manifest(generated,consumed),
            'executable':str(executable),'executable_sha256':exehash,'cargo_artifact':artifacts[0],
            'build_environment':{key:os.environ.get(key) for key in ['CARGO_TARGET_DIR','RUSTFLAGS','RUSTC','CARGO_HOME']}}
    if digest(executable)!=exehash:raise AssertionError('executable changed during execution')
    save(receipt,report);print(json.dumps({key:report[key] for key in ['status','cases','programs']}))
    return report

if __name__=='__main__':main()
