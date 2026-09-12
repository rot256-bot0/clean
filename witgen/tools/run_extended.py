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
'Witgen.Branching.conditional_false','Witgen.Branching.match_none','Witgen.Branching.match_some'}

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

def independent_cases():
    rows=[]
    def add(name,inputs,value):rows.append({'program':name,'inputs':inputs,'expected':str(value)})
    for f,p in enumerate(FIELD_MODULI):
        p=int(p);stem=f'field_{f}'
        vals=list(dict.fromkeys(x%p for x in [0,1,2,p-1,p-2,2**200+17]))
        for op in ['neg','inv']:
            for x in vals:
                value=(-x)%p if op=='neg' else (0 if x==0 else pow(x,-1,p))
                for mode in ['native','nat']:add(f'{stem}_{op}_{mode}',[str(x)],value)
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
        value=json.loads(line);f=int(row['program'].split('_')[1]);p=int(FIELD_MODULI[f])
        if not isinstance(value,str) or not re.fullmatch(r'0|[1-9][0-9]*',value) or not int(value)<p:
            raise AssertionError({'noncanonical_native':value,'case':row})
        if value!=row['expected']:raise AssertionError({'expected':row,'native':value})
        outcomes.append({**row,'actual':value})
    save(ART/'cases.json',outcomes)
    flags={row['inputs'][0] for row in rows if row['program'].endswith('_conditional')}
    option_cases={row['inputs'][0] is None for row in rows if row['program'].endswith('_match')}
    modes={row['program'].rsplit('_',1)[1] for row in rows if '_inv_' in row['program']}
    if flags!={False,True} or option_cases!={False,True} or modes!={'native','nat'}:raise AssertionError('missing semantic coverage')
    if sources()!=before:raise AssertionError('consumed sources changed during execution')
    generated=[*gen.glob('*.rs'),binpath,* (ART/'bundle').glob('*.json'),ART/'requests.jsonl',ART/'cases.json',ART/'native.log']
    report={'status':'PASS','cases':len(rows),'independent_cases':len(expected),'programs':len(names),
            'native_and_nat_inverse':True,'both_if_branches':True,'both_option_branches':True,
            'u64_rejection_proved':True,'audit':audited,'sources':before,
            'artifacts':artifact_manifest(generated,consumed),
            'executable':str(executable),'executable_sha256':exehash,'cargo_artifact':artifacts[0],
            'build_environment':{key:os.environ.get(key) for key in ['CARGO_TARGET_DIR','RUSTFLAGS','RUSTC','CARGO_HOME']}}
    if digest(executable)!=exehash:raise AssertionError('executable changed during execution')
    save(receipt,report);print(json.dumps({key:report[key] for key in ['status','cases','programs']}))
    return report

if __name__=='__main__':main()
