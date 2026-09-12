#!/usr/bin/env python3
"""Verify typed field/method/U64/secp paths and emit one shared U64 library."""
from collections import Counter
from pathlib import Path
import copy
import hashlib
import json
import os
import re
import subprocess

ROOT=Path(__file__).resolve().parents[1]
ART=ROOT/'artifacts/methods'
# CLI preflight includes project imports, which can fail before run_all starts.
if __name__=='__main__':
    (ART/'verification.json').unlink(missing_ok=True)

from axiom_audit import check_axioms
from emit_methods import emit_module, FIELD_MODULI
P,N=map(int,FIELD_MODULI[1:])
G=(55066263022277343669578718895168534326250603453777594175500187360389116729240,
   32670510020758816978083085130507043184471273380659243275938904335757337482424)
TYPED_AUDIT=(
 'Witgen.Methods.call_substitution','Witgen.Methods.Library.ref_unique',
 'Witgen.Methods.Library.earlier_only','Witgen.Methods.Library.caller_refinement',
 'Witgen.Methods.libraryJson_size','Witgen.Typed.squareFallback_respects',
 'Witgen.Typed.NatMethods.handler_respects','Witgen.Typed.fieldProgramNat_correct',
 'Witgen.Typed.Secp.basePrime','Witgen.Typed.Secp.scalarPrime',
 'Witgen.Typed.Secp.generator_equation','Witgen.Typed.Secp.discriminant_ne_zero',
 'Witgen.Typed.Secp.affine_roundtrip','Witgen.Typed.Secp.fromAffine_isSome_iff',
 'Witgen.Typed.Secp.concrete_mixed_correct','Witgen.Typed.Secp.concrete_generator_roundtrip',
 'Witgen.Typed.ValueOp.case_none','Witgen.Typed.ValueOp.case_some',
 'Witgen.Typed.Curve.const_spec','Witgen.Typed.Curve.literal_point_spec',
 'Witgen.Typed.Curve.mul_spec','Witgen.Typed.Curve.eq_spec','Witgen.Typed.Curve.msm_spec',
 'Witgen.Typed.Curve.msm_nil','Witgen.Typed.Curve.msm_singleton',
 'Witgen.Typed.Curve.affine_roundtrip','Witgen.Typed.Curve.fromAffine_toAffine',
 'Witgen.Typed.Curve.fromAffine_isSome_iff','Witgen.Typed.Secp.math',
 'Witgen.Typed.Secp.mixed_identity_none','Witgen.Typed.Secp.curveEq_correct',
 'Witgen.Typed.Secp.curveMSM_correct','Witgen.Typed.Secp.constructedMSM_correct',
 'Witgen.Typed.Secp.constantGenerator_correct','Witgen.Typed.Secp.constantIdentity_correct',
 'Witgen.Typed.u64FieldProgram_correct',
 'Witgen.Typed.Secp.generator_nonsingular','Witgen.Typed.Secp.mul_spec',
 'Witgen.Typed.Secp.fromAffine_zero_zero','Witgen.Typed.Secp.generator_roundtrip',
 'Witgen.Typed.Secp.mixed_correct','Witgen.Typed.Secp.mixed_one_one',
 'Witgen.Typed.Secp.roundtripProgram_eval','Witgen.Typed.Secp.generatorRoundtrip_correct',
 'Witgen.Typed.Secp.invalidPair_rejects_zero','Witgen.Typed.Public.mixed_eq',
 'Witgen.Typed.Public.mixed_correct','Witgen.Typed.CurveProgramTests.curveEq_correct',
 'Witgen.Typed.CurveProgramTests.curveMSM_correct','Witgen.Typed.CurveProgramTests.constructedMSM_correct',
 'Witgen.Typed.CurveProgramTests.roundtrip_correct','Witgen.Typed.CurveIntegrationTests.field_neg',
 'Witgen.Typed.CurveIntegrationTests.field_inv','Witgen.Typed.CurveIntegrationTests.field_inv_zero',
 'Witgen.Typed.CurveIntegrationTests.mixed_correct','Witgen.Typed.CurveIntegrationTests.roundtrip_eval',
 'Witgen.Typed.CurveIntegrationTests.generator_roundtrip')
U64_AUDIT=tuple('Witgen.U64.'+name for name in (
 'addc_correct','subb_correct','adc_correct','sbb_correct','Word4.decode_lt','Word4.decode_encode',
 'Word4.addCarry_correct','Word4.subBorrow_correct','Word4.Add_correct','wordBit_correct',
 'Word4.bitAt_correct','Word4.mulLoop_correct','Word4.Mul_correct','Word4.Square_correct',
 'addBody_correct','mulBody_correct','squareBody_correct','repeatDown_exec','RepeatExec.steps',
 'fieldAdd_spec','fieldMul_spec','fieldSquare_spec','lower_respects','certified','caller_correct'))
STRUCT_AUDIT=tuple('Witgen.'+name for name in (
 'Var.get_set','Var.set_get','Var.set_related','Var.get_set_other','Var.set_set',
 'StructRepr.get_set','StructRepr.set_get','StructRepr.get_set_other','StructRepr.set_set','structModel_respects'))


def point_add(a,b):
    if a is None:return b
    if b is None:return a
    x,y=a;u,v=b
    if x==u and (y+v)%P==0:return None
    slope=((3*x*x)*pow(2*y,P-2,P) if a==b else (v-y)*pow((u-x)%P,P-2,P))%P
    rx=(slope*slope-x-u)%P
    return rx,(slope*(x-rx)-y)%P


def point_scale(k,a):
    r=None
    while k:
        if k&1:r=point_add(r,a)
        a=point_add(a,a);k>>=1
    return r


def point_decode(encoded):
    if not isinstance(encoded,str) or not re.fullmatch(r'[0-9a-fA-F]+',encoded):
        raise ValueError('invalid point JSON')
    data=bytes.fromhex(encoded)
    if data==b'\0':return None
    if len(data)==65 and data[0]==4:
        x=int.from_bytes(data[1:33],'big');y=int.from_bytes(data[33:],'big')
    elif len(data)==33 and data[0] in (2,3):
        x=int.from_bytes(data[1:],'big');rhs=(x*x*x+7)%P;y=pow(rhs,(P+1)//4,P)
        if y%2!=data[0]%2:y=(-y)%P
    else:raise ValueError('unsupported SEC1 encoding')
    if not (0<=x<P and 0<=y<P and (y*y-x*x*x-7)%P==0):raise ValueError('off-curve native output')
    return x,y


def point_reference(p):
    return {'infinity':True} if p is None else {'x':str(p[0]),'y':str(p[1])}


def normalize(ty,value):
    if ty == 'bool':
        if type(value) is not bool:raise ValueError('non-Boolean output')
        return value
    if isinstance(ty,dict):
        if 'list' in ty:
            if not isinstance(value,list):raise ValueError('bad list output')
            return [normalize(ty['list'],v) for v in value]
        if 'field' in ty:
            if not isinstance(value,str) or not re.fullmatch(r'0|[1-9][0-9]*',value):raise ValueError('non-decimal field output')
            if int(value)>=int(ty['modulus']):raise ValueError('noncanonical field output')
            return value
        if 'point' in ty:return point_reference(point_decode(value))
        if 'option' in ty:
            if value is None:return None
            payload=ty['option']
            if isinstance(payload,dict) and 'option' in payload:
                if not isinstance(value,dict) or set(value)!={'some'}:
                    raise ValueError('nested option output requires exact some tag')
                return {'some':normalize(payload,value['some'])}
            return normalize(payload,value)
        if 'pair' in ty:
            if not isinstance(value,list) or len(value)!=2:raise ValueError('bad pair output')
            return [normalize(t,v) for t,v in zip(ty['pair'],value)]
    return value


def expected_independent(case):
    name=case['program'];args=case['inputs']
    if name.startswith('field_'):
        f=int(name.split('_')[1]);p=int(FIELD_MODULI[f]);a,b=map(int,args)
        return str((a*a*b+5)%p)
    if name.startswith('field.'):
        _,f,op=name.split('.');p=int(FIELD_MODULI[int(f)]);vals=list(map(int,args));a=vals[0]
        if op=='mul': value=a*vals[1]
        elif op=='add': value=a+vals[1]
        elif op=='square': value=a*a
        else: raise ValueError('unknown field operation')
        return str(value%p)
    if name=='secp_mixed_fields':
        s,t=map(int,args);k=(s*s*t+s)%N;q=point_add(point_scale(k,G),(G[0],(-G[1])%P))
        return None if q is None else str((q[0]*q[0]*q[1]+q[0])%P)
    if name in ('secp_generator_affine_roundtrip','curve_const_generator'):return point_reference(G)
    if name=='curve_const_identity':return point_reference(None)
    if name=='curve_eq':return point_decode(args[0])==point_decode(args[1])
    if name=='curve_msm':
        total=None
        for scalar,point in args[0]:total=point_add(total,point_scale(int(scalar),point_decode(point)))
        return point_reference(total)
    if name=='curve_msm_constructed':return point_reference(point_scale(int(args[0]),point_decode(args[1])))
    if name in ('secp_to_affine','secp_affine_roundtrip'):
        p=point_decode(args[0])
        return None if p is None else list(map(str,p)) if name=='secp_to_affine' else point_reference(p)
    if name=='secp_from_affine':
        x,y=map(int,args[0]);return point_reference((x,y)) if (y*y-x*x*x-7)%P==0 else None
    raise ValueError('missing independent checker: '+name)


def required_cases():
    """Independent input specification, not inferred from the exported fixtures.

    MainMethods.inputPairs/exportAll and U64.Tests.casesFor/checkFieldPair are
    transcribed here intentionally: changing the producer must reconcile this
    gate. Dedup only pairs where Lean uses eraseDups, never projected square
    inputs or the two independently specified occurrences of -G.
    """
    cases=[]
    def add(program,mode,inputs):
        cases.append({'program':program,'mode':mode,'inputs':inputs})
    for f,modulus in enumerate(FIELD_MODULI):
        p=int(modulus)
        pairs=[(0,0),(1,1),(p-1,p-1),(p-2,p-3),(p-1,1),
               (2**64,2**128+3),(2**200+7,2**192+9),(2**255-1,p-1),
               (p//2,p//3),(p-123456789,p-987654321),(2**253,2**250),
               (2**65+99,2**129+101)]
        for a,b in dict.fromkeys((a%p,b%p) for a,b in pairs):
            for suffix,mode in [('native','native'),('nat_methods','nat'),('u64_methods','u64')]:
                add(f'field_{f}_{suffix}',mode,[str(a),str(b)])
    for args in [(0,0),(1,1),(1,0),(2,3),(N-1,1),
                 (2**200+7,2**129+9),(17,19)]:
        add('secp_mixed_fields','native',list(map(str,args)))
    doubled=point_add(G,G)
    negative=(G[0],(-G[1])%P)
    def encode(point):
        return '00' if point is None else '04'+''.join(format(x,'064x') for x in point)
    # -G and (n-1)G intentionally occur twice, including in the input multiset.
    points=[None,G,doubled,negative,negative]
    for point in points:
        encoded=encode(point)
        for name in ['secp_to_affine','secp_affine_roundtrip']:
            add(name,'native',[encoded])
    for xy in [G,doubled,(0,0),(1,1)]:
        add('secp_from_affine','native',[list(map(str,xy))])
    for a in points:
        for b in points:add('curve_eq','native',[encode(a),encode(b)])
    for terms in [[],[(0,G)],[(1,G)],[(1,None)],[(1,G),(1,negative)],
                  [(2,G),(3,doubled)],[(N-1,G)],
                  [(2**200+7,G),(2**129+9,negative),(17,None)]]:
        add('curve_msm','native',[[[str(k),encode(point)] for k,point in terms]])
    for k,point in [(0,G),(1,G),(N-1,G),(N-1,None),(2**200+7,doubled)]:
        add('curve_msm_constructed','native',[str(k),encode(point)])
    for name in ('curve_const_generator','curve_const_identity','secp_generator_affine_roundtrip'):
        add(name,'native',[])
    for f,modulus in enumerate(FIELD_MODULI):
        p=int(modulus);radix=2**64;capacity=2**256
        edges=[(0,0),(0,1),(1,0),(1,1),(p-1,p-1),(p-1,1),(p-2,p-3),
               (radix-1,1),(radix-1,radix-1),(radix+1,radix-1),
               (2**127+17,2**129+3),(2**192+7,2**193+11),(2**255-1,2**255-1),
               (2**255+1,p-1),(capacity-1,capacity-1)]
        patterns=[(2**(16*i)+2**(255-i)+i*65537,
                   2**(255-16*i)+2**(64+i)+i*4294967291) for i in range(16)]
        exhaustive=[(a,b) for a in range(p) for b in range(p)] if p<=17 else []
        for a,b in dict.fromkeys((a%p,b%p) for a,b in edges+patterns+exhaustive):
            for op,inputs in [('add',[a,b]),('mul',[a,b]),('square',[a])]:
                add(f'field.{f}.{op}','u64',list(map(str,inputs)))
    return cases


def case_key(case):
    return json.dumps([case['program'],case['mode'],case['inputs']],sort_keys=True,separators=(',',':'))


def validate_case_coverage(cases):
    expected=Counter(map(case_key,required_cases()))
    actual=Counter(map(case_key,cases))
    if actual!=expected:
        raise ValueError('case multiset mismatch: '+json.dumps({
            'missing':dict(expected-actual),'unexpected':dict(actual-expected)},sort_keys=True))
    return {'total':sum(actual.values()),'unique':len(actual),
            'intentional_duplicates':sum(n-1 for n in actual.values())}


def validate_results(cases,results,output_types):
    if len(results)!=len(cases):raise ValueError('missing native results')
    records=[]
    for index,(case,result) in enumerate(zip(cases,results)):
        expected=expected_independent(case)
        if case['expected']!=expected:raise ValueError('Lean fixture/oracle mismatch: '+case['program'])
        if not isinstance(result,dict) or set(result)!={'ok'}:
            raise ValueError('native method mismatch: '+json.dumps({'case':case,'result':result}))
        normalized=normalize(output_types[case['program']],result['ok'])
        if normalized!=expected:
            raise ValueError('native method mismatch: '+json.dumps({'case':case,'result':result}))
        records.append({'case_index':index,'case':copy.deepcopy(case),'result':copy.deepcopy(result),
                        'output_type':output_types[case['program']],
                        'independent_expected':expected,'normalized':normalized})
    return records


def semantic_assertions(records):
    """Receipt flags require these exact executed null assertions, not counts."""
    required={
        'affine_invalid_rejected':[('secp_from_affine',[[str(x),str(x)]]) for x in (0,1)],
        'infinity_explicit':[(name,['00']) for name in ('secp_to_affine','secp_affine_roundtrip')]}
    assertions={}
    for label,requests in required.items():
        checks=[]
        for program,inputs in requests:
            matches=[r for r in records if r['case']['program']==program and r['case']['inputs']==inputs]
            if len(matches)!=1:raise ValueError('missing/duplicate semantic assertion: '+label)
            record=matches[0]
            passed=(record['case']['expected'] is None and record['independent_expected'] is None
                    and record['normalized'] is None and record['result']=={'ok':None})
            if not passed:raise ValueError('failed semantic assertion: '+label)
            checks.append({'case_index':record['case_index'],'program':program,'inputs':inputs,
                           'expected':None,'native_result':record['result'],'passed':passed})
        assertions[label]=checks
    return assertions


def sources():
    paths=set((ROOT/'Witgen').rglob('*.lean'))
    paths.update(ROOT/name for name in ('MainMethods.lean','MainTyped.lean','MainU64.lean',
      'tools/emit_methods.py','tools/run_methods.py','tools/axiom_audit.py','tools/emit_rust.py',
      'backend/src/typed.rs','backend/src/lib.rs','backend/src/crypto.rs','backend/src/error.rs',
      'backend/Cargo.toml','backend/Cargo.lock','lean-toolchain','lakefile.toml','lake-manifest.json'))
    return {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)}


def cargo_executable(text):
    """Select the executable Cargo actually built, never infer its target dir."""
    artifacts=[]
    for line in text.splitlines():
        event=json.loads(line)
        if (event.get('reason')=='compiler-artifact'
                and event.get('target',{}).get('name')=='witgen-methods'
                and 'bin' in event['target'].get('kind',[])
                and event.get('executable')):
            artifacts.append(event)
    if len(artifacts)!=1:
        raise ValueError('expected exactly one Cargo witgen-methods executable artifact')
    return artifacts[0]


def build_environment():
    # Build-affecting variables only; registry credentials are not receipt data.
    names={'PATH','HOME','CARGO_HOME','RUSTUP_HOME','RUSTUP_TOOLCHAIN','RUSTC','RUSTDOC',
           'RUSTFLAGS','RUSTDOCFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER',
           'CARGO_NET_OFFLINE','CC','CXX','AR','CFLAGS','CXXFLAGS','CPPFLAGS','LDFLAGS',
           'PKG_CONFIG_PATH','PKG_CONFIG_LIBDIR','PKG_CONFIG_SYSROOT_DIR'}
    prefixes=('CARGO_BUILD_','CARGO_TARGET_','CARGO_PROFILE_','CARGO_ENCODED_',
              'CC_','CXX_','AR_','CFLAGS_','CXXFLAGS_','GMP_')
    return {k:v for k,v in sorted(os.environ.items()) if k in names or k.startswith(prefixes)}


def configuration_hashes():
    """Cargo searches the invocation cwd's ancestors, not the manifest dir.

    Include absent candidates so adding a config during verification is also
    detected. Keep file contents private; bind them by hash in the receipt.
    """
    paths=set()
    for directory in [ROOT,*ROOT.parents]:
        paths.update(directory/'.cargo'/name for name in ('config','config.toml'))
        paths.update(directory/name for name in ('rust-toolchain','rust-toolchain.toml'))
    cargo_home=Path(os.environ.get('CARGO_HOME',str(Path.home()/'.cargo'))).expanduser()
    if not cargo_home.is_absolute():cargo_home=ROOT/cargo_home
    paths.update(cargo_home/name for name in ('config','config.toml'))
    return {str(p):hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file() else None
            for p in sorted(paths)}


def jsonl(rows):
    return ''.join(json.dumps(row,sort_keys=True)+'\n' for row in rows)


def validate_historical_receipt(receipt_path,root=None):
    """Validate a trusted, retained v2 receipt against its original files.

    This is integrity/replay checking, not authentication of a caller-supplied
    PASS or a fresh native execution. Pin the receipt itself externally. Sources,
    configured files and the exact Cargo executable must still be available.
    """
    root=ROOT if root is None else Path(root)
    report=json.loads(Path(receipt_path).read_text())
    def require(ok,message):
        if not ok:raise ValueError('invalid historical receipt: '+message)
    def verify_hash(path,digest):
        path=Path(path)
        actual=hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else None
        if actual!=digest:raise ValueError('receipt hash mismatch: '+str(path))
    def load(name):
        return json.loads((root/name).read_text())
    def rows(name):
        return [json.loads(line) for line in (root/'artifacts/methods'/name).read_text().splitlines()]
    try:
        require(report['schema']=='witgen-methods-receipt-v2' and report['status']=='PASS','not a bound v2 PASS')
        required=['artifacts/methods/'+name for name in ('bundle/manifest.json','bundle/reference.json',
            'native-requests.jsonl','native-results.jsonl','case-results.jsonl','negative-requests.jsonl',
            'negative-results.jsonl','negative-case-results.jsonl','cargo-artifacts.jsonl',
            'required-cases.json','source-config.json','nat.json','u64.json','mixed.json','affine.json','from-affine.json')]
        required += [directory+'/'+name for directory in ('artifacts/u64','artifacts/methods')
                     for name in ('u64-tests.json','u64-shared.json')]
        require(set(required)<=set(report['artifact_hashes']),'missing required artifact hashes')
        for group in ('source_hashes','artifact_hashes'):
            require(bool(report[group]),'empty '+group)
            for name,digest in report[group].items():
                require(isinstance(digest,str) and bool(re.fullmatch('[0-9a-f]{64}',digest)),'invalid digest')
                verify_hash(root/name,digest)
        for name,digest in report['build']['configuration_hashes'].items():
            verify_hash(name,digest)
        binary=report['executed_binary']
        require(bool(re.fullmatch('[0-9a-f]{64}',binary['sha256'])),'invalid executable digest')
        verify_hash(binary['path'],binary['sha256'])
        artifact=cargo_executable((root/'artifacts/methods/cargo-artifacts.jsonl').read_text())
        require(artifact==report['build']['compiler_artifact'] and artifact['executable']==binary['path'],
                'build/executed artifact mismatch')
        executions=[c['argv'] for c in report['commands'] if c['log'] in
                    ('native-results.jsonl','negative-results.jsonl')]
        require(executions==[[binary['path']],[binary['path']]],'execution command mismatch')
        require(all(c['returncode']==0 for c in report['commands']),'failed command')
        config=load('artifacts/methods/source-config.json')
        require(config['source_hashes']==report['source_hashes'] and config['build']==report['build'],
                'source/build configuration mismatch')
        require(config['field_moduli']==report['field_moduli']==list(FIELD_MODULI),'field configuration mismatch')
        require(load('artifacts/methods/required-cases.json')==required_cases(),'case specification mismatch')
        cases=load('artifacts/methods/bundle/reference.json')
        u64=load('artifacts/u64/u64-tests.json')
        require(len(u64['fixtures'])==u64['field_caller_checks'],'U64 declared total mismatch')
        cases += [dict(x,mode='u64') for x in u64['fixtures']]
        require(report['case_coverage']==validate_case_coverage(cases),'case coverage mismatch')
        require(report['native_cases']==len(cases) and report['per_program']==dict(Counter(c['program'] for c in cases)),
                'case count mismatch')
        require(rows('native-requests.jsonl')==[{k:c[k] for k in ('program','inputs')} for c in cases],
                'ordered request mismatch')
        records=validate_results(cases,rows('native-results.jsonl'),config['output_types'])
        require(records==rows('case-results.jsonl'),'complete case/result mismatch')
        assertions=semantic_assertions(records)
        require(report['semantic_assertions']==assertions,'semantic assertion mismatch')
        for label,checks in assertions.items():
            require(report[label] is all(c['passed'] for c in checks),'semantic flag mismatch')
        negative=[{'program':f'field_{f}_u64_methods','inputs':[FIELD_MODULI[f],'0']} for f in range(3)]
        neg=rows('negative-results.jsonl')
        require(rows('negative-requests.jsonl')==negative and len(neg)==len(negative),'negative request mismatch')
        require(all(r.get('error')=='noncanonical_field' for r in neg),'canonicality assertion mismatch')
        require(rows('negative-case-results.jsonl')==[
            {'case_index':i,'request':request,'expected_error':'noncanonical_field','result':result}
            for i,(request,result) in enumerate(zip(negative,neg))],'negative records mismatch')
    except (KeyError,TypeError,AttributeError) as error:
        raise ValueError('incomplete historical receipt: '+str(error)) from error
    return report


def run_all():
    (ART/'verification.json').unlink(missing_ok=True)
    ART.mkdir(parents=True,exist_ok=True)
    before=sources();commands=[];consumed={}
    build_env=build_environment();build_configs=configuration_hashes()
    def read_artifact(path):
        data=path.read_bytes();digest=hashlib.sha256(data).hexdigest()
        if path in consumed and consumed[path]!=digest:
            raise ValueError('consumed artifact changed during verification: '+str(path))
        consumed[path]=digest
        return data
    def load_artifact(path):
        return json.loads(read_artifact(path))
    def run(command,log,input_text=None,timeout=180):
        r=subprocess.run(command,cwd=ROOT,text=True,input=input_text,capture_output=True,timeout=timeout)
        (ART/log).write_text(r.stdout if log.endswith('.jsonl') else r.stdout+r.stderr)
        stderr_log=log+'.stderr.log'
        (ART/stderr_log).write_text(r.stderr)
        if r.returncode:raise RuntimeError(f'{command!r} failed:\n{(r.stdout+r.stderr)[-5000:]}')
        commands.append({'argv':command,'cwd':str(ROOT),'log':log,
                         'stderr_log':stderr_log,'returncode':r.returncode})
        return r.stdout
    run(['lake','build','Witgen.Typed.Audit','Witgen.Typed.PublicTests','Witgen.U64.Tests',
         'Witgen.StructSetTests','Witgen.StructSetAudit','Witgen.PrimalityTests'],'lean-build.log')
    audits={}
    for file,names in [('Witgen/Typed/Audit.lean',TYPED_AUDIT),('Witgen/U64/Audit.lean',U64_AUDIT),
                       ('Witgen/StructSetAudit.lean',STRUCT_AUDIT)]:
        log=file.replace('/','-')+'.log'
        text=run(['lake','env','lean','-DwarningAsError=true',file],log)
        audits[file]={'declarations':list(names),'axioms':check_axioms(text,names,
                       allowed_axioms={'propext','Quot.sound','Classical.choice'})}
    run(['lake','env','lean','--run','MainMethods.lean','export','artifacts/methods/bundle'],'export.log')
    run(['lake','env','lean','--run','MainU64.lean','export','artifacts/u64'],'u64-export.log')
    manifest=load_artifact(ART/'bundle/manifest.json')
    modules={entry['name']:(load_artifact(ART/'bundle'/f'{entry["name"]}.json'),entry['mode'])
             for entry in manifest['programs']}
    required_modules={(c['program'],c['mode']) for c in required_cases() if not c['program'].startswith('field.')}
    if ({(name,mode) for name,(_,mode) in modules.items()}!=required_modules
            or len(modules)!=len(manifest['programs'])):raise ValueError('module coverage mismatch')
    aliases={'nat':'field_2_nat_methods','u64':'field_2_u64_methods','mixed':'secp_mixed_fields',
             'affine':'secp_generator_affine_roundtrip','from-affine':'secp_from_affine'}
    for alias,source_name in aliases.items():
        (ART/(alias+'.json')).write_text(json.dumps(modules[source_name][0],indent=2)+'\n')
        read_artifact(ART/(alias+'.json'))
    for file in ('u64-shared.json','u64-tests.json'):
        data=read_artifact(ROOT/'artifacts/u64'/file)
        (ART/file).write_bytes(data)
        consumed[ART/file]=hashlib.sha256(data).hexdigest()
    bundle=load_artifact(ROOT/'artifacts/u64/u64-shared.json')
    for name,(module,mode) in modules.items():
        if mode=='u64':
            if module['methods']!=bundle['methods']:raise ValueError('shared U64 registry differs')
            bundle['programs'].append({k:v for k,v in module.items() if k not in ('methods','version')})
    compiled={name:value for name,value in modules.items() if value[1]!='u64'}
    compiled['shared_u64']=(bundle,'u64')
    output_dir=ROOT/'backend/src/generated_methods';output_dir.mkdir(exist_ok=True)
    declarations=[];arms=[];output_types={};source_texts={}
    for i,(name,(module,mode)) in enumerate(compiled.items()):
        stem='shared_u64' if name=='shared_u64' else f'module_{i}'
        source=emit_module(module,mode);source_texts[name]=source
        (output_dir/(stem+'.rs')).write_text(source)
        declarations.append(f'#[allow(dead_code)]\n#[path = "../generated_methods/{stem}.rs"]\nmod module_{i};')
        if name=='shared_u64':
            for index,program in enumerate(module['programs']):
                arms.append(f'{json.dumps(program["name"])} => module_{i}::run_json({index}, inputs),')
                output_types[program['name']]=program['output']
        else:
            arms.append(f'{json.dumps(name)} => module_{i}::run_json(inputs),');output_types[name]=module['output']
    driver='''
use std::io::{self,BufRead};
fn execute(request: &serde_json::Value) -> witgen_native::Result<serde_json::Value> {
 let program=request["program"].as_str().ok_or(witgen_native::Error::InvalidInputType{expected:"program string"})?;
 let inputs=request["inputs"].as_array().ok_or(witgen_native::Error::InvalidInputType{expected:"input array"})?;
 match program {
'''+ '\n'.join(arms)+'''
 _=>Err(witgen_native::Error::UnknownProgram(program.to_owned()))
 }
}
fn main(){
 for line in io::stdin().lock().lines(){
  let result=line.map_err(witgen_native::Error::from)
   .and_then(|s|serde_json::from_str(&s).map_err(witgen_native::Error::from))
   .and_then(|x|execute(&x));
  let output=match result {Ok(v)=>serde_json::json!({"ok":v}),Err(e)=>serde_json::json!({"error":e.code(),"message":e.to_string()})};
  println!("{}",output);
 }
}
'''
    binary_source=ROOT/'backend/src/bin/witgen-methods.rs'
    binary_source.write_text('\n'.join(declarations)+driver)
    run(['rustfmt','--edition','2021',str(binary_source)],'rustfmt.log')
    build_command=['cargo','build','--locked','--manifest-path','backend/Cargo.toml',
                   '--bin','witgen-methods','--message-format=json-render-diagnostics']
    cargo_version=run(['cargo','--version','--verbose'],'cargo-version.log').strip()
    rustc_version=run(['rustc','--version','--verbose'],'rustc-version.log').strip()
    cargo_output=run(build_command,'rust-build.log')
    (ART/'cargo-artifacts.jsonl').write_text(cargo_output)
    artifact=cargo_executable(cargo_output)
    binary=Path(artifact['executable'])
    binary_hash=hashlib.sha256(binary.read_bytes()).hexdigest()
    cases=load_artifact(ART/'bundle/reference.json')
    u64_report=load_artifact(ROOT/'artifacts/u64/u64-tests.json')
    if len(u64_report['fixtures'])!=u64_report['field_caller_checks']:raise ValueError('U64 declared total mismatch')
    cases += [dict(x,mode='u64') for x in u64_report['fixtures']]
    coverage=validate_case_coverage(cases)
    expected_names=set(modules)|{p['name'] for p in bundle['programs']}
    if set(c['program'] for c in cases)!=expected_names:raise ValueError('missing program fixtures')
    (ART/'required-cases.json').write_text(json.dumps(required_cases(),indent=2)+'\n')
    requests=[{'program':c['program'],'inputs':c['inputs']} for c in cases]
    request_text=jsonl(requests)
    (ART/'native-requests.jsonl').write_text(request_text)
    text=run([str(binary)],'native-results.jsonl',request_text)
    results=[json.loads(line) for line in text.splitlines()]
    records=validate_results(cases,results,output_types)
    (ART/'case-results.jsonl').write_text(jsonl(records))
    assertions=semantic_assertions(records)
    source=source_texts['shared_u64']
    if len(re.findall(r'^fn method_\d+\(',source,re.M))!=12 or source.count('.rev()')!=1:
        raise ValueError('U64 methods/loop duplicated')
    arithmetic=source.split('fn method_0(',1)[1].split('// method 3:',1)[0]
    if any(x in arithmetic for x in ('Integer','nat_','bn254_','secp_','field_modulus',' % ')):
        raise ValueError('whole-field arithmetic hidden in U64 methods')
    # Emitter validates every call; count actual retained call sites and definitions too.
    if 'method_1(' not in source.split('fn method_2(',1)[1].split('// method 3:',1)[0]:
        raise ValueError('Square no longer calls Mul')
    negative=[{'program':f'field_{f}_u64_methods','inputs':[FIELD_MODULI[f],'0']} for f in range(3)]
    (ART/'negative-requests.jsonl').write_text(jsonl(negative))
    neg=[json.loads(line) for line in run([str(binary)],'negative-results.jsonl',
         jsonl(negative)).splitlines()]
    if len(neg)!=3 or any(row.get('error')!='noncanonical_field' for row in neg):raise ValueError('canonicality gate failed')
    (ART/'negative-case-results.jsonl').write_text(jsonl([
        {'case_index':i,'request':request,'expected_error':'noncanonical_field','result':result}
        for i,(request,result) in enumerate(zip(negative,neg))]))
    if before!=sources():raise ValueError('source changed during verification')
    if binary_hash!=hashlib.sha256(binary.read_bytes()).hexdigest():
        raise ValueError('executed binary changed during verification')
    if build_env!=build_environment() or build_configs!=configuration_hashes():
        raise ValueError('build configuration changed during verification')
    for path,digest in consumed.items():
        if hashlib.sha256(path.read_bytes()).hexdigest()!=digest:
            raise ValueError('consumed artifact changed during verification: '+str(path))
    build={'argv':build_command,'cwd':str(ROOT),'environment':build_env,
           'configuration_hashes':build_configs,'compiler_artifact':artifact,
           'cargo_version':cargo_version,'rustc_version':rustc_version}
    source_config={'source_hashes':before,'build':build,'field_moduli':list(FIELD_MODULI),
                   'output_types':output_types,
                   'case_specification':['MainMethods.inputPairs/exportAll','Witgen.U64.Tests.casesFor/checkFieldPair'],
                   'reference_files':['artifacts/methods/bundle/reference.json','artifacts/u64/u64-tests.json']}
    (ART/'source-config.json').write_text(json.dumps(source_config,indent=2)+'\n')
    artifact_paths=list(consumed)+list(output_dir.glob('*.rs'))+[binary_source]
    artifact_paths += [ART/name for name in ('native-requests.jsonl','native-results.jsonl','case-results.jsonl',
        'negative-requests.jsonl','negative-results.jsonl','negative-case-results.jsonl',
        'cargo-artifacts.jsonl','source-config.json','required-cases.json')]
    artifact_paths += [ART/c[key] for c in commands for key in ('log','stderr_log')]
    report={'schema':'witgen-methods-receipt-v2','status':'PASS','native_cases':len(cases),
      'per_program':dict(Counter(c['program'] for c in cases)),
      'field_moduli':list(FIELD_MODULI),'u64_generic_bodies':3,'u64_total_methods':12,
      'u64_callers':len(bundle['programs']),'calls_retained':True,'no_u64_bigint_field_arithmetic':True,
      **{label:all(check['passed'] for check in checks) for label,checks in assertions.items()},
      'semantic_assertions':assertions,'case_coverage':coverage,'curve_backend':'arkworks',
      'audits':audits,'commands':commands,'source_hashes':before,
      'executed_binary':{'path':str(binary),'sha256':binary_hash},
      'build':build,
      'artifact_hashes':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(set(artifact_paths))},
      'scope':{'curve_to_field_lowering':False,'curve_to_u64_lowering':False,'generator_order_proved':False,
               'native_compiler_and_libraries':'tested TCB, not kernel-verified','u64_multiply':'reference bounded double/add, not optimized or constant-time certified'}}
    pending=ART/'verification.pending.json'
    pending.write_text(json.dumps(report,indent=2)+'\n')
    try:
        validate_historical_receipt(pending)
        pending.replace(ART/'verification.json')
    finally:
        pending.unlink(missing_ok=True)
    return report

if __name__=='__main__':
    r=run_all();print(json.dumps({k:v for k,v in r.items() if k not in ('commands','source_hashes','artifact_hashes','audits')},indent=2))
