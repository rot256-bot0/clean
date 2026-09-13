"""Independent SOURCE-REVIEWED translation of all active winning witness blocks/rows.
NOT an extracted Lean circuit and NOT a proof of cross-language correspondence.
No imports from downloaded Lean; all loops finite. Field values canonical integers.
"""
from pathlib import Path
import json, math
P = 21888242871839275222246405745257275088548364400416034343698204186575808495617
SHIFT = sum(1 << (8*j+7) for j in range(510)) + (1 << 4095)
T = json.loads((Path(__file__).parent/'tables.json').read_text())

def limbs(x, B, m): return [(x >> (B*i)) % (1 << B) for i in range(m)]
def value(a, B): return sum(x << (B*i) for i,x in enumerate(a))
def ev(a, x):
    y=0
    for c in reversed(a): y=(y*x+c)%P
    return y

def conv(a,b):
    out=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): out[i+j]+=x*y
    return [x%P for x in out]

def em_bytes(digest):
    return bytes([0,1])+bytes([255])*458+bytes([0])+bytes.fromhex('3031300d060960864801650304020105000420')+digest

class Runner:
    def __init__(self, witness=None):
        self.input_witness=witness; self.witness=[]; self.cursor=0; self.rows=0; self.failures=[]; self.events=[]
    def alloc(self,n,compute):
        if self.input_witness is None: a=compute()
        else: a=self.input_witness[self.cursor:self.cursor+n]
        if len(a)!=n or any(type(x)!=int or not 0<=x<P for x in a): raise ValueError(('bad witness block',self.cursor,n))
        self.events.append(('witness',n))
        self.cursor+=n; self.witness.extend(a); return a
    def check(self,x):
        self.events.append(('assert',1))
        if x%P: self.failures.append(self.rows)
        self.rows+=1
    def rc(self,x,width):
        x%=P
        bits=self.alloc(width-1,lambda:[(x>>i)&1 for i in range(width-1)])
        for bit in bits:self.check(bit*(bit-1))
        top=(x-sum(b<<i for i,b in enumerate(bits)))*pow(1<<(width-1),-1,P)%P
        self.check(top*(top-1));return bits+[top]
    def norm(self,a,B,top):
        result=[]
        for i,x in enumerate(a):result.extend(self.rc(x,top if i==len(a)-1 else B))
        return result
    def interpolate(self,a,b,z):
        for c in range(1,len(z)+1):self.check(ev(a,c)*ev(b,c)-ev(z,c))
    def carries(self,lhs,rhs,B,widths,offsets,sizes):
        # GroupedEqXV.carryExpr; offsets are VR.OFFf (negative side).
        pos=0;signed=0
        for k,width in enumerate(widths):
            size=sizes[k]
            delta=sum((lhs[pos+j]-rhs[pos+j])*(1<<(B*j)) for j in range(size))
            signed=(signed+delta)*pow(1<<(B*size),-1,P)%P
            self.rc((signed+offsets[k])%P,width)
            pos+=size
    def lt(self,signature,modulus):
        def chunks(raw):
            raw=bytes(28)+raw
            return [int.from_bytes(raw[i:i+6],'big') for i in range(0,540,6)]
        s,n=chunks(signature),chunks(modulus)
        first=next((j for j in range(90) if n[j]!=s[j]),None)
        flags=self.alloc(17,lambda:[int(n[:5*g]==s[:5*g]) for g in range(1,18)])
        dv=self.alloc(1,lambda:[max(0,n[first]-s[first]-1) if first is not None else 0])[0]
        x=self.alloc(5,lambda:[(n[5*(first//5)+i]-s[5*(first//5)+i])%P for i in range(5)] if first is not None else [0]*5)
        ls=[];packed=0
        for a in x:packed=(packed*(1<<48)+a)%P;ls.append((packed-dv-1)%P)
        product=ls[0]
        for j in range(1,4):
            rhs=product*ls[j]%P
            product=self.alloc(1,lambda:[rhs])[0];self.check(rhs-product)
        self.check(product*ls[4]);self.rc(dv,48)
        group=lambda a,g:sum(a[5*g+i]<<(48*(4-i)) for i in range(5))
        for g in range(17):self.check(flags[g]*(group(n,g)-group(s,g)))
        for u in range(5,90):
            before=flags[u//5-1];after=0 if u//5==17 else flags[u//5]
            self.check((before-after)*(n[u]-s[u]-x[u%5]))
        self.check((1-flags[0])*(n[4]-s[4]-dv-1))
    def window(self,a,B):
        K=19;t=1<<B; full=conv(a,a)
        sums=self.alloc(38,lambda:[sum((full[9*w+j] if 9*w+j<len(full) else 0)*pow(t,j,P) for j in range(9))%P for w in range(38)])
        def factors(c):
            h=[pow(t,i,P)*ev(a[i::9],c)%P for i in range(9)]
            A=[sum(h[k:])%P for k in range(10)]
            return [(2*h[8]*(A[1]-A[4]))%P,(2*h[7]*(A[2]-A[4]))%P,(2*h[6]*(A[3]-A[4]))%P,A[5]*(2*A[4]-A[5])%P],A[0]
        products=self.alloc(148,lambda:[v for c in range(1,38) for v in factors(c)[0]])
        for c in range(1,38):
            f,_=factors(c)
            for j in range(4):self.check(f[j]-products[4*(c-1)+j])
        high=[sum(products[4*s:4*s+4])%P for s in range(37)]
        high.append(sum(-((-1)**(37-s))*math.comb(37,s)*high[s] for s in range(37))%P)
        for index in range(38):
            c=index+1;_,beta=factors(c)
            self.check(pow(t,9,P)*beta*beta-(pow(t,9,P)*ev(sums,c)-(c-pow(t,9,P))*high[index]))
        return [sums[k//9] if k%9==0 else 0 for k in range(341)]
    def square(self,stored,n,first=False):
        B=24;m=171;N=value(n,B);A=value(stored,B)
        product=A*A if first else (A-SHIFT)**2
        quotient,remainder=divmod(product,N)
        branch=int(remainder >= (1<<4096)-SHIFT)
        q=self.alloc(m,lambda:limbs(quotient+branch,B,m))
        r=self.alloc(m,lambda:limbs(remainder+SHIFT-branch*N,B,m))
        self.norm(q,B,16 if first else 15);bits=self.norm(r,B,16)
        a=stored if first else [(x-d)%P for x,d in zip(stored,limbs(SHIFT,B,m))]
        pc=self.window(a,B)
        qn=self.alloc(340,lambda:conv(q,n)[:340])
        rhs=[(x+(r[k]-limbs(SHIFT,B,m)[k] if k<m else 0))%P for k,x in enumerate(qn)]+[0]
        top=(ev(pc,1<<B)-ev(rhs[:-1],1<<B))*pow(1<<(B*340),-1,P)%P
        self.interpolate(q,n,qn+[top])
        rhs[-1]=top
        kind='first' if first else 'middle'
        self.carries(pc,rhs,B,T[kind+'_widths'][:37],T[kind+'_offset_negative'],[9]*37)
        return r,bits
    def final(self,a,b,n,em):
        B=16;m=256
        prod=(value(a,B)-SHIFT)**2*value(b,B)
        q=self.alloc(512,lambda:limbs(prod//value(n,B),B,512))
        self.norm(q,B,15)
        shifted=[(x-d)%P for x,d in zip(a,limbs(SHIFT,B,m))]
        z1=self.alloc(511,lambda:conv(shifted,shifted));self.interpolate(shifted,shifted,z1)
        z2=self.alloc(766,lambda:conv(z1,b));self.interpolate(z1,b,z2)
        qn=self.alloc(766,lambda:conv(q,n)[:766])
        rhs=[(x+(em[k] if k<m else 0))%P for k,x in enumerate(qn)]+[0]
        lhs=z2+[0]
        top=(ev(lhs,1<<B)-ev(rhs[:-1],1<<B))*pow(1<<(B*766),-1,P)%P
        self.interpolate(q,n,qn+[top]);rhs[-1]=top
        sizes=[9 if k==0 else 13 if k<10 else 12 if k<52 else 13 for k in range(62)]
        self.carries(lhs,rhs,B,T['final_widths'][:62],T['final_offset_negative'],sizes)
    def run(self,modulus,digest,signature):
        # External assumptions, not counted as circuit rows.
        assert len(modulus)==len(signature)==512 and len(digest)==32
        N=int.from_bytes(modulus,'big'); S=int.from_bytes(signature,'big')
        assert N.bit_length()==4096
        self.lt(signature,modulus)
        n=limbs(N,24,171);r,bits=self.square(limbs(S,24,171),n,True)
        for _ in range(14):r,bits=self.square(r,n)
        a16=[sum(bits[16*k+i]*(1<<i) for i in range(16))%P for k in range(256)]
        self.final(a16,limbs(S,16,256),limbs(N,16,256),limbs(int.from_bytes(em_bytes(digest),'big'),16,256))
        assert self.cursor==160527 and self.rows==161242,(self.cursor,self.rows)
        if self.input_witness is not None:assert len(self.input_witness)==self.cursor
        return {'evidence':'SOURCE_REVIEWED_NOT_LEAN_BOUND','allocations':self.cursor,'constraints':self.rows,'failed_rows':self.failures,'rsa_check':S<N and pow(S,65537,N)==int.from_bytes(em_bytes(digest),'big')}
