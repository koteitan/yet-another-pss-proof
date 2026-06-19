# The CRUX: psiSelf eta u <= psiSelf(psiSelf eta w) u  (623/623). Find its proof.
# c = psiSelf eta w, u<=w, eta u-canon, c u-non-canon.
# Sub-facts to test:
#  X1: psiSelf eta u <= c=psiSelf eta w     (psiSelf_mono? no, both args eta but diff sub)
#      Actually psiSelf eta u vs psiSelf eta w: u<=w. Is psiSelf eta u <= psiSelf eta w?
#  X2: c=psiSelf eta w <= psiSelf c u ??  (no, psiSelf c u <= c)
#  X3: psiSelf eta u <= psiSelf c u directly; and is it EQUALITY? (F3 says yes 623/623)
#  X4: the route: eta u-canon => psiSelf eta u is the value; c u-non-canon and c on
#      eta's plateau => psiSelf c u = psiSelf eta u. The proof = psiSelf_eq_of_notMem
#      at (eta, c)?? psiSelf_eq_of_notMem(eta<=c? NO c<eta). Reversed.
#  X5: KEY alternative -- prove psiSelf c u = psiSelf eta u via:
#      psiSelf c u <= psiSelf eta u  (mono, c<=eta) -- have.
#      psiSelf eta u <= psiSelf c u  -- want. Equivalent: psiSelf eta u NOT in stuff < it...
#  Try: is psiSelf eta u <= psiSelf eta w (=c)?  AND psiSelf c u >= psiSelf eta u because
#      psiSelf eta u <= c so by below_psiSelf, psiSelf eta u in CsetSelf(c) u UNLESS
#      psiSelf eta u >= psiSelf c u. i.e. EITHER psiSelf eta u < psiSelf c u (want >=, contra)
#      OR psiSelf eta u in CsetSelf(c) u. Test: is psiSelf eta u in CsetSelf(c) u? If NOT,
#      then psiSelf eta u >= psiSelf c u (the crux) by below_psiSelf contrapositive!
import sys
sys.path.insert(0,'.')
from valnorm import conv, nrm, lt_term, G, in_OT
from wfe_explore import translate, enum_ST
Z=()
def cn(x): return tuple(('D',vv,cn(bb)) for _,vv,bb in x)
def le_t(a,b): return a==b or lt_term(a,b)
def acanon(u,t): return not any(not lt_term(x,t) for x in G(u,t))
def princ_in(alpha,v,p):
    _,u,xi=p
    if u<v: return True
    if not lt_term(xi,alpha): return False
    if not acanon(u,xi): return False
    return term_in(alpha,v,xi)
def term_in(alpha,v,delta):
    if delta==Z: return True
    return all(princ_in(alpha,v,p) for p in delta)
def psi(a,arg): return cn(nrm((('D',a,arg),)))
def noncanon_self(u,t): return not term_in(t,u,t)
def collect(r):
    s=set()
    for M in enum_ST(rounds=r):
        t=conv(translate(M)); st=[t]
        while st:
            x=st.pop()
            if not x: continue
            for (_,_,arg) in x: st.append(arg)
            s.add(x)
    return s
for r in (6,7):
    terms=[cn(t) for t in collect(r) if in_OT(t)]
    seen=set(); n=0
    x1=0  # psiSelf eta u <= psiSelf eta w (=c)
    x5=0  # psiSelf eta u NOT in CsetSelf(c) u  (=> crux via below_psiSelf contrapos)
    peu_le_c=0  # psiSelf eta u <= c
    for eta in terms:
        for w in range(0,4):
            pw=psi(w,eta)
            for u in range(0,4):
                if not(u<=w and (not noncanon_self(u,eta)) and noncanon_self(u,pw)): continue
                key=(str(eta),w,u)
                if key in seen: continue
                seen.add(key); n+=1
                c=pw; peu=psi(u,eta); pcu=psi(u,c)
                if le_t(peu,pw): x1+=1
                if not term_in(c,u,peu): x5+=1
                if le_t(peu,c): peu_le_c+=1
    print(f"rounds={r}: inst={n}")
    print(f"  X1 psiSelf eta u <= psiSelf eta w (=c)        = {x1}/{n}")
    print(f"  X5 psiSelf eta u NOT in CsetSelf(c) u (CRUX)  = {x5}/{n}")
    print(f"  psiSelf eta u <= c                            = {peu_le_c}/{n}")
