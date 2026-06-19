# hVB needs: u-canonical gamma in [c,eta), c=psiSelf eta w => psiSelf gamma u < psiSelf c u.
# psiSelf_strict_mono_arg(gamma<eta, gamma canon) gives psiSelf gamma u < psiSelf eta u (GREEN).
# Q1: is psiSelf c u  >=  psiSelf eta u  i.e. would psiSelf gamma u < psiSelf eta u <= psiSelf c u
#     give hVB directly? Need psiSelf eta u <= psiSelf c u = the CRUX (circular).
# Q2: ALTERNATIVE - restructure collapse to target psiSelf eta u: apply
#     collapseSelf_le_valuebounded with alpha=c, beta=eta needs value-bound vs psiSelf c u.
#     OR with the OTHER orientation. The crux is psiSelf c u = psiSelf eta u; we want to
#     avoid assuming it. Test: is psiSelf gamma u < psiSelf eta u (623/623, =strict_mono)
#     AND psiSelf c u == psiSelf eta u? If the collapse holds then hVB(<psiSelf c u) <=>
#     hVB(<psiSelf eta u) = strict_mono. So they're equivalent GIVEN collapse - circular.
# Q3: THE NON-CIRCULAR test: prove hVB(< psiSelf c u) WITHOUT the collapse. Is there a
#     direct reason psiSelf gamma u < psiSelf c u for u-canon gamma in [c,eta)?
#     gamma >= c = psiSelf eta w. psiSelf gamma u vs psiSelf (psiSelf eta w) u.
#     gamma is u-canonical, c may not be. Hmm gamma>=c but psiSelf gamma u < psiSelf c u
#     would VIOLATE psiSelf_mono_arg (gamma>=c => psiSelf gamma u >= psiSelf c u)!!
#     UNLESS gamma's value at u is genuinely smaller despite gamma>=c (Omega-crossing again).
#  CHECK: for u-canon gamma in [c,eta), is gamma >= c as ORDINAL VALUE? (lt_term unfaithful!)
#     If gamma >= c faithfully then psiSelf_mono gives psiSelf gamma u >= psiSelf c u,
#     CONTRADICTING hVB (psiSelf gamma u < psiSelf c u). So EITHER hVB is false OR these
#     gamma are NOT >= c in true ordinal value (term order lied). DECISIVE for the route.
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
def selfcanon(u,t): return term_in(t,u,t)
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
    terms=[cn(t) for t in collect(r) if in_OT(t)]; pool=terms
    seen=set(); n=0
    gam_ge_c_value_via_psi=0  # psiSelf gamma u >= psiSelf c u for some gap-canon gamma? (would be hVB viol)
    crux_eq=0
    tot_gam=0; psimono_resp=0
    for eta in terms:
        for w in range(0,4):
            pw=psi(w,eta)
            for u in range(0,4):
                if not(u<=w and selfcanon(u,eta) and (not selfcanon(u,pw))): continue
                key=(str(eta),w,u)
                if key in seen: continue
                seen.add(key); n+=1
                c=pw; pcu=psi(u,c); peu=psi(u,eta)
                if pcu==peu: crux_eq+=1
                gam=[g for g in pool if le_t(c,g) and lt_term(g,eta) and selfcanon(u,g)]
                for g in gam:
                    tot_gam+=1
                    pg=psi(u,g)
                    # psiSelf_mono would say g>=c (term) => pg>=pcu. Check if RESPECTED:
                    if le_t(pcu,pg): psimono_resp+=1   # pg>=pcu (mono respected -> hVB viol!)
    print(f"rounds={r}: subA-A inst={n}  crux psiSelf c u==psiSelf eta u={crux_eq}/{n}")
    print(f"  gap-canon gamma total={tot_gam}  with psiSelf gamma u >= psiSelf c u (hVB VIOL)={psimono_resp}")
