# Is hVB reducible to strict_mono? hVB: u-canon gamma, c<=gamma<eta (TERM order) =>
#   psiSelf gamma u < psiSelf c u. We showed 0 viol (psiSelf gamma u always < psiSelf c u).
# strict_mono gives psiSelf gamma u < psiSelf eta u (gamma<eta TRUE, canon). For hVB we
# need < psiSelf c u. Since crux says psiSelf c u = psiSelf eta u, they coincide.
# KEY: can we get hVB from strict_mono to a CANONICAL bound <= c?
#   For u-canonical gamma in gap, is psiSelf gamma u < psiSelf c u because gamma's VALUE
#   psiSelf gamma u is < psiSelf c u and c's u-non-canonicity means psiSelf c u is a
#   PLATEAU value that dominates all canonical-arg values up to eta? 
# The genuinely-provable lemma (NO crux): for ANY delta and u-canon gamma with gamma<delta,
#   psiSelf gamma u < psiSelf delta u  (strict_mono). Apply delta=eta: psiSelf gamma u <
#   psiSelf eta u. So hVB-with-target-eta is FREE. The collapse needs target psiSelf c u.
# THEREFORE: restate collapse to use target psiSelf eta u! i.e. prove
#   psiSelf c u = psiSelf eta u  via collapseSelf_le_valuebounded ALPHA=c BETA=eta with
#   value-bound psiSelf gamma u < psiSelf c u. The bound is vs ALPHA=c per the lemma sig.
# So I CANNOT swap to eta in the current lemma (bound is vs psiSelf alpha = psiSelf c).
# OPTION: generalize collapseSelf_le_valuebounded to bound vs psiSelf BETA (=eta) instead
#   of psiSelf alpha. Does the PROOF still work? Witness xi canonical < beta=eta,
#   psiSelf xi a = psiSelf c a (=alpha's value). Cases: xi<c: strict_mono psiSelf xi a<
#   psiSelf c a, but heq says =, contra. c<=xi<eta: need psiSelf xi a != psiSelf c a.
#   value-bound-vs-eta: psiSelf xi a < psiSelf eta a. Does that contradict psiSelf xi a =
#   psiSelf c a? Only if psiSelf c a >= psiSelf eta a, i.e. psiSelf eta a <= psiSelf c a
#   = the CRUX again. So bound-vs-beta does NOT close without crux. Bound-vs-alpha(=c) DOES
#   (it directly contradicts heq: psiSelf xi a = psiSelf c a but < psiSelf c a). 
# CONCLUSION: the lemma correctly needs bound vs psiSelf alpha=psiSelf c. And hVB
#   (psiSelf gamma u < psiSelf c u) is NOT free from strict_mono (that gives vs eta).
#   hVB is genuine content. VERIFY hVB is NOT derivable from strict_mono alone by checking
#   psiSelf c u < psiSelf eta u STRICTLY ever (if psiSelf c u < psiSelf eta u sometimes,
#   then bound-vs-c is STRICTLY stronger than bound-vs-eta = strict_mono, confirming
#   hVB needs more). But crux says psiSelf c u == psiSelf eta u ALWAYS (623/623), so
#   bound-vs-c and bound-vs-eta COINCIDE in truth value -> hVB IS equivalent to strict_mono
#   GIVEN the crux. Without crux, hVB(vs c) vs strict_mono(vs eta) differ iff psiSelf c u
#   != psiSelf eta u. Since they're always equal, hVB holds. But PROVING hVB in Lean w/o
#   crux: need psiSelf gamma u < psiSelf c u. Have psiSelf gamma u < psiSelf eta u (free).
#   Need psiSelf eta u <= psiSelf c u (crux). CIRCULAR at the value level.
# => hVB genuinely needs the crux/joint-IH. Confirm psiSelf c u vs psiSelf eta u once more
#    and whether psiSelf c u < psiSelf eta u EVER (if never, they're equal=crux).
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
for r in (7,):
    terms=[cn(t) for t in collect(r) if in_OT(t)]
    seen=set(); n=0; pcu_lt_peu=0; pcu_eq_peu=0
    for eta in terms:
        for w in range(0,4):
            pw=psi(w,eta)
            for u in range(0,4):
                if not(u<=w and selfcanon(u,eta) and (not selfcanon(u,pw))): continue
                key=(str(eta),w,u)
                if key in seen: continue
                seen.add(key); n+=1
                pcu=psi(u,pw); peu=psi(u,eta)
                if pcu==peu: pcu_eq_peu+=1
                elif lt_term(pcu,peu): pcu_lt_peu+=1
    print(f"rounds={r}: inst={n}  psiSelf c u == psiSelf eta u={pcu_eq_peu}  < ={pcu_lt_peu}")
