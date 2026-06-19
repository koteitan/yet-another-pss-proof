# Is subA_nm provable non-circularly, or is the crux (psiSelf eta u <= psiSelf c u)
# itself the plateau content? Test the candidate DIRECT route:
#   psiSelf c u = psiSelf eta u via psiSelf_eq_of_notMem applied at bound eta to c?
#   NO that's circular. Test instead:
# ALTERNATIVE: maybe subA_nm follows from a SIMPLER fact:
#   eta u-canonical + c=psiSelf eta w u-non-canonical + u<=w  =>  psiSelf c u = psiSelf eta u
# is equivalent to: psiSelf eta w "collapses to" the eta-plateau at subscript u.
# Check the EXACT Buchholz mechanism: since eta is u-canonical, psiSelf eta u is a
# GENERATOR firing into CsetSelf(eta+1)... and c=psiSelf eta w with w>=u.
# KEY TEST: is  psiSelf eta u  ==  psiSelf c u  provable from
#   (a) psiSelf eta u <= psiSelf c u   [the crux]   AND
#   (b) the crux itself = "no canonical zeta<eta has psiSelf zeta u >= psiSelf c u"?
# Simpler: TEST whether  psiSelf c u  is ALWAYS  ==  psiSelf eta u  (F3 re-confirm, 623/623)
# and whether the ALTERNATIVE smaller fact holds:
#   c < eta, c u-non-canonical, eta u-canonical => psiSelf c u NOT in CsetSelf(eta) u
#   can be shown via: every zeta in [c, eta) ... no. Test:
#   is psiSelf c u >= psiSelf eta u equivalent to "c is on eta's u-plateau top"?
# Decisive: does subA_nm reduce to psiSelf_notMem(eta,u) + F3, and is F3 (the value eq)
# provable WITHOUT subA_nm? F3 = psiSelf c u = psiSelf eta u. Buchholz: c=psiSelf eta w,
# and psiSelf eta u = psiSelf(psiSelf eta w) u would mean applying psiSelf at u to BOTH.
# Test the LICENSE: psiSelf(psiSelf eta w) u = psiSelf eta u  WHEN  psiSelf eta w is on
# the same u-plateau as eta. The plateau is [proj_u-rep, ...]. This IS the rep identity.
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
# the SIMPLE-FACT hypothesis: maybe subA_nm follows from
#   psiSelf c u  is itself u-non-canonical and <= c, AND c<eta both bound below eta,
#   then psiSelf c u in CsetSelf(eta) u would require a canonical generator zeta<eta
#   with psiSelf zeta u = psiSelf c u, forcing (inj) zeta = the canonical rep. The rep
#   of value psiSelf c u at subscript u is <= c < eta but its psiSelf zeta u < psiSelf eta u
#   (strict mono, zeta<eta canonical). So psiSelf c u < psiSelf eta u. Need this < the
#   ACTUAL relationship. TEST: exists canonical zeta<eta with psiSelf zeta u=psiSelf c u?
for r in (6,7):
    terms=[cn(t) for t in collect(r) if in_OT(t)]
    pool=terms
    seen=set(); n=0
    has_canon_wit=0   # exists canonical zeta<eta, psiSelf zeta u = psiSelf c u
    rep_is_eta=0      # the canonical realizer of psiSelf c u (at u) is eta itself
    for eta in terms:
        for w in range(0,4):
            pw=psi(w,eta)
            for u in range(0,4):
                if not(u<=w and (not noncanon_self(u,eta)) and noncanon_self(u,pw)): continue
                key=(str(eta),w,u)
                if key in seen: continue
                seen.add(key); n+=1
                c=pw; pcu=psi(u,c)
                wits=[z for z in pool if acanon(u,z) and lt_term(z,eta) and psi(u,z)==pcu]
                if wits: has_canon_wit+=1
                # is eta a canonical realizer? eta canon@u (hyp), psiSelf eta u = pcu?
                if acanon(u,eta) and psi(u,eta)==pcu: rep_is_eta+=1
    print(f"rounds={r}: subA-A inst={n}")
    print(f"  exists canonical zeta<eta with psiSelf zeta u = psiSelf c u = {has_canon_wit}/{n}  (0 = membership impossible cleanly)")
    print(f"  eta itself is a canonical u-realizer of psiSelf c u          = {rep_is_eta}/{n}  (eta=the rep)")
