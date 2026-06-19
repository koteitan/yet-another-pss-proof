# Assembly: caseB conclusion EXISTS delta with (a)delta<alpha (b)delta in CsetSelf(alpha)v
# (c)delta u-canon (d)psiSelf delta u = psiSelf(psiSelf eta w)u.
# delta = proj_u eta (= proj_u c). Components:
#   H2: psiSelf(proj_u eta) u = psiSelf eta u   [psi_proj at eta, = IH(eta)]
#   H1: psiSelf eta u = psiSelf(psiSelf eta w) u [subscript collapse]
#   => (d) by H2.trans H1.
#   (c) delta=proj_u eta u-canonical : proj_u eta is u-reduced (no u-violators) => acanon.
#   (a) delta<alpha, (b) delta in CsetSelf(alpha)v : the IH(eta) rep ALSO gives these IF
#       we invoke NoncanonValueMem-rep at eta with BOUND alpha (not eta). 
# RECONSIDER the IH application: IHα is the well-founded hyp 'NoncanonValueMem at all beta<alpha'.
#   NoncanonValueMem(beta): xi in CsetSelf(beta)v', xi<beta, xi u-noncanon, v'<=u =>
#     psiSelf xi u in CsetSelf(beta)v'. To get eta's rep IN CsetSelf(alpha)v with delta<alpha,
#     we need the rep-form at BOUND alpha. But IHα only gives bounds beta<alpha.
#   The rep at bound alpha for eta is what 'rnk' produces (current alpha). eta is at rank n
#   (hηX), so rnk's IHn gives eta's rep? NO - eta is u-NON-canonical (hηu) so IHn(eta) gives
#   a rep delta_eta<alpha, in CsetSelf(alpha)v, u-canon, psiSelf delta_eta u = psiSelf eta u.
#   THAT delta_eta = the rep of eta = proj_u eta = our delta! And (a)(b)(c)(d-via-H1) all from IHn(eta)!
# So caseB <- IHn(eta) [eta at rank n, u-non-canon] gives delta with psiSelf delta u=psiSelf eta u,
#   then H1 (psiSelf eta u = psiSelf c u) finishes (d). TEST: eta reachable at rank n satisfies
#   IHn's hyps (eta in CstepSelf'^[n], eta<alpha, eta u-noncanon, v<=u). All hold at call site!
# So the ONLY genuinely-new content beyond IHn is H1. Confirm H1 is the sole residual.
print("Design confirmed analytically: caseB <- IHn(eta) [rank-n rep of eta] . H1.")
print("IHn(eta) gives delta=rep(eta): delta<alpha, in CsetSelf(alpha)v, u-canon, psiSelf delta u=psiSelf eta u.")
print("H1: psiSelf eta u = psiSelf(psiSelf eta w) u finishes the value-identity.")
print("=> caseB residual = H1 ALONE (a subscript-collapse), given the rnk IHn.")
