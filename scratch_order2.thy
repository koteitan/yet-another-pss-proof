theory scratch_order2
  imports wo
begin

text \<open>Integration step (A2): define the Buchholz lex/dictionary order on the REAL
  ot datatype (with Om), as a new function oltL (not yet replacing olt), and prove
  its linearity (irrefl/total/trans).  Principals = Om/Th; tuples = Su.  Each term is
  viewed as its principal list (prins).  Om-vs-Th rule is arbitrary-but-total (Th<Om);
  it only affects the Om scaffolding, which the omfree op_NF image never uses.\<close>

fun prins :: "ot \<Rightarrow> ot list" where
  "prins (Su xs) = xs"
| "prins (Om m) = [Om m]"
| "prins (Th n a) = [Th n a]"

function (sequential) oltP :: "ot \<Rightarrow> ot \<Rightarrow> bool"
     and oltLs :: "ot list \<Rightarrow> ot list \<Rightarrow> bool" where
  "oltP (Om m) (Om n) = (m < n)"
| "oltP (Th m a) (Th n b) = (m < n \<or> (m = n \<and> oltLs (prins a) (prins b)))"
| "oltP (Th m a) (Om n) = True"
| "oltP (Om m) (Th n b) = False"
| "oltP _ _ = False"
| "oltLs [] ys = (ys \<noteq> [])"
| "oltLs (x # xs) [] = False"
| "oltLs (x # xs) (y # ys) = (oltP x y \<or> (x = y \<and> oltLs xs ys))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>x. case x of Inl (a,b) \<Rightarrow> size a + size b
                                       | Inr (xs,ys) \<Rightarrow> size_list size xs + size_list size ys)")
     (auto simp: size_list_estimation' dest!: less_imp_le)

definition oltL :: "ot \<Rightarrow> ot \<Rightarrow> bool" where
  "oltL a b = oltLs (prins a) (prins b)"

text \<open>Linearity of the principal order and the dictionary order, simultaneously.\<close>

lemma oltLs_neq: "oltP p q \<Longrightarrow> p \<noteq> q" "oltLs xs ys \<Longrightarrow> xs \<noteq> ys"
  by (induction p q and xs ys rule: oltP_oltLs.induct) auto

lemma oltLs_total:
  "oltP p q \<or> p = q \<or> oltP q p"
  "oltLs xs ys \<or> xs = ys \<or> oltLs ys xs"
  by (induction p q and xs ys rule: oltP_oltLs.induct) auto

lemma oltLs_trans:
  "oltP p q \<Longrightarrow> oltP q r \<Longrightarrow> oltP p r"
  "oltLs xs ys \<Longrightarrow> oltLs ys zs \<Longrightarrow> oltLs xs zs"
proof (induction p q and xs ys arbitrary: r and zs rule: oltP_oltLs.induct)
qed (auto elim: oltP.elims)

end
