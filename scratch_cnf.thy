theory scratch_cnf
  imports wo
begin

text \<open>Minimal A2: a "cnf" (normal-form) predicate on ot — hereditarily, every Su
  list is non-increasing wrt <o (and well-formed).  On cnf terms the multiset
  single-dominator Su-order coincides with the dictionary order, so linearity
  (totality, asymmetry, transitivity) holds and is tractable.  This unblocks
  op_NF (embed images are cnf) without changing the order or the WF reduction.\<close>

fun cnfo :: "ot \<Rightarrow> bool" where
  "cnfo (Om n) = True"
| "cnfo (Th n a) = cnfo a"
| "cnfo (Su xs) = (length xs \<noteq> 1 \<and> (\<forall>x \<in> set xs. isH x \<and> cnfo x)
                    \<and> sorted_wrt (\<lambda>x y. y <\<^sub>o x \<or> y = x) xs)"

lemma cnfo_imp_wfo: "cnfo a \<Longrightarrow> wfo a"
  by (induction a) auto

text \<open>Totality of \<open><\<^sub>o\<close> on cnf terms.  (First milestone toward cnf-linearity.)\<close>

lemma cnfo_total: "cnfo a \<Longrightarrow> cnfo b \<Longrightarrow> a <\<^sub>o b \<or> a = b \<or> b <\<^sub>o a"
proof (induction "size a + size b" arbitrary: a b rule: less_induct)
  case less
  show ?case sorry
qed

end
