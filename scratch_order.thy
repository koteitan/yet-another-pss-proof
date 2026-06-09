theory scratch_order
  imports Main
begin

text \<open>Validate the Buchholz-standard order design (A2): dictionary order on tuples,
  lex on principals, NO critical-subterm domination in the comparison.
  Confirm linearity (irrefl, trans, totality) is straightforward.\<close>

datatype bt = Trm "bp list" and bp = Thb int bt

fun lessT :: "bt \<Rightarrow> bt \<Rightarrow> bool" and lessP :: "bp \<Rightarrow> bp \<Rightarrow> bool" where
  "lessT (Trm []) (Trm bs) = (bs \<noteq> [])"
| "lessT (Trm (a # as)) (Trm []) = False"
| "lessT (Trm (a # as)) (Trm (b # bs)) =
     (lessP a b \<or> (a = b \<and> lessT (Trm as) (Trm bs)))"
| "lessP (Thb u a) (Thb v b) = (u < v \<or> (u = v \<and> lessT a b))"

lemma less_neq: "lessT a b \<Longrightarrow> a \<noteq> b" "lessP p q \<Longrightarrow> p \<noteq> q"
  by (induction a b and p q rule: lessT_lessP.induct) auto

lemma less_irrefl: "\<not> lessT a a" "\<not> lessP p p"
  using less_neq by auto

lemma less_total:
  "lessT a b \<or> a = b \<or> lessT b a"
  "lessP p q \<or> p = q \<or> lessP q p"
  by (induction a b and p q rule: lessT_lessP.induct) auto

lemma less_trans:
  "lessT a b \<Longrightarrow> lessT b c \<Longrightarrow> lessT a c"
  "lessP p q \<Longrightarrow> lessP q r \<Longrightarrow> lessP p r"
proof (induction a b and p q arbitrary: c and r rule: lessT_lessP.induct)
  case (1 bs) then show ?case by (cases c; cases bs) auto
next
  case (2 a as) then show ?case by simp
next
  case (3 a as b bs)
  then show ?case
  proof (cases c)
    case (Trm cs) with 3 show ?thesis by (cases cs) auto
  qed
next
  case (4 u a v b) then show ?case by (cases r) auto
qed

end
