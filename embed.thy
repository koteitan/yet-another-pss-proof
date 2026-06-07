theory embed
  imports wf wo
begin

section \<open>Embedding the PSS notation into the well-foundedness core\<close>

text \<open>
  The PSS notation \<^typ>\<open>three\<close> (\<open>p\<^sub>a(b)+c\<close>, with the naive subscript-first order
  \<open>olt\<close> = \<open><o\<close> from \<^theory>\<open>YAPSS.mechanized\<close>) is mapped into Towsner's well-founded
  ordinal terms \<^typ>\<open>ot\<close> (\<^theory>\<open>YAPSS.wo\<close>) by reading each principal \<open>p\<^sub>a(b)\<close> as the
  collapsing term \<open>\<vartheta>\<^sub>a b\<close> (\<^const>\<open>Th\<close>) and the \<open>+\<close>-chain as the natural sum
  (\<^const>\<open>Su\<close>).

  A subtlety: Towsner's sums must have length \<open>\<noteq> 1\<close> (a lone principal is \<^emph>\<open>not\<close>
  written as a sum, and indeed \<open>Su [x] \<noteq> x\<close> under \<open><\<^sub>o\<close>).  So \<open>collapse\<close> turns the
  list of principal summands into \<open>Zero\<close> (empty), the bare principal (singleton),
  or a genuine \<open>Su\<close> (length \<open>\<ge> 2\<close>).  This makes the image well-formed (\<^const>\<open>wfo\<close>).

  The plan: prove this map is order-preserving on \<open>NF\<close> (where the naive order
  coincides with the true collapsing order), so well-foundedness of \<open><\<^sub>o\<close>
  transfers to \<open>NF\<close>, discharging the diagonal accessibility obligation.
\<close>

definition collapse :: "ot list \<Rightarrow> ot" where
  "collapse xs = (case xs of [] \<Rightarrow> Su [] | [x] \<Rightarrow> x | _ \<Rightarrow> Su xs)"

lemma collapse_Nil [simp]: "collapse [] = Su []"
  by (simp add: collapse_def)

lemma collapse_single [simp]: "collapse [x] = x"
  by (simp add: collapse_def)

lemma collapse_cons2 [simp]: "collapse (x # y # ys) = Su (x # y # ys)"
  by (simp add: collapse_def)

text \<open>\<open>eprincs t\<close> is the list of principal summands of \<open>t\<close>; \<open>embed t\<close> collapses it.\<close>

fun eprincs :: "three \<Rightarrow> ot list" where
  "eprincs Z = []"
| "eprincs (P a b c) = Th a (collapse (eprincs b)) # eprincs c"

definition embed :: "three \<Rightarrow> ot" where
  "embed t = collapse (eprincs t)"

lemma embed_Z [simp]: "embed Z = Zero"
  by (simp add: embed_def)

lemma eprincs_P [simp]:
  "eprincs (P a b c) = Th a (embed b) # eprincs c"
  by (simp add: embed_def)

text \<open>\<open>collapse\<close> of a list of well-formed principals is well-formed.\<close>

lemma wfo_collapse:
  assumes "\<forall>x \<in> set xs. isH x \<and> wfo x" shows "wfo (collapse xs)"
proof (cases xs)
  case Nil thus ?thesis by simp
next
  case (Cons x ys)
  show ?thesis
  proof (cases ys)
    case Nil thus ?thesis using Cons assms by simp
  next
    case (Cons y zs) thus ?thesis using \<open>xs = x # ys\<close> assms by auto
  qed
qed

text \<open>Every summand produced by the embedding is a principal \<vartheta>-term whose
  argument is itself a well-formed image; hence the image is well-formed.\<close>

lemma eprincs_props: "x \<in> set (eprincs t) \<Longrightarrow> isH x \<and> wfo x"
proof (induction t arbitrary: x)
  case (P a b c)
  from P.prems consider "x = Th a (embed b)" | "x \<in> set (eprincs c)"
    by (auto simp: embed_def)
  thus ?case
  proof cases
    case 1
    have "\<forall>y \<in> set (eprincs b). isH y \<and> wfo y" using P.IH(1) by blast
    hence "wfo (embed b)" unfolding embed_def by (rule wfo_collapse)
    thus ?thesis using 1 by simp
  next
    case 2
    show ?thesis by (rule P.IH(2)[OF 2])
  qed
qed simp

lemma wfo_embed: "wfo (embed t)"
  unfolding embed_def by (rule wfo_collapse) (use eprincs_props in auto)

end
