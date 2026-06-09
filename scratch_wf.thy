theory scratch_wf
  imports buchholz
begin

text \<open>\<^bold>\<open>Multi-\<open>\<vartheta>\<^sub>n\<close> well-foundedness, corrected hierarchy (memo 続38\<dash>39).\<close>

  The previous \<^const>\<open>Mn\<close>/\<^const>\<open>AccB\<close>/\<^const>\<open>Acc\<close> stratified by \<^const>\<open>gnd\<close>, which
  uses the convention \<open>FCset = {} \<Longrightarrow> 0\<close>.  That collapses Towsner's countable
  base level \<open>-\<infinity>\<close> into level \<open>0\<close> (\<open>\<Omega>\<^sub>0\<close>), making the hierarchy \<^emph>\<open>degenerate on the
  \<open>\<Omega>\<close>-free fragment\<close> (every \<open>\<Omega>\<close>-free term lands at level \<open>0\<close> with only \<open>K\<^sub>0\<close> control,
  no real stratification).

  Here we keep the countable terms (\<open>FCset = {}\<close>) as a genuine separate base
  \<^const>\<open>cntbl\<close> (Towsner \<open>M\<^bsub>-\<infinity>\<^esub>\<close>), and stratify the \<^emph>\<open>cardinal\<close> terms by the ground.

  This is a development scratch (not in \<^file>\<open>ROOT\<close>); the hard closure lemmas
  (Towsner 3.8\<dash>3.12, multi-\<open>\<vartheta>\<^sub>n\<close>) are built incrementally and verified by build
  before integration into \<^theory>\<open>YAPSS.buchholz\<close>.\<close>

subsection \<open>The countable base (Towsner \<open>M\<^bsub>-\<infinity>\<^esub>\<close>)\<close>

text \<open>\<open>cntbl a\<close>: no free cardinal occurs (\<open>FCset a = {}\<close>).  This is broader than
  \<^const>\<open>omfree\<close> (e.g. \<open>\<vartheta>\<^bsub>3\<^esub> \<Omega>\<^bsub>5\<^esub>\<close> is countable but not \<open>\<Omega>\<close>-free), but on the
  \<^emph>\<open>well-formed nonnegative\<close> target the two coincide on the embedding image.\<close>

definition cntbl :: "ot \<Rightarrow> bool" where
  "cntbl a \<longleftrightarrow> FCset a = {}"

lemma cntbl_omfree: "omfree a \<Longrightarrow> cntbl a"
  by (simp add: cntbl_def)

lemma cntbl_Su_iff: "cntbl (Su xs) \<longleftrightarrow> (\<forall>x \<in> set xs. cntbl x)"
  by (auto simp: cntbl_def)

lemma cntbl_Th: "cntbl (Th n a) \<longleftrightarrow> {m \<in> FCset a. m < n} = {}"
  by (simp add: cntbl_def)

text \<open>The countable base set and its accessible part (Towsner \<open>Acc\<^bsub>-\<infinity>\<^esub>\<close>).\<close>

definition Mbot :: "ot set" where
  "Mbot = {a. wfo a \<and> nneg a \<and> omfree a}"

text \<open>The order restricted to \<^const>\<open>Mbot\<close> is exactly \<^const>\<open>oltRwF\<close>: \<^const>\<open>omfree\<close> is
  preserved downward, so the accessible part of the base \<^emph>\<open>is\<close> the genuine
  accessibility we want.  (The base level alone is therefore tautological; the
  well-foundedness content lives in the \<open>\<Omega>\<close>-scaffolded higher levels and the
  master/closure lemmas that place every \<open>\<Omega>\<close>-free term into the base.)\<close>

lemma R_Mbot_eq_oltRwF: "{(x,y). x <\<^sub>o y \<and> x \<in> Mbot \<and> y \<in> Mbot} = oltRwF"
  by (auto simp: Mbot_def)

lemma Abot_subset_acc: "Awf Mbot \<subseteq> Wellfounded.acc oltRwF"
  using Awf_acc by (auto simp: Awf_def R_Mbot_eq_oltRwF)

subsection \<open>Sanity: the base reduction is tautological (documents the gap)\<close>

text \<open>Membership \<open>a \<in> Awf Mbot\<close> is \<^emph>\<open>equivalent\<close> to \<open>a \<in> acc oltRwF\<close> for \<open>\<Omega>\<close>-free
  \<open>a\<close> \<dash> so the base gives no new accessibility.  This makes precise why the
  hard work cannot be avoided at the base level.\<close>

lemma Abot_iff_acc:
  assumes "wfo a" "nneg a" "omfree a"
  shows "a \<in> Awf Mbot \<longleftrightarrow> a \<in> Wellfounded.acc oltRwF"
proof
  assume "a \<in> Awf Mbot" thus "a \<in> Wellfounded.acc oltRwF" using Abot_subset_acc by blast
next
  assume acc: "a \<in> Wellfounded.acc oltRwF"
  have "a \<in> Mbot" using assms by (simp add: Mbot_def)
  moreover have "a \<in> Wellfounded.acc {(x,y). x <\<^sub>o y \<and> x \<in> Mbot \<and> y \<in> Mbot}"
    using acc by (simp add: R_Mbot_eq_oltRwF)
  ultimately show "a \<in> Awf Mbot" by (simp add: Awf_def)
qed

end
