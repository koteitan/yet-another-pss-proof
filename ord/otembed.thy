theory otembed
  imports psi "YAPSS.proofs"
begin

text \<open>\<^bold>\<open>The order embedding \<open>o : three \<Rightarrow> V\<close>\<close> (Buchholz \<section>2) and the resulting
  well-foundedness of \<open>olt\<close> on the standard-form image \<open>NF\<close>, which discharges the
  last hypothesis of \<open>proofs\<close>'s \<open>step_terminates\<close>.

  \<open>three\<close> (from \<open>mechanized\<close>, HOL side) and \<open>V\<close> (from \<open>psi\<close>, ZFC-in-HOL side)
  coexist here.  Note: the infix \<open><o\<close> is ambiguous in this merged context
  (\<open>mechanized.olt\<close> vs HOL's \<open>ordLess2\<close>), so we always write \<open>olt\<close> explicitly.

  \<open>P a b c\<close> is Buchholz's \<open>D\<^bsub>a\<^esub>(b) + c\<close>, so \<open>o (P a b c) = \<psi>\<^bsub>a\<^esub>(o b) + o c\<close>
  and \<open>o Z = 0\<close>.\<close>

fun oV :: "three \<Rightarrow> V" where
  "oV Z = 0"
| "oV (P a b c) = psi (oV b) a + oV c"

lemma Ord_oV [simp, intro]: "Ord (oV t)"
  by (induction t) (auto simp: Ord_add)

subsection \<open>Order preservation on the standard-form image (Buchholz Lemma 2.2(c))\<close>

text \<open>\<^bold>\<open>Residual obligation\<close> (the genuine Buchholz-level core): the embedding is
  strictly monotone on \<open>NF = translate ` ST_PS\<close>.  To be proved from \<section>1
  (\<open>\<psi>\<^sub>v\<close> additive-principal 1.2(b), the bound 1.2(c) \<open>psi_lt_Om_Suc\<close>, and strict
  monotonicity 1.3 \<open>psi_strict_mono_arg\<close>) together with the standard-form
  (Buchholz OT) well-formedness of \<open>translate ` ST_PS\<close>.\<close>

lemma oV_order_pres_NF:
  assumes "u \<in> NF" "v \<in> NF" "olt v u"
  shows "oV v < oV u"
  sorry

subsection \<open>Well-foundedness of \<open>olt\<close> on \<open>NF\<close>, and PSS termination\<close>

theorem wf_Rnf: "wf {(v,u). olt v u \<and> u \<in> NF \<and> v \<in> NF}"
proof (rule wf_subset[OF wf_inv_image[OF wf_VWF, of oV]])
  show "{(v,u). olt v u \<and> u \<in> NF \<and> v \<in> NF} \<subseteq> inv_image VWF oV"
  proof (rule subrelI)
    fix v u assume "(v,u) \<in> {(v,u). olt v u \<and> u \<in> NF \<and> v \<in> NF}"
    then have "olt v u" "u \<in> NF" "v \<in> NF" by auto
    then have "oV v < oV u" using oV_order_pres_NF by blast
    thus "(v,u) \<in> inv_image VWF oV"
      by (simp add: inv_image_def VWF_iff_Ord_less)
  qed
qed

theorem PSS_terminates: "wf {(T,M). M \<in> ST_PS \<and> step M T}"
  by (rule step_terminates[OF wf_Rnf])

end
