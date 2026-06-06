theory proofs
  imports mechanized
begin

text \<open>
  Top-level termination of the Pair Sequence System.
  (File named \<open>proofs.thy\<close> rather than \<open>proof.thy\<close>: \<open>proof\<close> is an Isabelle
  keyword and cannot be a theory name.)

  Termination — no infinite expansion chain on the standard form
  \<open>ST_PS\<close> — is reduced rigorously to two facts about the \<open>p_a(b)+c\<close>
  measure \<open>translate\<close>:
    \<^item> \<open>dec\<close>: each expansion step strictly decreases \<open>translate\<close> (the genuine
      bad-branch case of @{thm [source] translate_oper_pred}'s sibling, still
      open; the Pred branches are done);
    \<^item> \<open>wfimg\<close>: the subscript-first order \<open><o\<close> is well-founded on the image
      \<open>translate ` ST_PS\<close> (the Buchholz-level core, still open).

  Both are stated as explicit hypotheses of @{text step_terminates_cond}: the
  theorem is the architecture, the hypotheses are exactly what remains.
\<close>

abbreviation NF :: "ord set" where
  "NF \<equiv> translate ` ST_PS"

text \<open>The expansion step lands inside \<open>ST_PS\<close> and inside \<open>NF\<close>.\<close>

lemma step_in_ST_PS:
  assumes "M \<in> ST_PS" and "step M T"
  shows "T \<in> ST_PS"
proof -
  from \<open>step M T\<close> obtain n where n: "1 \<le> n" and TM: "T = M[n]"
    by (auto elim: step.cases)
  show ?thesis using ST_PS.oper[OF \<open>M \<in> ST_PS\<close> n] TM by simp
qed

text \<open>Conditional termination: decrease + well-foundedness on the image give
  well-foundedness of the one-step relation on \<open>ST_PS\<close>.\<close>

theorem step_terminates_cond:
  assumes dec: "\<And>M n. M \<in> ST_PS \<Longrightarrow> 1 < Lng M \<Longrightarrow> 1 \<le> n \<Longrightarrow> translate (M[n]) <o translate M"
    and wfimg: "wf {(v,u). v <o u \<and> u \<in> NF \<and> v \<in> NF}"
  shows "wf {(T,M). M \<in> ST_PS \<and> step M T}"
proof (rule wf_subset)
  show "wf (inv_image {(v,u). v <o u \<and> u \<in> NF \<and> v \<in> NF} translate)"
    by (rule wf_inv_image[OF wfimg])
next
  show "{(T,M). M \<in> ST_PS \<and> step M T}
          \<subseteq> inv_image {(v,u). v <o u \<and> u \<in> NF \<and> v \<in> NF} translate"
  proof (rule subrelI)
    fix T M assume "(T,M) \<in> {(T,M). M \<in> ST_PS \<and> step M T}"
    then have M: "M \<in> ST_PS" and st: "step M T" by auto
    from st obtain n where L: "1 < Lng M" and n: "1 \<le> n" and TM: "T = M[n]"
      by (auto elim!: step.cases)
    have T: "T \<in> ST_PS" using M st by (rule step_in_ST_PS)
    have "translate T <o translate M" using dec[OF M L n] TM by simp
    moreover have "translate M \<in> NF" using M by simp
    moreover have "translate T \<in> NF" using T by simp
    ultimately show "(T,M) \<in> inv_image {(v,u). v <o u \<and> u \<in> NF \<and> v \<in> NF} translate"
      by (simp add: inv_image_def)
  qed
qed

text \<open>Equivalent phrasing: there is no infinite expansion sequence within
  \<open>ST_PS\<close>.\<close>

corollary no_infinite_expansion_cond:
  assumes dec: "\<And>M n. M \<in> ST_PS \<Longrightarrow> 1 < Lng M \<Longrightarrow> 1 \<le> n \<Longrightarrow> translate (M[n]) <o translate M"
    and wfimg: "wf {(v,u). v <o u \<and> u \<in> NF \<and> v \<in> NF}"
  shows "\<not> (\<exists>S. (\<forall>i. S i \<in> ST_PS) \<and> (\<forall>i. step (S i) (S (Suc i))))"
proof
  assume "\<exists>S. (\<forall>i. S i \<in> ST_PS) \<and> (\<forall>i. step (S i) (S (Suc i)))"
  then obtain S where S: "\<And>i. S i \<in> ST_PS" and stp: "\<And>i. step (S i) (S (Suc i))" by auto
  let ?R = "{(T,M). M \<in> ST_PS \<and> step M T}"
  have wf: "wf ?R" by (rule step_terminates_cond[OF dec wfimg])
  have chain: "\<forall>i. (S (Suc i), S i) \<in> ?R" using S stp by auto
  from wf have "\<not> (\<exists>f. \<forall>i. (f (Suc i), f i) \<in> ?R)"
    by (simp add: wf_iff_no_infinite_down_chain)
  with chain show False by blast
qed

end
