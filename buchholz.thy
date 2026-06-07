theory buchholz
  imports wflevel
begin

section \<open>The Buchholz well-foundedness core: \<open>wf pR\<close> via distinguished sets\<close>

text \<open>
  \<^bold>\<open>Under reconstruction (2026-06-08).\<close>  The previous content stratified the
  distinguished sets by the \<^emph>\<open>top\<close> cardinality \<^const>\<open>FC\<close>; that stratification was
  found to be unprovable (it concentrates the entire difficulty at level \<open>0\<close> with no
  inductive help, see \<^file>\<open>memo.md\<close>).  Following Towsner \<^emph>\<open>Polymorphic Ordinal
  Notations\<close> \<section>3.2 (transcribed to the absolute system with \<^typ>\<open>int\<close> levels), the
  well-foundedness proof is being rebuilt to stratify by the \<^emph>\<open>ground\<close>
  \<open>G(\<alpha>) = min (FCset \<alpha>)\<close> (Def 3.6\<dash>3.7), with an explicit shift on the cardinal
  levels (Def 3.3) needed to discharge the cross-subscript predecessor case
  (\<open>\<vartheta>\<^bsub>p\<^esub> e <\<^sub>o \<vartheta>\<^bsub>s\<^esub> d\<close> with \<open>p < s\<close>).

  The reduction \<^prop>\<open>wf pR \<Longrightarrow> wf oltRw\<close> (\<^theory>\<open>YAPSS.wflevel\<close>) and the generic
  accessibility infrastructure (\<^theory>\<open>YAPSS.accinfra\<close>) are unaffected and reused.
\<close>

subsection \<open>The shift is an automorphism of the order on well-formed terms\<close>

text \<open>Since \<^const>\<open>shift\<close> preserves both \<open><\<^sub>o\<close> (@{thm [source] shift_olt}) and
  \<^const>\<open>wfo\<close> (@{thm [source] shift_wfo}), it is an automorphism of \<^const>\<open>oltRw\<close>;
  hence accessibility is invariant under shifting.  This is what makes the
  ground-normalization legitimate.\<close>

lemma shift_oltRw [simp]: "((shift k a, shift k b) \<in> oltRw) = ((a, b) \<in> oltRw)"
  by simp

lemma acc_shift_aux: "a \<in> Wellfounded.acc oltRw \<Longrightarrow> shift k a \<in> Wellfounded.acc oltRw"
proof (induction set: Wellfounded.acc)
  case (1 a)
  show ?case
  proof (rule accI)
    fix y assume y: "(y, shift k a) \<in> oltRw"
    have "(shift k (shift (- k) y), shift k a) \<in> oltRw" using y by simp
    hence "(shift (- k) y, a) \<in> oltRw" by (simp only: shift_oltRw)
    hence "shift k (shift (- k) y) \<in> Wellfounded.acc oltRw" using "1.IH" by blast
    thus "y \<in> Wellfounded.acc oltRw" by simp
  qed
qed

lemma acc_shift [simp]: "(shift k a \<in> Wellfounded.acc oltRw) = (a \<in> Wellfounded.acc oltRw)"
proof
  assume "shift k a \<in> Wellfounded.acc oltRw"
  from acc_shift_aux[OF this, of "- k"] show "a \<in> Wellfounded.acc oltRw" by simp
next
  assume "a \<in> Wellfounded.acc oltRw"
  thus "shift k a \<in> Wellfounded.acc oltRw" by (rule acc_shift_aux)
qed

subsection \<open>Generic accessible part of a set under \<open><\<^sub>o\<close>\<close>

text \<open>\<open>Awf S\<close> is the \<open><\<^sub>o\<close>-accessible part of \<open>S\<close> (relative to the order restricted
  to \<open>S\<close>).  Independent of any particular stratification; reused for the
  distinguished sets below.\<close>

definition Awf :: "ot set \<Rightarrow> ot set" where
  "Awf S = S \<inter> Wellfounded.acc {(x, y). x <\<^sub>o y \<and> x \<in> S \<and> y \<in> S}"

lemma Awf_subset: "Awf S \<subseteq> S"
  by (auto simp: Awf_def)

lemma Awf_acc:
  "a \<in> Awf S \<Longrightarrow> a \<in> Wellfounded.acc {(x, y). x <\<^sub>o y \<and> x \<in> S \<and> y \<in> S}"
  by (simp add: Awf_def)

text \<open>The order restricted to \<^term>\<open>Awf S\<close> is well-founded.\<close>

lemma wf_on_Awf:
  "wf {(x, y). x <\<^sub>o y \<and> x \<in> Awf S \<and> y \<in> Awf S}"
proof -
  have sub: "{(x, y). x <\<^sub>o y \<and> x \<in> Awf S \<and> y \<in> Awf S}
             \<subseteq> {(x, y). x <\<^sub>o y \<and> x \<in> S \<and> y \<in> S}"
    by (auto simp: Awf_def)
  have "\<And>x. x \<in> Wellfounded.acc {(x, y). x <\<^sub>o y \<and> x \<in> Awf S \<and> y \<in> Awf S}"
  proof -
    fix x
    show "x \<in> Wellfounded.acc {(x, y). x <\<^sub>o y \<and> x \<in> Awf S \<and> y \<in> Awf S}"
    proof (cases "x \<in> Awf S")
      case True
      hence "x \<in> Wellfounded.acc {(x, y). x <\<^sub>o y \<and> x \<in> S \<and> y \<in> S}" by (rule Awf_acc)
      thus ?thesis using acc_subset[OF sub] by (rule rev_subsetD)
    next
      case False
      hence "\<And>y. (y, x) \<in> {(x, y). x <\<^sub>o y \<and> x \<in> Awf S \<and> y \<in> Awf S}
              \<Longrightarrow> y \<in> Wellfounded.acc {(x, y). x <\<^sub>o y \<and> x \<in> Awf S \<and> y \<in> Awf S}"
        by auto
      thus ?thesis by (rule accI)
    qed
  qed
  thus ?thesis by (subst wf_iff_acc) blast
qed

end
