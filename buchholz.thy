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

end
