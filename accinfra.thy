theory accinfra
  imports "HOL-Library.Multiset"
begin

section \<open>Generic accessibility infrastructure\<close>

text \<open>
  Reusable, problem-independent facts about @{const Wellfounded.acc} that the
  Buchholz well-foundedness proof relies on:
  \<^item> accessibility is stable under transitive closure;
  \<^item> accessibility pulls back along a monotone map;
  \<^item> the one-step multiset order is accessible at a multiset all of whose
    elements are accessible (the \<^emph>\<open>elementwise\<close> version of
    @{thm [source] all_accessible}, which assumes the whole relation is
    well-founded).
\<close>

subsection \<open>Accessibility and transitive closure\<close>

lemma acc_imp_acc_trancl:
  assumes "x \<in> Wellfounded.acc r"
  shows "x \<in> Wellfounded.acc (r\<^sup>+)"
  using assms
proof (induction set: Wellfounded.acc)
  case (1 x)
  show ?case
  proof (rule accI)
    fix z assume zx: "(z, x) \<in> r\<^sup>+"
    from zx obtain c where cx: "(c, x) \<in> r" and zc: "(z, c) \<in> r\<^sup>+ \<or> z = c"
      by (metis tranclE)
    from cx have "c \<in> Wellfounded.acc (r\<^sup>+)" using 1 by blast
    thus "z \<in> Wellfounded.acc (r\<^sup>+)" using zc by (metis acc_downward)
  qed
qed

subsection \<open>Accessibility along a monotone map\<close>

text \<open>If \<open>f\<close> maps \<open>R\<close>-edges to \<open>S\<close>-edges and \<open>f a\<close> is \<open>S\<close>-accessible, then \<open>a\<close>
  is \<open>R\<close>-accessible.\<close>

lemma acc_pullback:
  assumes mono: "\<And>p q. (p, q) \<in> R \<Longrightarrow> (f p, f q) \<in> S"
    and z: "f a \<in> Wellfounded.acc S"
  shows "a \<in> Wellfounded.acc R"
proof -
  have gen: "\<forall>a. f a = y \<longrightarrow> a \<in> Wellfounded.acc R" if "y \<in> Wellfounded.acc S" for y
    using that
  proof (induction set: Wellfounded.acc)
    case (1 y)
    show ?case
    proof (intro allI impI)
      fix a assume fa: "f a = y"
      show "a \<in> Wellfounded.acc R"
      proof (rule accI)
        fix b assume "(b, a) \<in> R"
        hence "(f b, f a) \<in> S" by (rule mono)
        hence "(f b, y) \<in> S" using fa by simp
        thus "b \<in> Wellfounded.acc R" using 1 by blast
      qed
    qed
  qed
  from gen[OF z] show ?thesis by blast
qed

subsection \<open>Elementwise multiset accessibility\<close>

text \<open>The single-element building block of @{thm [source] all_accessible}, with the
  global \<open>wf r\<close> replaced by accessibility of the element being added.\<close>

lemma acc_add_mset:
  assumes a: "a \<in> Wellfounded.acc r"
    and N: "N \<in> Wellfounded.acc (mult1 r)"
  shows "add_mset a N \<in> Wellfounded.acc (mult1 r)"
proof -
  let ?R = "mult1 r"
  let ?W = "Wellfounded.acc ?R"
  have tedious: "add_mset a M0 \<in> ?W"
    if M0: "M0 \<in> ?W"
      and wf_hyp: "\<And>b. (b, a) \<in> r \<Longrightarrow> (\<forall>M \<in> ?W. add_mset b M \<in> ?W)"
      and acc_hyp: "\<And>M. (M, M0) \<in> ?R \<Longrightarrow> add_mset a M \<in> ?W"
    for a M0
  proof (rule accI)
    fix N assume "(N, add_mset a M0) \<in> ?R"
    then consider M where "(M, M0) \<in> ?R" "N = add_mset a M"
      | K where "\<forall>b. b \<in># K \<longrightarrow> (b, a) \<in> r" "N = M0 + K"
      by atomize_elim (rule less_add)
    thus "N \<in> ?W"
    proof cases
      case 1
      from acc_hyp[OF 1(1)] show "N \<in> ?W" by (simp only: 1(2))
    next
      case 2
      from 2(1) have "M0 + K \<in> ?W"
      proof (induct K)
        case empty
        from M0 show ?case by simp
      next
        case (add x K)
        from add.prems have "(x, a) \<in> r" by simp
        with wf_hyp have "\<forall>M \<in> ?W. add_mset x M \<in> ?W" by blast
        moreover from add have "M0 + K \<in> ?W" by simp
        ultimately have "add_mset x (M0 + K) \<in> ?W" ..
        thus ?case by simp
      qed
      thus "N \<in> ?W" by (simp only: 2(2))
    qed
  qed
  from a have "\<forall>M \<in> ?W. add_mset a M \<in> ?W"
  proof (induction set: Wellfounded.acc)
    case (1 a)
    have wf_hyp: "\<And>b. (b, a) \<in> r \<Longrightarrow> (\<forall>M \<in> ?W. add_mset b M \<in> ?W)" using 1 by blast
    show ?case
    proof
      fix M assume "M \<in> ?W"
      thus "add_mset a M \<in> ?W"
      proof (induction set: Wellfounded.acc)
        case (1 M)
        have accm: "M \<in> ?W" using 1 by (blast intro: accI)
        have acc_hyp: "\<And>M'. (M', M) \<in> ?R \<Longrightarrow> add_mset a M' \<in> ?W" using 1 by blast
        show ?case by (rule tedious[OF accm wf_hyp acc_hyp])
      qed
    qed
  qed
  with N show ?thesis by blast
qed

lemma acc_mult1_of_elems:
  assumes "\<And>x. x \<in># M \<Longrightarrow> x \<in> Wellfounded.acc r"
  shows "M \<in> Wellfounded.acc (mult1 r)"
  using assms
proof (induction M)
  case empty
  show ?case
  proof (rule accI)
    fix b assume "(b, {#}) \<in> mult1 r"
    thus "b \<in> Wellfounded.acc (mult1 r)" using not_less_empty by blast
  qed
next
  case (add a M)
  have "a \<in> Wellfounded.acc r" using add.prems by simp
  moreover have "M \<in> Wellfounded.acc (mult1 r)" using add.IH add.prems by simp
  ultimately show ?case by (rule acc_add_mset)
qed

lemma acc_mult_of_elems:
  assumes "\<And>x. x \<in># M \<Longrightarrow> x \<in> Wellfounded.acc r"
  shows "M \<in> Wellfounded.acc (mult r)"
  unfolding mult_def
  by (rule acc_imp_acc_trancl[OF acc_mult1_of_elems[OF assms]])

end
