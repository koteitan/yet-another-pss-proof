theory wflevel
  imports wo accinfra
begin

section \<open>Reducing well-foundedness to the principal terms\<close>

text \<open>
  The target is \<^prop>\<open>wf oltRw\<close>, well-foundedness of \<open><\<^sub>o\<close> on \<^emph>\<open>well-formed\<close> terms
  (\<^const>\<open>wfo\<close>; the image of the PSS embedding).  Equivalently, every well-formed
  term is \<open>oltRw\<close>-accessible.

  This theory performs the \<^emph>\<open>sum reduction\<close>: a well-formed term is accessible as
  soon as all its principal (\<open>\<Omega>\<close>/\<open>\<vartheta>\<close>) summands are.  Sums are compared by the
  Dershowitz\<dash>Manna multiset extension (\<^const>\<open>bag\<close>, @{const mult}), so
  accessibility of the summands lifts to the sum via the multiset infrastructure
  of \<^theory>\<open>YAPSS.accinfra\<close>.

  What remains after this theory is purely the \<^emph>\<open>principal core\<close> (Buchholz /
  Towsner Lemmas 3.10\<dash>3.12): every well-formed principal term is accessible.
\<close>

abbreviation oltRw :: "(ot \<times> ot) set" where
  "oltRw \<equiv> {(a, b). a <\<^sub>o b \<and> wfo a \<and> wfo b}"

subsection \<open>Well-formedness of critical subterms\<close>

text \<open>Critical subterms of a well-formed term are well-formed (and principal).\<close>

lemma wfo_Kn: "wfo a \<Longrightarrow> \<gamma> \<in> Kn n a \<Longrightarrow> wfo \<gamma>"
proof (induction a arbitrary: \<gamma>)
  case (Om m)
  have "\<gamma> = Om m" using Om.prems(2) by (auto split: if_splits)
  thus ?case by simp
next
  case (Th m a)
  show ?case
  proof (cases "n < m")
    case True
    with Th.prems have "\<gamma> \<in> Kn n a" by simp
    moreover have "wfo a" using Th.prems(1) by simp
    ultimately show ?thesis using Th.IH by blast
  next
    case False
    with Th.prems have "\<gamma> = Th m a" by simp
    thus ?thesis using Th.prems(1) by simp
  qed
next
  case (Su xs)
  then obtain x where "x \<in> set xs" "\<gamma> \<in> Kn n x" by auto
  moreover have "wfo x" using Su.prems(1) \<open>x \<in> set xs\<close> by auto
  ultimately show ?case using Su.IH by auto
qed

subsection \<open>The \<open>bag\<close> map sends \<open>oltRw\<close> into the multiset extension\<close>

text \<open>Elements of \<^term>\<open>bag a\<close> are well-formed principal summands of a
  well-formed \<open>a\<close>.\<close>

lemma bag_elem_wfo:
  assumes "wfo a" "x \<in># bag a" shows "wfo x \<and> isH x"
  using assms by (cases a) auto

text \<open>The analogue of @{thm [source] bag_mono} but landing in
  \<open>mult oltRw\<close> (so the summand witnesses carry \<^const>\<open>wfo\<close>).\<close>

lemma bag_mono_w:
  assumes "(a, b) \<in> oltRw"
  shows "(bag a, bag b) \<in> mult oltRw"
proof -
  have wa: "wfo a" and wb: "wfo b" and ab: "a <\<^sub>o b" using assms by auto
  from ab wa wb show ?thesis
  proof (cases a)
    case a_Su: (Su xs)
    show ?thesis
    proof (cases b)
      case b_Su: (Su ys)
      from \<open>a <\<^sub>o b\<close> a_Su b_Su obtain c
        where c: "c \<in># mset ys - mset xs"
          and dom: "\<forall>z \<in># mset xs - mset ys. z <\<^sub>o c" by auto
      let ?I = "mset xs \<inter># mset ys"
      have x: "mset xs = ?I + (mset xs - mset ys)" by (simp add: multiset_eq_iff min_def)
      have y: "mset ys = ?I + (mset ys - mset xs)" by (simp add: multiset_eq_iff min_def)
      have ne: "mset ys - mset xs \<noteq> {#}" using c by auto
      have "\<forall>k \<in># mset xs - mset ys. \<exists>j \<in># mset ys - mset xs. (k, j) \<in> oltRw"
      proof
        fix k assume k: "k \<in># mset xs - mset ys"
        hence "k \<in> set xs" by (meson in_diffD set_mset_mset in_multiset_in_set)
        with a_Su wa have "wfo k" by auto
        moreover have "c \<in> set ys" using c by (meson in_diffD set_mset_mset in_multiset_in_set)
        with b_Su wb have "wfo c" by auto
        moreover have "k <\<^sub>o c" using dom k by auto
        ultimately show "\<exists>j \<in># mset ys - mset xs. (k, j) \<in> oltRw" using c by auto
      qed
      hence "(?I + (mset xs - mset ys), ?I + (mset ys - mset xs)) \<in> mult oltRw"
        by (rule one_step_implies_mult[OF ne])
      thus ?thesis using a_Su b_Su x y by simp
    next
      case b_Om: (Om n)
      have "\<forall>k \<in># mset xs. (k, Om n) \<in> oltRw"
        using a_Su b_Om \<open>a <\<^sub>o b\<close> wa by auto
      hence "(mset xs, {# Om n #}) \<in> mult oltRw" by (rule mult_single_dom)
      thus ?thesis using a_Su b_Om by simp
    next
      case b_Th: (Th n d)
      have "\<forall>k \<in># mset xs. (k, Th n d) \<in> oltRw"
        using a_Su b_Th \<open>a <\<^sub>o b\<close> wa wb by auto
      hence "(mset xs, {# Th n d #}) \<in> mult oltRw" by (rule mult_single_dom)
      thus ?thesis using a_Su b_Th by simp
    qed
  next
    case a_pr: (Om m)
    show ?thesis
    proof (cases b)
      case (Su ys)
      from \<open>a <\<^sub>o b\<close> a_pr Su obtain z where z: "z \<in> set ys" and le: "a <\<^sub>o z \<or> a = z"
        using a_pr by auto
      show ?thesis
      proof (cases "a <\<^sub>o z")
        case True
        have "wfo z" using z Su wb by auto
        have "z \<in># mset ys" using z by simp
        moreover have "(a, z) \<in> oltRw" using True \<open>wfo z\<close> wa by auto
        ultimately have "({# a #}, mset ys) \<in> mult oltRw" by (rule mult_dom_set)
        thus ?thesis using a_pr Su by simp
      next
        case False
        with le have ay: "a = z" by simp
        have ain: "a \<in># mset ys" using z ay by simp
        have eq: "mset ys = {# a #} + (mset ys - {# a #})"
          using ain by (metis insert_DiffM add_mset_add_single add.commute)
        have "ys \<noteq> []" using z by auto
        hence "1 \<le> length ys" by (simp add: Suc_le_eq)
        moreover have "length ys \<noteq> 1" using Su wb by simp
        ultimately have "2 \<le> length ys" by linarith
        hence "1 \<le> size (mset ys - {# a #})" using ain by (simp add: size_Diff_singleton)
        hence ne: "mset ys - {# a #} \<noteq> {#}" by auto
        have "({# a #}, mset ys) \<in> mult oltRw"
          using mult_add[of "mset ys - {# a #}" "{# a #}" oltRw, OF ne] eq by simp
        thus ?thesis using a_pr Su by simp
      qed
    next
      case (Om n)
      hence "(a, b) \<in> oltRw" using a_pr \<open>a <\<^sub>o b\<close> by auto
      hence "({# a #}, {# b #}) \<in> mult oltRw" using mult_single_dom[of "{# a #}" b] by simp
      thus ?thesis using a_pr Om by simp
    next
      case (Th n d)
      hence "(a, b) \<in> oltRw" using a_pr \<open>a <\<^sub>o b\<close> wa wb by auto
      hence "({# a #}, {# b #}) \<in> mult oltRw" using mult_single_dom[of "{# a #}" b] by simp
      thus ?thesis using a_pr Th by simp
    qed
  next
    case a_pr: (Th m e)
    show ?thesis
    proof (cases b)
      case (Su ys)
      from \<open>a <\<^sub>o b\<close> a_pr Su obtain z where z: "z \<in> set ys" and le: "a <\<^sub>o z \<or> a = z"
        using a_pr by auto
      show ?thesis
      proof (cases "a <\<^sub>o z")
        case True
        have "wfo z" using z Su wb by auto
        have "z \<in># mset ys" using z by simp
        moreover have "(a, z) \<in> oltRw" using True \<open>wfo z\<close> wa by auto
        ultimately have "({# a #}, mset ys) \<in> mult oltRw" by (rule mult_dom_set)
        thus ?thesis using a_pr Su by simp
      next
        case False
        with le have ay: "a = z" by simp
        have ain: "a \<in># mset ys" using z ay by simp
        have eq: "mset ys = {# a #} + (mset ys - {# a #})"
          using ain by (metis insert_DiffM add_mset_add_single add.commute)
        have "ys \<noteq> []" using z by auto
        hence "1 \<le> length ys" by (simp add: Suc_le_eq)
        moreover have "length ys \<noteq> 1" using Su wb by simp
        ultimately have "2 \<le> length ys" by linarith
        hence "1 \<le> size (mset ys - {# a #})" using ain by (simp add: size_Diff_singleton)
        hence ne: "mset ys - {# a #} \<noteq> {#}" by auto
        have "({# a #}, mset ys) \<in> mult oltRw"
          using mult_add[of "mset ys - {# a #}" "{# a #}" oltRw, OF ne] eq by simp
        thus ?thesis using a_pr Su by simp
      qed
    next
      case (Om n)
      hence "(a, b) \<in> oltRw" using a_pr \<open>a <\<^sub>o b\<close> wa wb by auto
      hence "({# a #}, {# b #}) \<in> mult oltRw" using mult_single_dom[of "{# a #}" b] by simp
      thus ?thesis using a_pr Om by simp
    next
      case (Th n d)
      hence "(a, b) \<in> oltRw" using a_pr \<open>a <\<^sub>o b\<close> wa wb by auto
      hence "({# a #}, {# b #}) \<in> mult oltRw" using mult_single_dom[of "{# a #}" b] by simp
      thus ?thesis using a_pr Th by simp
    qed
  qed
qed

subsection \<open>Sum reduction: principals accessible \<open>\<Longrightarrow>\<close> all accessible\<close>

text \<open>If every well-formed principal term is \<open>oltRw\<close>-accessible, then so is every
  well-formed term.\<close>

theorem acc_oltRw_of_principals:
  assumes P: "\<And>p. wfo p \<Longrightarrow> isH p \<Longrightarrow> p \<in> Wellfounded.acc oltRw"
    and a: "wfo a"
  shows "a \<in> Wellfounded.acc oltRw"
proof -
  have bagacc: "bag a \<in> Wellfounded.acc (mult oltRw)"
  proof (rule acc_mult_of_elems)
    fix x assume "x \<in># bag a"
    with bag_elem_wfo[OF a] have "wfo x" "isH x" by auto
    thus "x \<in> Wellfounded.acc oltRw" by (rule P)
  qed
  show "a \<in> Wellfounded.acc oltRw"
  proof (rule acc_pullback[where R = oltRw and S = "mult oltRw" and f = bag])
    fix p q assume "(p, q) \<in> oltRw"
    thus "(bag p, bag q) \<in> mult oltRw" by (rule bag_mono_w)
  next
    show "bag a \<in> Wellfounded.acc (mult oltRw)" by (rule bagacc)
  qed
qed

text \<open>Consequently, \<^prop>\<open>wf oltRw\<close> follows from accessibility of the principals.\<close>

theorem wf_oltRw_of_principals:
  assumes "\<And>p. wfo p \<Longrightarrow> isH p \<Longrightarrow> p \<in> Wellfounded.acc oltRw"
  shows "wf oltRw"
proof (subst wf_iff_acc, intro allI)
  fix a show "a \<in> Wellfounded.acc oltRw"
  proof (cases "wfo a")
    case True
    show ?thesis by (rule acc_oltRw_of_principals[OF assms True])
  next
    case False
    have "\<And>y. (y, a) \<in> oltRw \<Longrightarrow> y \<in> Wellfounded.acc oltRw" using False by auto
    thus ?thesis by (rule accI)
  qed
qed

end
