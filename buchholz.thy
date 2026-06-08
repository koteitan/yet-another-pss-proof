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

subsection \<open>The ground-stratified distinguished sets (Towsner Def 3.7, absolute)\<close>

text \<open>A term is \<^emph>\<open>normalized\<close> when its top cardinal sits at \<open>0\<close> (or it is countable,
  \<open>FCset = {}\<close>).  \<^const>\<open>norm\<close> maps any term to a normalized one (order-equivalently
  for accessibility, by @{thm [source] acc_shift}).  \<open>Klt a\<close> is the set of critical
  subterms strictly below \<open>\<Omega>\<^bsub>0\<^esub>\<close> (Towsner \<open>K\<^bsup><0\<^esup>\<close>).\<close>

definition normd :: "ot \<Rightarrow> bool" where
  "normd a \<longleftrightarrow> (FCset a = {} \<or> FC a = 0)"

definition Klt :: "ot \<Rightarrow> ot set" where
  "Klt a = {\<gamma>. \<gamma> \<in> Kn 0 a \<and> \<gamma> <\<^sub>o Om 0}"

text \<open>\<open>Mn n prev\<close>: normalized well-formed principals of \<^emph>\<open>width\<close> \<open>\<le> n\<close> (ground
  \<open>\<ge> -n\<close>) whose below-\<open>\<Omega>\<^bsub>0\<^esub>\<close> critical subterms normalize into the lower levels
  \<open>prev\<close>.  \<open>Acc n\<close> is its \<open><\<^sub>o\<close>-accessible part.\<close>

definition Mn :: "nat \<Rightarrow> ot set \<Rightarrow> ot set" where
  "Mn n prev = {a. isH a \<and> wfo a \<and> normd a \<and> nat (- gnd a) \<le> n
                   \<and> (\<forall>\<gamma> \<in> Klt a. norm \<gamma> \<in> prev)}"

fun AccB :: "nat \<Rightarrow> ot set" where
  "AccB 0 = {}"
| "AccB (Suc n) = AccB n \<union> Awf (Mn n (AccB n))"

abbreviation Acc :: "nat \<Rightarrow> ot set" where
  "Acc n \<equiv> Awf (Mn n (AccB n))"

subsection \<open>Monotonicity of the level family\<close>

lemma Mn_mono_prev: "prev \<subseteq> prev' \<Longrightarrow> Mn n prev \<subseteq> Mn n prev'"
  by (auto simp: Mn_def)

lemma AccB_Suc: "AccB n \<subseteq> AccB (Suc n)"
  by auto

lemma AccB_mono: "m \<le> n \<Longrightarrow> AccB m \<subseteq> AccB n"
proof (induction n)
  case 0 thus ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "m = Suc n")
    case True thus ?thesis by simp
  next
    case False
    with Suc.prems have "m \<le> n" by simp
    with Suc.IH have "AccB m \<subseteq> AccB n" .
    thus ?thesis using AccB_Suc by blast
  qed
qed

lemma Acc_subset_Mn: "Acc n \<subseteq> Mn n (AccB n)"
  by (rule Awf_subset)

lemma Mn_wfo: "a \<in> Mn n prev \<Longrightarrow> wfo a" by (simp add: Mn_def)
lemma Mn_isH: "a \<in> Mn n prev \<Longrightarrow> isH a" by (simp add: Mn_def)
lemma Mn_normd: "a \<in> Mn n prev \<Longrightarrow> normd a" by (simp add: Mn_def)

lemma AccB_props: "a \<in> AccB n \<Longrightarrow> wfo a \<and> isH a"
proof (induction n)
  case 0 thus ?case by simp
next
  case (Suc n)
  from Suc.prems have "a \<in> AccB n \<or> a \<in> Acc n" by auto
  thus ?case
  proof
    assume "a \<in> AccB n" thus ?thesis by (rule Suc.IH)
  next
    assume "a \<in> Acc n"
    hence "a \<in> Mn n (AccB n)" using Acc_subset_Mn by blast
    thus ?thesis using Mn_wfo Mn_isH by blast
  qed
qed

lemma Acc_subset_AccB: "m < n \<Longrightarrow> Acc m \<subseteq> AccB n"
proof -
  assume "m < n"
  hence "Suc m \<le> n" by simp
  have "Acc m \<subseteq> AccB (Suc m)" by auto
  also have "AccB (Suc m) \<subseteq> AccB n" using \<open>Suc m \<le> n\<close> by (rule AccB_mono)
  finally show ?thesis .
qed

subsection \<open>The shift is also an automorphism of the principal order \<open>pR\<close>\<close>

lemma shift_pR [simp]: "((shift k a, shift k b) \<in> pR) = ((a, b) \<in> pR)"
  by simp

lemma acc_shift_pR_aux: "a \<in> Wellfounded.acc pR \<Longrightarrow> shift k a \<in> Wellfounded.acc pR"
proof (induction set: Wellfounded.acc)
  case (1 a)
  show ?case
  proof (rule accI)
    fix y assume y: "(y, shift k a) \<in> pR"
    have "(shift k (shift (- k) y), shift k a) \<in> pR" using y by simp
    hence "(shift (- k) y, a) \<in> pR" by (simp only: shift_pR)
    hence "shift k (shift (- k) y) \<in> Wellfounded.acc pR" using "1.IH" by blast
    thus "y \<in> Wellfounded.acc pR" by simp
  qed
qed

lemma acc_shift_pR [simp]: "(shift k a \<in> Wellfounded.acc pR) = (a \<in> Wellfounded.acc pR)"
proof
  assume "shift k a \<in> Wellfounded.acc pR"
  from acc_shift_pR_aux[OF this, of "- k"] show "a \<in> Wellfounded.acc pR" by simp
next
  assume "a \<in> Wellfounded.acc pR"
  thus "shift k a \<in> Wellfounded.acc pR" by (rule acc_shift_pR_aux)
qed

subsection \<open>Normalization lands in the normalized terms\<close>

lemma normd_norm [simp]: "normd (norm a)"
proof (cases "FCset a = {}")
  case True thus ?thesis by (simp add: normd_def norm_def FC_def)
next
  case False thus ?thesis by (simp add: normd_def FC_norm)
qed

lemma wfo_norm [simp]: "wfo (norm a) = wfo a"
  by (simp add: norm_def)

lemma isH_norm [simp]: "isH (norm a) = isH a"
  by (simp add: norm_def)

subsection \<open>The actual well-foundedness target: the \<open>\<Omega>\<close>-free terms\<close>

text \<open>\<^bold>\<open>Correction (2026-06-08).\<close>  With \<^typ>\<open>int\<close> levels the \<^emph>\<open>full\<close> order is
  \<^emph>\<open>not\<close> well-founded: \<open>\<Omega>\<^bsub>0\<^esub> >\<^sub>o \<Omega>\<^bsub>-1\<^esub> >\<^sub>o \<Omega>\<^bsub>-2\<^esub> >\<^sub>o \<dots>\<close> descends forever (Towsner
  \<section>3.2 opening).  So \<open>wf pR\<close> / \<open>wf oltRw\<close> on \<^emph>\<open>all\<close> terms are \<^bold>\<open>false\<close>.

  The PSS embedding \<^const>\<open>embed\<close> however produces only \<^const>\<open>Th\<close>/\<^const>\<open>Su\<close> terms \<dash>
  \<^emph>\<open>no \<open>\<Omega>\<close> at all\<close> (the \<open>\<Omega>\<^bsub>n\<^esub>\<close> are merely scaffolding inside the well-foundedness
  proof).  Hence the real target is well-foundedness restricted to the \<open>\<Omega>\<close>-free
  terms, which excludes the descending \<open>\<Omega>\<^bsub>-k\<^esub>\<close> chain and is genuinely well-founded.\<close>

lemma omfree_FCset [simp]: "omfree a \<Longrightarrow> FCset a = {}"
  by (induction a) auto

lemma omfree_Kn: "omfree a \<Longrightarrow> \<gamma> \<in> Kn n a \<Longrightarrow> omfree \<gamma>"
  by (induction a arbitrary: \<gamma>) (auto split: if_splits)

text \<open>The well-foundedness target: \<open><\<^sub>o\<close> restricted to the well-formed, \<open>\<Omega>\<close>-free,
  \<^bold>\<open>nonnegative-subscript\<close> terms.  The \<open>nneg\<close> conjunct is essential for soundness:
  without it \<open>\<vartheta>\<^bsub>-k\<^esub> 0\<close> gives an infinite descending chain (@{thm [source] nneg_Kn}
  context).  The embedding image satisfies all four conjuncts.\<close>

abbreviation oltRwF :: "(ot \<times> ot) set" where
  "oltRwF \<equiv> {(a,b). a <\<^sub>o b \<and> wfo a \<and> wfo b \<and> omfree a \<and> omfree b \<and> nneg a \<and> nneg b}"

abbreviation pRF :: "(ot \<times> ot) set" where
  "pRF \<equiv> {(a,b). a <\<^sub>o b \<and> isH a \<and> isH b \<and> wfo a \<and> wfo b \<and> omfree a \<and> omfree b \<and> nneg a \<and> nneg b}"

subsection \<open>Sum reduction on the \<open>\<Omega>\<close>-free terms\<close>

text \<open>The \<^const>\<open>bag\<close> map sends \<open>oltRwF\<close> into the multiset extension of \<open>oltRwF\<close>.
  Since \<^const>\<open>omfree\<close> excludes \<^const>\<open>Om\<close>, only the \<^const>\<open>Su\<close>/\<^const>\<open>Th\<close> cases occur.\<close>

lemma bag_mono_wF:
  assumes "(a, b) \<in> oltRwF"
  shows "(bag a, bag b) \<in> mult oltRwF"
proof -
  have ab: "a <\<^sub>o b" and wa: "wfo a" and wb: "wfo b" and fa: "omfree a" and fb: "omfree b"
    and na: "nneg a" and nb: "nneg b"
    using assms by auto
  show ?thesis
  proof (cases a)
    case (Om m) thus ?thesis using fa by simp
  next
    case a_Su: (Su xs)
    show ?thesis
    proof (cases b)
      case (Om n) thus ?thesis using fb by simp
    next
      case b_Su: (Su ys)
      from ab a_Su b_Su obtain c
        where c: "c \<in># mset ys - mset xs"
          and dom: "\<forall>z \<in># mset xs - mset ys. z <\<^sub>o c" by auto
      let ?I = "mset xs \<inter># mset ys"
      have x: "mset xs = ?I + (mset xs - mset ys)" by (simp add: multiset_eq_iff min_def)
      have y: "mset ys = ?I + (mset ys - mset xs)" by (simp add: multiset_eq_iff min_def)
      have ne: "mset ys - mset xs \<noteq> {#}" using c by auto
      have "\<forall>k \<in># mset xs - mset ys. \<exists>j \<in># mset ys - mset xs. (k, j) \<in> oltRwF"
      proof
        fix k assume k: "k \<in># mset xs - mset ys"
        hence kx: "k \<in> set xs" by (meson in_diffD set_mset_mset in_multiset_in_set)
        with a_Su wa fa na have "wfo k" "omfree k" "nneg k" by auto
        moreover have cy: "c \<in> set ys" using c by (meson in_diffD set_mset_mset in_multiset_in_set)
        with b_Su wb fb nb have "wfo c" "omfree c" "nneg c" by auto
        moreover have "k <\<^sub>o c" using dom k by auto
        ultimately show "\<exists>j \<in># mset ys - mset xs. (k, j) \<in> oltRwF" using c by auto
      qed
      hence "(?I + (mset xs - mset ys), ?I + (mset ys - mset xs)) \<in> mult oltRwF"
        by (rule one_step_implies_mult[OF ne])
      thus ?thesis using a_Su b_Su x y by simp
    next
      case b_Th: (Th n d)
      have "\<forall>k \<in># mset xs. (k, Th n d) \<in> oltRwF"
        using a_Su b_Th ab wa wb fa fb na nb by auto
      hence "(mset xs, {# Th n d #}) \<in> mult oltRwF" by (rule mult_single_dom)
      thus ?thesis using a_Su b_Th by simp
    qed
  next
    case a_Th: (Th m e)
    show ?thesis
    proof (cases b)
      case (Om n) thus ?thesis using fb by simp
    next
      case b_Su: (Su ys)
      from ab a_Th b_Su obtain z where z: "z \<in> set ys" and le: "a <\<^sub>o z \<or> a = z"
        using a_Th by auto
      show ?thesis
      proof (cases "a <\<^sub>o z")
        case True
        have wz: "wfo z" "omfree z" "nneg z" using z b_Su wb fb nb by auto
        have "z \<in># mset ys" using z by simp
        moreover have "(a, z) \<in> oltRwF" using True wz wa fa na a_Th by auto
        ultimately have "({# a #}, mset ys) \<in> mult oltRwF" by (rule mult_dom_set)
        thus ?thesis using a_Th b_Su by simp
      next
        case False
        with le have ay: "a = z" by simp
        have ain: "a \<in># mset ys" using z ay by simp
        have eq: "mset ys = {# a #} + (mset ys - {# a #})"
          using ain by (metis insert_DiffM add_mset_add_single add.commute)
        have "ys \<noteq> []" using z by auto
        hence "1 \<le> length ys" by (simp add: Suc_le_eq)
        moreover have "length ys \<noteq> 1" using b_Su wb by simp
        ultimately have "2 \<le> length ys" by linarith
        hence "1 \<le> size (mset ys - {# a #})" using ain by (simp add: size_Diff_singleton)
        hence ne: "mset ys - {# a #} \<noteq> {#}" by auto
        have "({# a #}, mset ys) \<in> mult oltRwF"
          using mult_add[of "mset ys - {# a #}" "{# a #}" oltRwF, OF ne] eq by simp
        thus ?thesis using a_Th b_Su by simp
      qed
    next
      case b_Th: (Th n d)
      hence "(a, b) \<in> oltRwF" using a_Th ab wa wb fa fb na nb by auto
      hence "({# a #}, {# b #}) \<in> mult oltRwF" using mult_single_dom[of "{# a #}" b] by simp
      thus ?thesis using a_Th b_Th by simp
    qed
  qed
qed

text \<open>A well-formed \<open>\<Omega>\<close>-free term is accessible once all its \<^const>\<open>bag\<close> summands are.\<close>

lemma acc_of_bag_elemsF:
  assumes a: "wfo a" "omfree a"
    and elems: "\<And>x. x \<in># bag a \<Longrightarrow> x \<in> Wellfounded.acc oltRwF"
  shows "a \<in> Wellfounded.acc oltRwF"
proof -
  have bagacc: "bag a \<in> Wellfounded.acc (mult oltRwF)"
    by (rule acc_mult_of_elems) (rule elems)
  show "a \<in> Wellfounded.acc oltRwF"
  proof (rule acc_pullback[where R = oltRwF and S = "mult oltRwF" and f = bag])
    fix p q assume "(p, q) \<in> oltRwF"
    thus "(bag p, bag q) \<in> mult oltRwF" by (rule bag_mono_wF)
  next
    show "bag a \<in> Wellfounded.acc (mult oltRwF)" by (rule bagacc)
  qed
qed

subsection \<open>The principal (collapse) closure \<dash> the hard core (Towsner Lemma 3.10)\<close>

text \<open>\<^bold>\<open>The well-foundedness core (sorry):\<close> if the argument \<open>d\<close> of a collapse is
  \<open>oltRwF\<close>-accessible then so is \<open>\<vartheta>\<^bsub>n\<^esub> d\<close>.  This is the absolute transcription of
  Buchholz/Towsner Lemma 3.10\<dash>3.11 (proved by induction on \<open>d\<close>'s accessibility plus
  a structural induction on the predecessor, using the ground-stratified
  distinguished sets \<^const>\<open>Acc\<close> with \<open>\<Omega>\<^bsub>n\<^esub>\<close> as cardinal scaffolding and
  \<^const>\<open>norm\<close>/\<^const>\<open>shift\<close> for ground-normalization; the cross-subscript predecessor
  case \<open>\<vartheta>\<^bsub>p\<^esub> e <\<^sub>o \<vartheta>\<^bsub>n\<^esub> d\<close> with \<open>p < n\<close> is the genuine difficulty).  It is the single
  remaining hard obligation; the whole termination theorem reduces to it.\<close>

lemma L_ThF:
  assumes "omfree d" "wfo d" "nneg d" "0 \<le> n" "d \<in> Wellfounded.acc oltRwF"
  shows "Th n d \<in> Wellfounded.acc oltRwF"
proof -
  from assms(5)
  have "omfree d \<longrightarrow> wfo d \<longrightarrow> nneg d \<longrightarrow> (\<forall>n. 0 \<le> n \<longrightarrow> Th n d \<in> Wellfounded.acc oltRwF)"
  proof (induction set: Wellfounded.acc)
    case (1 d)
    note dacc = "1.hyps"
    note IH  = "1.IH"
    have pred_acc: "\<And>y. (y, d) \<in> oltRwF \<Longrightarrow> y \<in> Wellfounded.acc oltRwF"
      using dacc by (blast intro: acc_downward)
    show ?case
    proof (intro impI allI)
      assume fd: "omfree d" and wd: "wfo d" and nd: "nneg d"
      fix n :: int assume n0: "0 \<le> n"
      show "Th n d \<in> Wellfounded.acc oltRwF"
      proof (rule accI)
        fix r assume rR: "(r, Th n d) \<in> oltRwF"
        hence rlt: "r <\<^sub>o Th n d" and wr: "wfo r" and fr: "omfree r" and nr: "nneg r" by auto
        \<comment> \<open>domination by a critical subterm of \<open>d\<close> is accessible\<close>
        have dom_acc: "\<And>q. wfo q \<Longrightarrow> omfree q \<Longrightarrow> nneg q \<Longrightarrow> (\<exists>\<gamma>\<in>Kn n d. q \<le>\<^sub>o \<gamma>) \<Longrightarrow> q \<in> Wellfounded.acc oltRwF"
        proof -
          fix q assume wq: "wfo q" and fq: "omfree q" and nq: "nneg q" and ex: "\<exists>\<gamma>\<in>Kn n d. q \<le>\<^sub>o \<gamma>"
          from ex obtain \<gamma> where g: "\<gamma> \<in> Kn n d" "q \<le>\<^sub>o \<gamma>" by auto
          have wg: "wfo \<gamma>" using wfo_Kn[OF wd g(1)] .
          have fg: "omfree \<gamma>" using omfree_Kn[OF fd g(1)] .
          have ng: "nneg \<gamma>" using nneg_Kn[OF nd g(1)] .
          have gd: "\<gamma> \<le>\<^sub>o d" using Kn_le_self[OF g(1)] .
          have g_acc: "\<gamma> \<in> Wellfounded.acc oltRwF"
          proof (cases "\<gamma> = d")
            case True thus ?thesis by (simp add: dacc)
          next
            case False with gd have "(\<gamma>, d) \<in> oltRwF" using wg fg ng wd fd nd by simp
            thus ?thesis by (rule pred_acc)
          qed
          show "q \<in> Wellfounded.acc oltRwF"
          proof (cases "q = \<gamma>")
            case True thus ?thesis by (simp add: g_acc)
          next
            case False with g(2) have qg: "(q, \<gamma>) \<in> oltRwF" using wq fq nq wg fg ng by simp
            show ?thesis by (rule acc_downward[OF g_acc qg])
          qed
        qed
        \<comment> \<open>principal predecessor of \<open>Th n d\<close> is accessible\<close>
        have pacc: "\<And>q. wfo q \<Longrightarrow> omfree q \<Longrightarrow> nneg q \<Longrightarrow> isH q \<Longrightarrow> q <\<^sub>o Th n d \<Longrightarrow> q \<in> Wellfounded.acc oltRwF"
        proof -
          fix q assume wq: "wfo q" and fq: "omfree q" and nq: "nneg q" and hq: "isH q" and qlt: "q <\<^sub>o Th n d"
          from hq fq obtain p e where qTh: "q = Th p e"
            by (cases q) auto
          have we: "wfo e" using wq qTh by simp
          have fe: "omfree e" using fq qTh by simp
          have ne: "nneg e" using nq qTh by simp
          have p0: "0 \<le> p" using nq qTh by simp
          from qlt qTh
          have disj: "(\<exists>\<gamma>\<in>Kn n d. Th p e \<le>\<^sub>o \<gamma>)
              \<or> ((\<forall>\<gamma>\<in>Kn p e. \<gamma> <\<^sub>o Th n d) \<and> (p < n \<or> (p = n \<and> e <\<^sub>o d)))" by simp
          from disj show "q \<in> Wellfounded.acc oltRwF"
          proof
            assume "\<exists>\<gamma>\<in>Kn n d. Th p e \<le>\<^sub>o \<gamma>"
            thus ?thesis using dom_acc[of q] wq fq nq qTh by simp
          next
            assume A: "(\<forall>\<gamma>\<in>Kn p e. \<gamma> <\<^sub>o Th n d) \<and> (p < n \<or> (p = n \<and> e <\<^sub>o d))"
            from A consider (eq) "p = n" "e <\<^sub>o d" | (lt) "p < n" by auto
            thus ?thesis
            proof cases
              case eq
              have ed: "(e, d) \<in> oltRwF" using eq(2) we fe ne wd fd nd by simp
              have "Th n e \<in> Wellfounded.acc oltRwF"
                using IH[OF ed] we fe ne n0 by blast
              thus ?thesis using qTh eq(1) by simp
            next
              case lt
              \<comment> \<open>\<^bold>\<open>the genuine Buchholz collapse core (sorry)\<close>: cross-subscript \<open>0 \<le> p < n\<close>\<close>
              \<comment> \<open>now a TRUE goal (the \<open>nneg\<close> restriction removes the false \<open>p < 0\<close> descent)\<close>
              show ?thesis sorry
            qed
          qed
        qed
        show "r \<in> Wellfounded.acc oltRwF"
        proof (cases "isH r")
          case True thus ?thesis using pacc[of r] wr fr nr rlt by simp
        next
          case False
          then obtain ys where ys: "r = Su ys" using fr by (cases r) auto
          have summ: "\<And>z. z \<in> set ys \<Longrightarrow> z <\<^sub>o Th n d"
            using rlt ys by (cases "Th n d") auto
          show ?thesis
          proof (rule acc_of_bag_elemsF)
            show "wfo r" by (rule wr)
            show "omfree r" by (rule fr)
            fix x assume "x \<in># bag r"
            hence x: "x \<in> set ys" using ys by simp
            hence wx: "wfo x" and hx: "isH x" and fx: "omfree x" and nx: "nneg x"
              using wr fr nr ys by auto
            show "x \<in> Wellfounded.acc oltRwF" using pacc[of x] wx fx nx hx summ[OF x] by simp
          qed
        qed
      qed
    qed
  qed
  with assms(1,2,3,4) show ?thesis by blast
qed

text \<open>Towsner Thm 3.12 (structural induction): every \<open>\<Omega>\<close>-free well-formed term is
  accessible.  \<^const>\<open>Om\<close> cannot occur (\<^const>\<open>omfree\<close>); \<^const>\<open>Su\<close> reduces to its
  summands; \<^const>\<open>Th\<close> uses the collapse closure @{thm [source] L_ThF}.\<close>

lemma masterF: "omfree a \<Longrightarrow> wfo a \<Longrightarrow> nneg a \<Longrightarrow> a \<in> Wellfounded.acc oltRwF"
proof (induction a)
  case (Om m) thus ?case by simp
next
  case (Th n d)
  have d: "omfree d" "wfo d" "nneg d" using Th.prems by auto
  have n0: "0 \<le> n" using Th.prems by simp
  have "d \<in> Wellfounded.acc oltRwF" using Th.IH d by blast
  thus ?case using L_ThF[OF d(1) d(2) d(3) n0] by blast
next
  case (Su xs)
  show ?case
  proof (rule acc_of_bag_elemsF)
    show "wfo (Su xs)" using Su.prems by simp
    show "omfree (Su xs)" using Su.prems by simp
    fix x assume "x \<in># bag (Su xs)"
    hence x: "x \<in> set xs" by simp
    hence "omfree x" "wfo x" "nneg x" using Su.prems by auto
    thus "x \<in> Wellfounded.acc oltRwF" using Su.IH x by blast
  qed
qed

subsection \<open>Assembly: \<open>wf oltRwF\<close> (well-foundedness on the \<open>\<Omega>\<close>-free terms)\<close>

theorem wf_oltRwF: "wf oltRwF"
proof (subst wf_iff_acc, intro allI)
  fix b
  show "b \<in> Wellfounded.acc oltRwF"
  proof (cases "wfo b \<and> omfree b \<and> nneg b")
    case True thus ?thesis by (intro masterF) auto
  next
    case False
    have "\<And>y. (y, b) \<in> oltRwF \<Longrightarrow> y \<in> Wellfounded.acc oltRwF" using False by auto
    thus ?thesis by (rule accI)
  qed
qed

end
