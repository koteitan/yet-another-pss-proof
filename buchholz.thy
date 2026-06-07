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

abbreviation oltRwF :: "(ot \<times> ot) set" where
  "oltRwF \<equiv> {(a,b). a <\<^sub>o b \<and> wfo a \<and> wfo b \<and> omfree a \<and> omfree b}"

abbreviation pRF :: "(ot \<times> ot) set" where
  "pRF \<equiv> {(a,b). a <\<^sub>o b \<and> isH a \<and> isH b \<and> wfo a \<and> wfo b \<and> omfree a \<and> omfree b}"

text \<open>\<^bold>\<open>The well-foundedness core (sorry):\<close> every \<open>\<Omega>\<close>-free well-formed principal is
  \<open>pRF\<close>-accessible.  This is the absolute transcription of Buchholz/Towsner Thm 3.12
  (structural induction populating the distinguished sets \<^const>\<open>Acc\<close> via the closure
  Lemmas 3.10/3.11, with \<open>\<Omega>\<^bsub>n\<^esub>\<close> as cardinal scaffolding).  It is the single remaining
  hard obligation.\<close>

lemma masterF: "omfree a \<Longrightarrow> wfo a \<Longrightarrow> isH a \<Longrightarrow> a \<in> Wellfounded.acc pRF"
  sorry

subsection \<open>Assembly: \<open>wf pRF\<close> and \<open>wf oltRwF\<close> (on the \<open>\<Omega>\<close>-free terms)\<close>

theorem wf_pRF: "wf pRF"
proof (subst wf_iff_acc, intro allI)
  fix b
  show "b \<in> Wellfounded.acc pRF"
  proof (cases "wfo b \<and> isH b \<and> omfree b")
    case True
    thus ?thesis by (intro masterF) auto
  next
    case False
    have "\<And>y. (y, b) \<in> pRF \<Longrightarrow> y \<in> Wellfounded.acc pRF" using False by auto
    thus ?thesis by (rule accI)
  qed
qed

end
