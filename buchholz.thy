theory buchholz
  imports wflevel
begin

section \<open>The Buchholz well-foundedness core: \<open>wf pR\<close> via distinguished sets\<close>

text \<open>
  We prove the remaining obligation \<^prop>\<open>wf pR\<close> \<dash> equivalently, every
  well-formed term is \<open>oltRw\<close>-accessible \<dash> by the distinguished-set construction
  of Buchholz / Towsner (\<^emph>\<open>Polymorphic Ordinal Notations\<close> \<section>3.2), adapted to the
  absolute system of \<^theory>\<open>YAPSS.wo\<close>.

  Accessibility cannot be obtained by any simple measure induction: an
  \<open><\<^sub>o\<close>-predecessor of \<open>a\<close> may have arbitrarily large \<^const>\<open>size\<close> (e.g.
  \<open>\<vartheta>\<^sub>p e <\<^sub>o \<vartheta>\<^sub>n d\<close> with \<open>p < n\<close> and \<open>e\<close> huge but all its critical subterms small).
  Instead we stratify by formal cardinality \<^const>\<open>FC\<close> and build, level by level, a
  family \<open>AccBelow\<close> of already-accessible terms, proving that predecessors of a
  level-\<open>n\<close> term stay within the level or drop to a lower one.

  \<^item> \<^term>\<open>Mlev n prev\<close> \<dash> the well-formed terms of cardinality \<open>\<le> n\<close> whose
    critical subterms of cardinality \<open>< n\<close> are already in \<open>prev\<close>;
  \<^item> \<^term>\<open>AccBelow n\<close> \<dash> \<open>\<Union>\<^bsub>i<n\<^esub>\<close> of the accessible part of each level \<open>Mlev i\<close>.
\<close>

subsection \<open>The level family\<close>

definition Mlev :: "nat \<Rightarrow> ot set \<Rightarrow> ot set" where
  "Mlev n prev =
     {a. wfo a \<and> FC a \<le> n \<and> (\<forall>p \<gamma>. \<gamma> \<in> Kn p a \<longrightarrow> FC \<gamma> < n \<longrightarrow> \<gamma> \<in> prev)}"

definition Awf :: "ot set \<Rightarrow> ot set" where
  "Awf S = S \<inter> Wellfounded.acc {(x, y). x <\<^sub>o y \<and> x \<in> S \<and> y \<in> S}"

fun AccBelow :: "nat \<Rightarrow> ot set" where
  "AccBelow 0 = {}"
| "AccBelow (Suc n) = AccBelow n \<union> Awf (Mlev n (AccBelow n))"

abbreviation Acc :: "nat \<Rightarrow> ot set" where
  "Acc n \<equiv> Awf (Mlev n (AccBelow n))"

subsection \<open>Basic facts about the accessible part \<open>Awf\<close>\<close>

lemma Awf_subset: "Awf S \<subseteq> S"
  by (auto simp: Awf_def)

lemma Awf_acc:
  "a \<in> Awf S \<Longrightarrow> a \<in> Wellfounded.acc {(x, y). x <\<^sub>o y \<and> x \<in> S \<and> y \<in> S}"
  by (simp add: Awf_def)

text \<open>The order restricted to \<^term>\<open>Awf S\<close> is well-founded (used to lift
  within-level accessibility).\<close>

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

subsection \<open>Monotonicity of the level family\<close>

lemma AccBelow_Suc: "AccBelow n \<subseteq> AccBelow (Suc n)"
  by auto

lemma AccBelow_mono: "m \<le> n \<Longrightarrow> AccBelow m \<subseteq> AccBelow n"
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
    with Suc.IH have "AccBelow m \<subseteq> AccBelow n" .
    thus ?thesis using AccBelow_Suc by blast
  qed
qed

lemma Mlev_mono_prev: "prev \<subseteq> prev' \<Longrightarrow> Mlev n prev \<subseteq> Mlev n prev'"
  by (auto simp: Mlev_def)

lemma Acc_subset_Mlev: "Acc n \<subseteq> Mlev n (AccBelow n)"
  by (rule Awf_subset)

lemma AccBelow_wfo: "a \<in> AccBelow n \<Longrightarrow> wfo a"
proof (induction n)
  case 0 thus ?case by simp
next
  case (Suc n)
  from Suc.prems have "a \<in> AccBelow n \<or> a \<in> Acc n" by auto
  thus ?case
  proof
    assume "a \<in> AccBelow n" thus ?thesis by (rule Suc.IH)
  next
    assume "a \<in> Acc n"
    hence "a \<in> Mlev n (AccBelow n)" using Acc_subset_Mlev by blast
    thus ?thesis by (simp add: Mlev_def)
  qed
qed

end
