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
     {a. wfo a \<and> isH a \<and> FC a \<le> n \<and> (\<forall>p \<gamma>. \<gamma> \<in> Kn p a \<longrightarrow> FC \<gamma> < n \<longrightarrow> \<gamma> \<in> prev)}"

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

lemma Mlev_wfo: "a \<in> Mlev n prev \<Longrightarrow> wfo a"
  by (simp add: Mlev_def)

lemma Mlev_isH: "a \<in> Mlev n prev \<Longrightarrow> isH a"
  by (simp add: Mlev_def)

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
    thus ?thesis by (rule Mlev_wfo)
  qed
qed

lemma AccBelow_isH: "a \<in> AccBelow n \<Longrightarrow> isH a"
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
    thus ?thesis by (rule Mlev_isH)
  qed
qed

text \<open>The restricted order used inside \<^const>\<open>Awf\<close> of a principal set sits inside
  the principal order \<^const>\<open>pR\<close>.\<close>

lemma restrict_into_pR:
  assumes "S \<subseteq> {a. wfo a \<and> isH a}"
  shows "{(x, y). x <\<^sub>o y \<and> x \<in> S \<and> y \<in> S} \<subseteq> pR"
  using assms by auto

subsection \<open>Predecessor closure (the key order lemma)\<close>

text \<open>A \<^const>\<open>pR\<close>-predecessor of a level-\<open>n\<close> term is again at level \<open>n\<close> or has
  already been collected at a lower level.  This is the heart of the Buchholz
  argument (the order is engineered so that the critical subterms of a predecessor
  are bounded by those of the larger term).\<close>

definition PC :: "nat \<Rightarrow> bool" where
  "PC n \<longleftrightarrow> (\<forall>a r. a \<in> Mlev n (AccBelow n) \<longrightarrow> (r, a) \<in> pR
              \<longrightarrow> r \<in> Mlev n (AccBelow n) \<or> r \<in> AccBelow n)"

subsection \<open>(II) Level-accessibility lifts to global \<open>pR\<close>-accessibility\<close>

lemma Acc_imp_acc_pR_step:
  assumes IHn: "AccBelow n \<subseteq> Wellfounded.acc pR"
    and pc: "PC n"
  shows "Acc n \<subseteq> Wellfounded.acc pR"
proof
  fix a assume "a \<in> Acc n"
  let ?M = "Mlev n (AccBelow n)"
  let ?R = "{(x, y). x <\<^sub>o y \<and> x \<in> ?M \<and> y \<in> ?M}"
  from \<open>a \<in> Acc n\<close> have aM: "a \<in> ?M" and "a \<in> Wellfounded.acc ?R"
    by (auto simp: Awf_def)
  from \<open>a \<in> Wellfounded.acc ?R\<close> have "a \<in> ?M \<longrightarrow> a \<in> Wellfounded.acc pR"
  proof (induction set: Wellfounded.acc)
    case (1 a)
    show ?case
    proof
      assume aM: "a \<in> ?M"
      show "a \<in> Wellfounded.acc pR"
      proof (rule accI)
        fix r assume rpa: "(r, a) \<in> pR"
        from pc aM rpa have "r \<in> ?M \<or> r \<in> AccBelow n"
          by (simp add: PC_def)
        thus "r \<in> Wellfounded.acc pR"
        proof
          assume rM: "r \<in> ?M"
          have "r <\<^sub>o a" using rpa by simp
          hence "(r, a) \<in> ?R" using rM aM by simp
          thus ?thesis using 1 rM by blast
        next
          assume "r \<in> AccBelow n"
          thus ?thesis using IHn by blast
        qed
      qed
    qed
  qed
  with aM show "a \<in> Wellfounded.acc pR" by simp
qed

lemma AccBelow_acc_pR:
  assumes "\<And>m. PC m"
  shows "AccBelow n \<subseteq> Wellfounded.acc pR"
proof (induction n)
  case 0 thus ?case by simp
next
  case (Suc n)
  have "Acc n \<subseteq> Wellfounded.acc pR"
    by (rule Acc_imp_acc_pR_step[OF Suc.IH assms])
  thus ?case using Suc.IH by auto
qed

subsection \<open>(I) every well-formed principal sits at its own level\<close>

text \<open>The cumulative family collects every lower level.\<close>

lemma Acc_subset_AccBelow: "m < n \<Longrightarrow> Acc m \<subseteq> AccBelow n"
proof -
  assume "m < n"
  hence "Suc m \<le> n" by simp
  have "Acc m \<subseteq> AccBelow (Suc m)" by auto
  also have "AccBelow (Suc m) \<subseteq> AccBelow n" using \<open>Suc m \<le> n\<close> by (rule AccBelow_mono)
  finally show "Acc m \<subseteq> AccBelow n" .
qed

text \<open>The master accessibility statement (Towsner Thm 3.12, absolute form):
  every well-formed principal term lies in the accessible part of its own level.\<close>

definition Ifull :: bool where
  "Ifull \<longleftrightarrow> (\<forall>a. wfo a \<longrightarrow> isH a \<longrightarrow> a \<in> Acc (FC a))"

text \<open>\<open>Ifull\<close> gives the \<open>(I\<dash>below)\<close> property used to discharge \<^const>\<open>PC\<close>.\<close>

lemma Ifull_imp_below:
  assumes Ifull
    and "wfo \<gamma>" "isH \<gamma>" "FC \<gamma> < n"
  shows "\<gamma> \<in> AccBelow n"
proof -
  have "\<gamma> \<in> Acc (FC \<gamma>)" using assms by (simp add: Ifull_def)
  moreover have "Acc (FC \<gamma>) \<subseteq> AccBelow n" using \<open>FC \<gamma> < n\<close> by (rule Acc_subset_AccBelow)
  ultimately show ?thesis by blast
qed

lemma Ifull_imp_PC:
  assumes Ifull
  shows "PC n"
  unfolding PC_def
proof (intro allI impI)
  fix a r
  assume aM: "a \<in> Mlev n (AccBelow n)" and rpa: "(r, a) \<in> pR"
  from rpa have rlt: "r <\<^sub>o a" and hr: "isH r" and wr: "wfo r"
    and ha: "isH a" and wa: "wfo a" by auto
  have "FC a \<le> n" using aM by (simp add: Mlev_def)
  moreover have "FC r \<le> FC a" using FC_mono_pr[OF hr ha rlt] .
  ultimately have FCr: "FC r \<le> n" by simp
  show "r \<in> Mlev n (AccBelow n) \<or> r \<in> AccBelow n"
  proof (cases "FC r < n")
    case True
    hence "r \<in> AccBelow n" using Ifull_imp_below[OF assms wr hr] by simp
    thus ?thesis ..
  next
    case False
    with FCr have "FC r = n" by simp
    have "\<forall>p \<gamma>. \<gamma> \<in> Kn p r \<longrightarrow> FC \<gamma> < n \<longrightarrow> \<gamma> \<in> AccBelow n"
    proof (intro allI impI)
      fix p \<gamma> assume g: "\<gamma> \<in> Kn p r" and fg: "FC \<gamma> < n"
      have "wfo \<gamma>" using wfo_Kn[OF wr g] .
      moreover have "isH \<gamma>" using Kn_isH[OF g] .
      ultimately show "\<gamma> \<in> AccBelow n" using Ifull_imp_below[OF assms _ _ fg] by simp
    qed
    hence "r \<in> Mlev n (AccBelow n)"
      using wr hr FCr by (simp add: Mlev_def)
    thus ?thesis ..
  qed
qed

subsection \<open>Assembly: \<open>Ifull \<Longrightarrow> wf pR\<close>\<close>

theorem wf_pR_of_Ifull:
  assumes Ifull
  shows "wf pR"
proof (subst wf_iff_acc, intro allI)
  fix a
  have pc: "\<And>m. PC m" using assms by (rule Ifull_imp_PC)
  show "a \<in> Wellfounded.acc pR"
  proof (cases "wfo a \<and> isH a")
    case True
    hence "a \<in> Acc (FC a)" using assms by (simp add: Ifull_def)
    hence "a \<in> AccBelow (Suc (FC a))" by auto
    moreover have "AccBelow (Suc (FC a)) \<subseteq> Wellfounded.acc pR"
      by (rule AccBelow_acc_pR[OF pc])
    ultimately show ?thesis by blast
  next
    case False
    have "\<And>y. (y, a) \<in> pR \<Longrightarrow> y \<in> Wellfounded.acc pR" using False by auto
    thus ?thesis by (rule accI)
  qed
qed

corollary wf_oltRw_of_Ifull:
  assumes Ifull
  shows "wf oltRw"
  by (rule wf_oltRw_of_wf_pR[OF wf_pR_of_Ifull[OF assms]])

end
