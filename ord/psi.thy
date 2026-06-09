theory psi
  imports "ZFC_in_HOL.ZFC_in_HOL" "ZFC_in_HOL.Ordinal_Exp"
begin

text \<open>\<^bold>\<open>Buchholz \<open>\<psi>\<^sub>v\<close> collapsing functions on the ZFC-in-HOL ordinals\<close> (route A).

  Faithful transcription of Buchholz 1986 \<section>1 (see \<^file>\<open>../conventionals.md\<close>).  The
  PSS notation \<open>three\<close> uses only \<^emph>\<open>finite\<close> subscripts, so we index the collapsing
  functions by \<^typ>\<open>nat\<close> (\<open>v \<in> \<nat>\<close>); \<open>\<psi>\<^sub>\<omega>\<close> occurs only as the cofinal limit, never
  inside a term.  \<open>\<Omega>\<^sub>v = \<aleph>\<^sub>v\<close> (\<open>v>0\<close>), \<open>\<Omega>\<^sub>0 = 1\<close>.

  Session \<open>PSI\<close> (dir \<open>ord/\<close>).  Once \<section>1\<dash>2 are stable they wire into the PSS
  termination via the order-embedding \<open>o : three \<Rightarrow> V\<close>.\<close>

subsection \<open>The cardinals \<open>\<Omega>\<^sub>v\<close>\<close>

definition Om :: "nat \<Rightarrow> V" where
  "Om v = (if v = 0 then 1 else \<aleph> (ord_of_nat v))"

lemma Ord_Om [simp, intro]: "Ord (Om v)"
  by (simp add: Om_def Card_is_Ord)

lemma Om_0 [simp]: "Om 0 = 1"
  by (simp add: Om_def)

lemma Card_Om: "0 < v \<Longrightarrow> Card (Om v)"
  by (simp add: Om_def Card_Aleph)

text \<open>Strictly increasing: \<open>\<Omega>\<^sub>v < \<Omega>\<^bsub>v+1\<^esub>\<close> (needed so that \<open>\<psi>\<^sub>v \<alpha> < \<Omega>\<^bsub>v+1\<^esub>\<close>).\<close>

lemma Om_less_Suc: "Om v < Om (Suc v)"
proof -
  have inf: "\<omega> \<le> Om (Suc v)"
    using InfCard_Aleph[of "ord_of_nat (Suc v)"] by (simp add: Om_def InfCard_def)
  show ?thesis
  proof (cases v)
    case 0
    have "(1::V) < \<omega>" by (simp add: OrdmemD)
    from less_le_trans[OF this inf] show ?thesis using 0 by simp
  next
    case (Suc k)
    have "ord_of_nat v < ord_of_nat (Suc v)" by (simp add: less_succ_self)
    thus ?thesis using Suc by (simp add: Om_def Aleph_increasing)
  qed
qed

subsection \<open>The sets \<open>C\<^sub>v(\<alpha>)\<close> and the collapsing functions \<open>\<psi>\<^sub>v(\<alpha>)\<close> (Buchholz \<section>1)\<close>

text \<open>\<open>C\<^sub>v(\<alpha>)\<close> = least set \<open>\<supseteq> \<Omega>\<^sub>v\<close> closed under \<open>+\<close> and under \<open>\<xi> \<mapsto> \<psi>\<^sub>u \<xi>\<close> for
  \<open>\<xi> < \<alpha>\<close>, \<open>u \<in> \<nat>\<close> (Buchholz's condition \<open>\<xi>\<in>C\<^sub>u(\<xi>)\<close> omitted per his Remark).  Built as
  the countable union of the finite closure iterates of \<^term>\<open>Cstep\<close> from \<^term>\<open>Om v\<close>.
  Here \<open>p \<xi> u = \<psi>\<^sub>u \<xi>\<close> is supplied by \<^const>\<open>transrec\<close> for \<open>\<xi> < \<alpha>\<close>.\<close>

definition Cstep :: "(V \<Rightarrow> nat \<Rightarrow> V) \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V" where
  "Cstep p \<alpha> X =
     X \<squnion> set ((\<lambda>(\<xi>,\<eta>). \<xi> + \<eta>) ` (elts X \<times> elts X))
       \<squnion> set ((\<lambda>(\<xi>,u). p \<xi> u) ` ((elts X \<inter> elts \<alpha>) \<times> UNIV))"

definition Cset :: "(V \<Rightarrow> nat \<Rightarrow> V) \<Rightarrow> V \<Rightarrow> nat \<Rightarrow> V" where
  "Cset p \<alpha> v = \<Squnion> (range (\<lambda>n. (Cstep p \<alpha> ^^ n) (Om v)))"

definition psi :: "V \<Rightarrow> nat \<Rightarrow> V" where
  "psi = transrec (\<lambda>p \<alpha> v. (LEAST \<gamma>. Ord \<gamma> \<and> \<gamma> \<notin> elts (Cset p \<alpha> v)))"

text \<open>\<open>\<psi>\<^sub>v(\<alpha>)\<close> with the conventional argument order.\<close>

definition Psi :: "nat \<Rightarrow> V \<Rightarrow> V" where
  "Psi v \<alpha> = psi \<alpha> v"

text \<open>The defining equation of \<^const>\<open>psi\<close> via \<^const>\<open>transrec\<close>.\<close>

lemma psi_unfold:
  "psi \<alpha> v = (LEAST \<gamma>. Ord \<gamma> \<and> \<gamma> \<notin> elts (Cset (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v))"
  unfolding psi_def by (subst transrec) simp

text \<open>\<open>C\<^sub>v(\<alpha>)\<close> is a set, so it cannot contain all ordinals: \<open>\<psi>\<^sub>v(\<alpha>)\<close> is well defined.\<close>

lemma psi_ex: "\<exists>\<gamma>. Ord \<gamma> \<and> \<gamma> \<notin> elts (Cset p \<alpha> v)"
proof (rule ccontr)
  assume "\<not> (\<exists>\<gamma>. Ord \<gamma> \<and> \<gamma> \<notin> elts (Cset p \<alpha> v))"
  hence "ON \<subseteq> elts (Cset p \<alpha> v)" by auto
  from smaller_than_small[OF small_elts this] show False using big_ON by simp
qed

lemma Ord_psi [simp, intro]: "Ord (psi \<alpha> v)"
proof -
  obtain \<gamma> where "Ord \<gamma>" "\<gamma> \<notin> elts (Cset (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v)"
    using psi_ex by blast
  hence "Ord (LEAST \<gamma>. Ord \<gamma> \<and> \<gamma> \<notin> elts (Cset (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v))"
    by (rule Ord_Least)
  thus ?thesis by (subst psi_unfold)
qed

lemma Ord_Psi [simp, intro]: "Ord (Psi v \<alpha>)"
  by (simp add: Psi_def)

lemma psi_notin: "psi \<alpha> v \<notin> elts (Cset (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v)"
proof -
  have "(LEAST \<gamma>. Ord \<gamma> \<and> \<gamma> \<notin> elts (Cset (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v))
          \<notin> elts (Cset (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v)"
    using Ord_LeastI_ex[OF psi_ex] by blast
  thus ?thesis by (subst psi_unfold)
qed

subsection \<open>Closure properties of \<open>C\<^sub>v(\<alpha>)\<close> (Buchholz \<section>1, conditions C1\<dash>C3)\<close>

abbreviation Citer :: "(V \<Rightarrow> nat \<Rightarrow> V) \<Rightarrow> V \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> V" where
  "Citer p \<alpha> v n \<equiv> (Cstep p \<alpha> ^^ n) (Om v)"

lemma small_Cstep_images:
  "small ((\<lambda>(\<xi>,\<eta>). \<xi> + \<eta>) ` (elts X \<times> elts X))"
  "small ((\<lambda>(\<xi>,u::nat). p \<xi> u) ` ((elts X \<inter> elts \<alpha>) \<times> (UNIV::nat set)))"
proof -
  show "small ((\<lambda>(\<xi>,\<eta>). \<xi> + \<eta>) ` (elts X \<times> elts X))" by simp
  have nat: "small (UNIV::nat set)" using small_image_nat[of "\<lambda>x. x" UNIV] by simp
  have "small (elts X \<inter> elts \<alpha>)" using smaller_than_small[OF small_elts Int_lower1] .
  from small_Times[OF this nat]
  have sp: "small ((elts X \<inter> elts \<alpha>) \<times> (UNIV::nat set))" .
  show "small ((\<lambda>(\<xi>,u::nat). p \<xi> u) ` ((elts X \<inter> elts \<alpha>) \<times> (UNIV::nat set)))"
    using replacement[OF sp, where f = "\<lambda>(\<xi>, u::nat). p \<xi> u"] .
qed

lemma elts_Cstep:
  "elts (Cstep p \<alpha> X) = elts X
     \<union> (\<lambda>(\<xi>,\<eta>). \<xi> + \<eta>) ` (elts X \<times> elts X)
     \<union> (\<lambda>(\<xi>,u). p \<xi> u) ` ((elts X \<inter> elts \<alpha>) \<times> UNIV)"
  unfolding Cstep_def by (simp add: small_Cstep_images)

lemma elts_Cset: "elts (Cset p \<alpha> v) = (\<Union>n. elts (Citer p \<alpha> v n))"
  by (simp add: Cset_def)

lemma Cstep_ge: "X \<le> Cstep p \<alpha> X"
  by (metis (no_types, lifting) Cstep_def le_supI1 sup_ge1)

lemma Citer_mono_le: "m \<le> n \<Longrightarrow> Citer p \<alpha> v m \<le> Citer p \<alpha> v n"
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
    with Suc.IH have "Citer p \<alpha> v m \<le> Citer p \<alpha> v n" .
    also have "Citer p \<alpha> v n \<le> Citer p \<alpha> v (Suc n)" using Cstep_ge by simp
    finally show ?thesis .
  qed
qed

lemma Citer_in_Cset: "elts (Citer p \<alpha> v n) \<subseteq> elts (Cset p \<alpha> v)"
  by (auto simp: elts_Cset)

text \<open>C1: \<open>\<Omega>\<^sub>v \<subseteq> C\<^sub>v(\<alpha>)\<close>.\<close>

lemma Om_subset_Cset: "elts (Om v) \<subseteq> elts (Cset p \<alpha> v)"
  using Citer_in_Cset[where n=0] by simp

text \<open>Membership reduces to some finite iterate.\<close>

lemma Cset_mem_iff: "x \<in> elts (Cset p \<alpha> v) \<longleftrightarrow> (\<exists>n. x \<in> elts (Citer p \<alpha> v n))"
  by (auto simp: elts_Cset)

lemma sum_in_Cstep: "\<xi> \<in> elts X \<Longrightarrow> \<eta> \<in> elts X \<Longrightarrow> \<xi> + \<eta> \<in> elts (Cstep p \<alpha> X)"
  by (auto simp: elts_Cstep)

lemma psiarg_in_Cstep: "\<xi> \<in> elts X \<Longrightarrow> \<xi> \<in> elts \<alpha> \<Longrightarrow> p \<xi> u \<in> elts (Cstep p \<alpha> X)"
  by (force simp: elts_Cstep)

lemma Citer_subset_mono: "m \<le> n \<Longrightarrow> elts (Citer p \<alpha> v m) \<subseteq> elts (Citer p \<alpha> v n)"
  by (metis Citer_mono_le less_eq_V_def)

text \<open>C2: closed under \<open>+\<close>.\<close>

lemma Cset_add_closed:
  assumes "\<xi> \<in> elts (Cset p \<alpha> v)" "\<eta> \<in> elts (Cset p \<alpha> v)"
  shows "\<xi> + \<eta> \<in> elts (Cset p \<alpha> v)"
proof -
  from assms obtain m n where m: "\<xi> \<in> elts (Citer p \<alpha> v m)" and n: "\<eta> \<in> elts (Citer p \<alpha> v n)"
    by (auto simp: Cset_mem_iff)
  have "\<xi> \<in> elts (Citer p \<alpha> v (max m n))"
    using m Citer_subset_mono[OF max.cobounded1] by blast
  moreover have "\<eta> \<in> elts (Citer p \<alpha> v (max m n))"
    using n Citer_subset_mono[OF max.cobounded2] by blast
  ultimately have "\<xi> + \<eta> \<in> elts (Cstep p \<alpha> (Citer p \<alpha> v (max m n)))" by (rule sum_in_Cstep)
  also have "Cstep p \<alpha> (Citer p \<alpha> v (max m n)) = Citer p \<alpha> v (Suc (max m n))" by simp
  finally show ?thesis using Citer_in_Cset by blast
qed

text \<open>C3: closed under \<open>\<xi> \<mapsto> p \<xi> u\<close> for \<open>\<xi> < \<alpha>\<close>.\<close>

lemma Cset_psi_closed:
  assumes "\<xi> \<in> elts (Cset p \<alpha> v)" "\<xi> \<in> elts \<alpha>"
  shows "p \<xi> u \<in> elts (Cset p \<alpha> v)"
proof -
  from assms(1) obtain n where n: "\<xi> \<in> elts (Citer p \<alpha> v n)" by (auto simp: Cset_mem_iff)
  from psiarg_in_Cstep[OF n assms(2)] have "p \<xi> u \<in> elts (Cstep p \<alpha> (Citer p \<alpha> v n))" .
  also have "Cstep p \<alpha> (Citer p \<alpha> v n) = Citer p \<alpha> v (Suc n)" by simp
  finally show ?thesis using Citer_in_Cset by blast
qed

text \<open>Every element of \<open>C\<^sub>v(\<alpha>)\<close> is an ordinal, provided the parameter \<open>p\<close> produces
  ordinals on \<open>\<alpha>\<close> (true for \<open>p = \<psi>\<close>).\<close>

lemma Ord_Citer:
  "(\<forall>\<xi> u. \<xi> \<in> elts \<alpha> \<longrightarrow> Ord (p \<xi> u)) \<Longrightarrow> x \<in> elts (Citer p \<alpha> v n) \<Longrightarrow> Ord x"
proof (induction n arbitrary: x)
  case 0
  have "x \<in> elts (Om v)" using "0.prems"(2) by simp
  thus ?case by (rule Ord_in_Ord[OF Ord_Om])
next
  case (Suc n)
  from Suc.prems(2) have "x \<in> elts (Cstep p \<alpha> (Citer p \<alpha> v n))" by simp
  then consider "x \<in> elts (Citer p \<alpha> v n)"
    | \<xi> \<eta> where "\<xi> \<in> elts (Citer p \<alpha> v n)" "\<eta> \<in> elts (Citer p \<alpha> v n)" "x = \<xi> + \<eta>"
    | \<xi> u where "\<xi> \<in> elts (Citer p \<alpha> v n)" "\<xi> \<in> elts \<alpha>" "x = p \<xi> u"
    by (auto simp: elts_Cstep)
  thus ?case
  proof cases
    case 1 thus ?thesis using Suc.IH[OF Suc.prems(1)] by blast
  next
    case 2 thus ?thesis using Suc.IH[OF Suc.prems(1)] by (simp add: Ord_add)
  next
    case 3 thus ?thesis using Suc.prems(1) by simp
  qed
qed

lemma Cset_Ord:
  assumes "\<forall>\<xi> u. \<xi> \<in> elts \<alpha> \<longrightarrow> Ord (p \<xi> u)" and "x \<in> elts (Cset p \<alpha> v)"
  shows "Ord x"
proof -
  from assms(2) obtain n where n: "x \<in> elts (Citer p \<alpha> v n)" by (auto simp: Cset_mem_iff)
  show ?thesis by (rule Ord_Citer[OF assms(1) n])
qed

subsection \<open>Basic properties of \<open>\<psi>\<^sub>v\<close> (Buchholz Lemma 1.2)\<close>

text \<open>\<open>\<Omega>\<^sub>v \<le> \<psi>\<^sub>v(\<alpha>)\<close>: since \<open>\<Omega>\<^sub>v \<subseteq> C\<^sub>v(\<alpha>)\<close>, the least ordinal not in \<open>C\<^sub>v(\<alpha>)\<close> is \<open>\<ge> \<Omega>\<^sub>v\<close>.\<close>

lemma Om_le_psi: "Om v \<le> psi \<alpha> v"
proof (rule ccontr)
  assume "\<not> Om v \<le> psi \<alpha> v"
  hence "psi \<alpha> v < Om v" using Ord_not_le[OF Ord_Om Ord_psi] by blast
  hence "psi \<alpha> v \<in> elts (Om v)" using Ord_mem_iff_lt[OF Ord_psi Ord_Om] by blast
  hence "psi \<alpha> v \<in> elts (Cset (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v)" using Om_subset_Cset by blast
  thus False using psi_notin by simp
qed

subsection \<open>Monotonicity of \<open>C\<^sub>v(\<alpha>)\<close> and \<open>\<psi>\<^sub>v(\<alpha>)\<close> in \<open>\<alpha>\<close> (Buchholz Lemma 1.2(d))\<close>

text \<open>A larger argument and an agreeing (wider) parameter give a larger set.\<close>

lemma Cstep_mono_param:
  assumes "elts \<alpha> \<subseteq> elts \<beta>" "\<forall>\<xi> u. \<xi> \<in> elts \<alpha> \<longrightarrow> p \<xi> u = q \<xi> u" "elts X \<subseteq> elts Y"
  shows "elts (Cstep p \<alpha> X) \<subseteq> elts (Cstep q \<beta> Y)"
proof (rule subsetI)
  fix x assume "x \<in> elts (Cstep p \<alpha> X)"
  then consider "x \<in> elts X"
    | "x \<in> (\<lambda>(\<xi>,\<eta>). \<xi> + \<eta>) ` (elts X \<times> elts X)"
    | "x \<in> (\<lambda>(\<xi>,u). p \<xi> u) ` ((elts X \<inter> elts \<alpha>) \<times> UNIV)"
    by (auto simp: elts_Cstep)
  thus "x \<in> elts (Cstep q \<beta> Y)"
  proof cases
    case 1 thus ?thesis using assms(3) by (auto simp: elts_Cstep)
  next
    case 2
    then obtain \<xi> \<eta> where "\<xi> \<in> elts X" "\<eta> \<in> elts X" "x = \<xi> + \<eta>" by auto
    thus ?thesis using assms(3) by (auto simp: elts_Cstep)
  next
    case 3
    then obtain \<xi> u where x: "\<xi> \<in> elts X \<inter> elts \<alpha>" "x = p \<xi> u" by auto
    have "\<xi> \<in> elts Y \<inter> elts \<beta>" using x(1) assms(1,3) by blast
    moreover have "x = q \<xi> u" using x assms(2) by auto
    ultimately show ?thesis by (auto simp: elts_Cstep)
  qed
qed

lemma Citer_mono_param:
  assumes "elts \<alpha> \<subseteq> elts \<beta>" "\<forall>\<xi> u. \<xi> \<in> elts \<alpha> \<longrightarrow> p \<xi> u = q \<xi> u"
  shows "elts (Citer p \<alpha> v n) \<subseteq> elts (Citer q \<beta> v n)"
proof (induction n)
  case 0 thus ?case by simp
next
  case (Suc n)
  have "elts (Cstep p \<alpha> (Citer p \<alpha> v n)) \<subseteq> elts (Cstep q \<beta> (Citer q \<beta> v n))"
    by (rule Cstep_mono_param[OF assms(1) assms(2) Suc.IH])
  thus ?case by simp
qed

lemma Cset_mono_param:
  assumes "elts \<alpha> \<subseteq> elts \<beta>" "\<forall>\<xi> u. \<xi> \<in> elts \<alpha> \<longrightarrow> p \<xi> u = q \<xi> u"
  shows "elts (Cset p \<alpha> v) \<subseteq> elts (Cset q \<beta> v)"
proof
  fix x assume "x \<in> elts (Cset p \<alpha> v)"
  then obtain n where "x \<in> elts (Citer p \<alpha> v n)" by (auto simp: Cset_mem_iff)
  hence "x \<in> elts (Citer q \<beta> v n)" using Citer_mono_param[OF assms(1) assms(2)] by blast
  thus "x \<in> elts (Cset q \<beta> v)" by (auto simp: Cset_mem_iff)
qed

text \<open>Specialised to \<open>p = q = \<psi>\<close>: \<open>\<alpha> \<le> \<beta> \<Longrightarrow> C\<^sub>v(\<alpha>) \<subseteq> C\<^sub>v(\<beta>)\<close>.\<close>

lemma CC_mono:
  assumes "\<alpha> \<le> \<beta>"
  shows "elts (Cset (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v) \<subseteq> elts (Cset (\<lambda>\<xi>\<in>elts \<beta>. psi \<xi>) \<beta> v)"
proof (rule Cset_mono_param)
  show "elts \<alpha> \<subseteq> elts \<beta>" using assms by (simp add: less_eq_V_def)
  show "\<forall>\<xi> u. \<xi> \<in> elts \<alpha> \<longrightarrow> (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<xi> u = (\<lambda>\<xi>\<in>elts \<beta>. psi \<xi>) \<xi> u"
    using assms by (auto simp: less_eq_V_def subsetD)
qed

text \<open>Weak monotonicity in the argument: \<open>\<alpha> \<le> \<beta> \<Longrightarrow> \<psi>\<^sub>v(\<alpha>) \<le> \<psi>\<^sub>v(\<beta>)\<close> (Buchholz 1.2(d)).\<close>

lemma psi_mono_arg:
  assumes "\<alpha> \<le> \<beta>" shows "psi \<alpha> v \<le> psi \<beta> v"
proof (rule ccontr)
  assume "\<not> psi \<alpha> v \<le> psi \<beta> v"
  hence lt: "psi \<beta> v < psi \<alpha> v" using Ord_not_le[OF Ord_psi Ord_psi] by blast
  have "psi \<beta> v \<in> elts (Cset (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v)"
  proof (rule ccontr)
    assume nin: "psi \<beta> v \<notin> elts (Cset (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v)"
    have "(LEAST \<gamma>. Ord \<gamma> \<and> \<gamma> \<notin> elts (Cset (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v)) \<le> psi \<beta> v"
    proof (rule Ord_Least_le)
      show "Ord (psi \<beta> v)" by simp
      show "psi \<beta> v \<notin> elts (Cset (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v)" by (rule nin)
    qed
    hence "psi \<alpha> v \<le> psi \<beta> v" using psi_unfold[of \<alpha> v] by simp
    with lt show False by simp
  qed
  with CC_mono[OF assms] have "psi \<beta> v \<in> elts (Cset (\<lambda>\<xi>\<in>elts \<beta>. psi \<xi>) \<beta> v)" by blast
  thus False using psi_notin by simp
qed

text \<open>\<^bold>\<open>Strict monotonicity (Buchholz Lemma 1.3)\<close>: if \<open>\<alpha> < \<beta>\<close> and \<open>\<alpha> \<in> C\<^sub>v(\<alpha>)\<close> then
  \<open>\<psi>\<^sub>v(\<alpha>) < \<psi>\<^sub>v(\<beta>)\<close>.  Key for the order-embedding (Lemma 2.2(c)).\<close>

lemma psi_strict_mono_arg:
  assumes "Ord \<alpha>" "Ord \<beta>" "\<alpha> < \<beta>" "\<alpha> \<in> elts (Cset (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v)"
  shows "psi \<alpha> v < psi \<beta> v"
proof -
  have le: "\<alpha> \<le> \<beta>" using assms(3) by simp
  have a\<beta>: "\<alpha> \<in> elts (Cset (\<lambda>\<xi>\<in>elts \<beta>. psi \<xi>) \<beta> v)" using assms(4) CC_mono[OF le] by blast
  have amem: "\<alpha> \<in> elts \<beta>" using assms(1,2,3) by (simp add: Ord_mem_iff_lt)
  have "(\<lambda>\<xi>\<in>elts \<beta>. psi \<xi>) \<alpha> v \<in> elts (Cset (\<lambda>\<xi>\<in>elts \<beta>. psi \<xi>) \<beta> v)"
    by (rule Cset_psi_closed[OF a\<beta> amem])
  hence "psi \<alpha> v \<in> elts (Cset (\<lambda>\<xi>\<in>elts \<beta>. psi \<xi>) \<beta> v)" using amem by simp
  hence "psi \<alpha> v \<noteq> psi \<beta> v" using psi_notin by metis
  with psi_mono_arg[OF le] show ?thesis by (metis order_le_imp_less_or_eq)
qed

subsection \<open>\<open>\<psi>\<^sub>v(\<alpha>)\<close> is additive principal (Buchholz Lemma 1.2(b))\<close>

text \<open>Every ordinal below \<open>\<psi>\<^sub>v(\<alpha>)\<close> already lies in \<open>C\<^sub>v(\<alpha>)\<close> (because \<open>\<psi>\<^sub>v(\<alpha>)\<close> is
  the \<^emph>\<open>least\<close> ordinal outside it).\<close>

lemma below_psi_in_Cset:
  assumes "Ord \<delta>" "\<delta> < psi \<alpha> v"
  shows "\<delta> \<in> elts (Cset (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v)"
proof (rule ccontr)
  assume nin: "\<delta> \<notin> elts (Cset (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v)"
  have "(LEAST \<gamma>. Ord \<gamma> \<and> \<gamma> \<notin> elts (Cset (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v)) \<le> \<delta>"
    by (rule Ord_Least_le) (use assms(1) nin in auto)
  hence "psi \<alpha> v \<le> \<delta>" by (subst psi_unfold)
  with assms(2) show False by simp
qed

text \<open>\<^bold>\<open>Lemma 1.2(b)\<close>: \<open>\<psi>\<^sub>v(\<alpha>)\<close> is additive principal — a sum of two ordinals
  below it stays below it.  (\<open>C\<^sub>v(\<alpha>)\<close> is closed under \<open>+\<close> and contains every
  ordinal below \<open>\<psi>\<^sub>v(\<alpha>)\<close>, while \<open>\<psi>\<^sub>v(\<alpha>)\<close> itself is not in it.)  Proof by
  transfinite induction on the second summand.\<close>

lemma psi_add_principal:
  assumes "Ord \<beta>" "Ord \<gamma>" "\<beta> < psi \<alpha> v" "\<gamma> < psi \<alpha> v"
  shows "\<beta> + \<gamma> < psi \<alpha> v"
proof -
  let ?C = "Cset (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v"
  have betaC: "\<beta> \<in> elts ?C" using assms(1,3) by (rule below_psi_in_Cset)
  have "\<gamma> < psi \<alpha> v \<longrightarrow> \<beta> + \<gamma> < psi \<alpha> v" using assms(2)
  proof (induction \<gamma> rule: Ord_induct)
    case (step \<gamma>)
    show ?case
    proof
      assume gd: "\<gamma> < psi \<alpha> v"
      from step.hyps show "\<beta> + \<gamma> < psi \<alpha> v"
      proof (cases \<gamma> rule: Ord_cases)
        case 0
        with assms(3) show ?thesis by simp
      next
        case (succ \<eta>)
        have eg: "\<eta> \<in> elts \<gamma>" using succ by (metis elts_succ insertI1)
        have eOrd: "Ord \<eta>" using succ by simp
        have ed: "\<eta> < psi \<alpha> v" using less_trans[OF OrdmemD[OF step.hyps eg] gd] .
        have bh: "\<beta> + \<eta> < psi \<alpha> v" using step.IH[OF eg] ed by simp
        have bhC: "\<beta> + \<eta> \<in> elts ?C"
          by (rule below_psi_in_Cset[OF Ord_add[OF assms(1) eOrd] bh])
        have d1: "(1::V) < psi \<alpha> v"
        proof -
          have zg: "(0::V) \<in> elts \<gamma>" using eOrd succ by (metis zero_in_succ)
          have "succ 0 \<le> \<gamma>"
            using succ_le_iff[OF Ord_0 step.hyps] OrdmemD[OF step.hyps zg] by simp
          hence "(1::V) \<le> \<gamma>" by (simp add: succ_eq_add1)
          thus ?thesis using gd by (rule le_less_trans)
        qed
        have oneC: "(1::V) \<in> elts ?C" by (rule below_psi_in_Cset[OF Ord_1 d1])
        have bg: "\<beta> + \<gamma> = (\<beta> + \<eta>) + 1" using succ by (metis add.assoc succ_eq_add1)
        have inC: "\<beta> + \<gamma> \<in> elts ?C"
          using bg Cset_add_closed[OF bhC oneC] by simp
        have le: "\<beta> + \<gamma> \<le> psi \<alpha> v"
        proof -
          have "(\<beta> + \<eta>) + 1 \<le> psi \<alpha> v"
            using bh by (simp add: succ_eq_add1[symmetric] succ_le_iff Ord_add assms(1) eOrd)
          thus ?thesis using bg by simp
        qed
        show ?thesis using le inC psi_notin by (metis order_le_imp_less_or_eq)
      next
        case limit
        have gord: "Ord \<gamma>" using limit by (rule Limit_is_Ord)
        have bz: "\<beta> + z \<le> psi \<alpha> v" if z: "z \<in> elts \<gamma>" for z
        proof -
          have "z < psi \<alpha> v" using less_trans[OF OrdmemD[OF step.hyps z] gd] .
          thus ?thesis using step.IH[OF z] by simp
        qed
        have le: "\<beta> + \<gamma> \<le> psi \<alpha> v"
        proof -
          have "(\<Squnion>z\<in>elts \<gamma>. \<beta> + z) \<le> psi \<alpha> v" using bz by (simp add: SUP_le_iff)
          thus ?thesis using add_Limit[OF limit] by simp
        qed
        have gC: "\<gamma> \<in> elts ?C" by (rule below_psi_in_Cset[OF gord gd])
        have "\<beta> + \<gamma> \<in> elts ?C" using betaC gC by (rule Cset_add_closed)
        with le psi_notin show ?thesis by (metis order_le_imp_less_or_eq)
      qed
    qed
  qed
  thus ?thesis using assms(4) by blast
qed

subsection \<open>The cardinality bound (Buchholz Lemma 1.2(c)): \<open>\<psi>\<^sub>v(\<alpha>) < \<Omega>\<^bsub>v+1\<^esub>\<close>\<close>

text \<open>\<open>|C\<^sub>v(\<alpha>)| \<le> \<Omega>\<^sub>v \<squnion> \<omega> < \<Omega>\<^bsub>v+1\<^esub>\<close>, since \<open>C\<^sub>v(\<alpha>)\<close> is the closure of \<^term>\<open>Om v\<close>
  under \<open>+\<close> and the countably many maps \<open>\<psi>\<^sub>u\<close>.  We avoid importing
  \<open>ZFC_in_HOL.General_Cardinals\<close> (which clashes \<^const>\<open>set\<close> with \<open>List.set\<close>)
  by reproving locally the only two of its lemmas we need (the proofs use base
  \<open>ZFC_in_HOL.ZFC_Cardinals\<close> only).\<close>

text \<open>Local copy of \<open>General_Cardinals.gcard_Times\<close>.\<close>

lemma gcard_Times': "gcard (X \<times> Y) = gcard X \<otimes> gcard Y"
proof (cases "small X \<and> small Y")
  case True
  have "elts (gcard (X \<times> Y)) \<approx> X \<times> Y"
    by (simp add: True gcard_eqpoll)
  also have "... \<approx> elts (gcard X) \<times> elts (gcard Y)"
    by (simp add: True eqpoll_sym gcard_eqpoll times_eqpoll_cong)
  also have "... \<approx> elts (gcard X \<otimes> gcard Y)"
    by (simp add: elts_cmult eqpoll_sym)
  finally show ?thesis
    using Card_cardinal_eq cmult_def gcardinal_cong by force
next
  case False
  have "gcard (X \<times> Y) = 0"
    by (metis False Times_empty gcard_big_0 gcard_empty_0 small_Times_iff)
  then show ?thesis
    by (metis False cmult_0 cmult_commute gcard_big_0)
qed

text \<open>Local copy of \<open>General_Cardinals.gcard_Union_le_cmult\<close>.\<close>

lemma gcard_Union_le_cmult':
  assumes "small U" and \<kappa>: "\<And>x. x \<in> U \<Longrightarrow> gcard x \<le> \<kappa>" and sm: "\<And>x. x \<in> U \<Longrightarrow> small x"
  shows "gcard (\<Union>U) \<le> gcard U \<otimes> \<kappa>"
proof -
  have "\<exists>f. f \<in> x \<rightarrow> elts \<kappa> \<and> inj_on f x" if "x \<in> U" for x
    using \<kappa> [OF that] gcard_le_lepoll by (metis image_subset_iff_funcset lepoll_def sm that)
  then obtain \<phi> where \<phi>: "\<And>x. x \<in> U \<Longrightarrow> (\<phi> x) \<in> x \<rightarrow> elts \<kappa> \<and> inj_on (\<phi> x) x"
    by metis
  define u where "u \<equiv> \<lambda>y. @x. x \<in> U \<and> y \<in> x"
  have u: "u y \<in> U \<and> y \<in> (u y)" if "y \<in> \<Union>( U)" for y
    unfolding u_def using that by (fast intro!: someI2)
  define \<rho> where "\<rho> \<equiv> \<lambda>y. (u y, \<phi> (u y) y)"
  have U: "elts (gcard U) \<approx> U"
    using assms by (simp add: gcard_eqpoll)
  have "\<Union>U \<lesssim> U \<times> elts \<kappa>"
    unfolding lepoll_def
  proof (intro exI conjI)
    show "inj_on \<rho> (\<Union> U)"
      using \<phi> u by (smt (verit) \<rho>_def inj_on_def prod.inject)
    show "\<rho> ` \<Union> U \<subseteq> U \<times> elts \<kappa>"
      using \<phi> u by (auto simp: \<rho>_def)
  qed
  also have "\<dots>  \<approx> elts (gcard U \<otimes> \<kappa>)"
    using U elts_cmult eqpoll_sym eqpoll_trans times_eqpoll_cong by blast
  finally have "(\<Union>U) \<lesssim> elts (gcard U \<otimes> \<kappa>)" .
  then show ?thesis
    by (metis cardinal_idem cmult_def gcard_eq_vcard lepoll_imp_gcard_le small_elts)
qed

text \<open>Auxiliary cardinal facts about \<open>\<Omega>\<^sub>v\<close> and \<open>\<nat>\<close>.\<close>

lemma small_nat_UNIV [simp]: "small (UNIV::nat set)"
  using small_image_nat[of "\<lambda>x. x" UNIV] by simp

lemma Card_Om_all: "Card (Om v)"
proof (cases v)
  case 0
  have "Card (1::V)" using Card_csucc[of 0] by (simp add: csucc_0)
  then show ?thesis using 0 by (simp add: Om_def)
next
  case (Suc k) then show ?thesis by (simp add: Om_def Card_Aleph)
qed

lemma InfCard_Om_sup_omega: "InfCard (Om v \<squnion> \<omega>)"
  by (simp add: InfCard_def Card_Om_all)

lemma gcard_UNIV_nat: "gcard (UNIV::nat set) = \<omega>"
proof -
  have "gcard (UNIV::nat set) = gcard (ord_of_nat ` (UNIV::nat set))"
    using gcard_image[OF inj_ord_of_nat] by simp
  also have "ord_of_nat ` (UNIV::nat set) = elts \<omega>"
    by (auto simp: elts_\<omega>)
  also have "gcard (elts \<omega>) = \<omega>"
    by (simp add: gcard_eq_vcard Card_cardinal_eq)
  finally show ?thesis .
qed

lemma omega_less_Om_Suc: "\<omega> < Om (Suc v)"
proof -
  have "(0::V) < ord_of_nat (Suc v)"
    by (metis OrdmemD Ord_ord_of_nat ord_of_nat.simps(2) zero_in_succ)
  hence "\<aleph>0 < \<aleph> (ord_of_nat (Suc v))"
    by (rule Aleph_increasing) auto
  thus ?thesis by (simp add: Om_def)
qed

lemma kappa_less_Suc: "Om v \<squnion> \<omega> < Om (Suc v)"
proof (cases "Om v \<le> \<omega>")
  case True
  hence "Om v \<squnion> \<omega> = \<omega>" by (simp add: sup.absorb2)
  thus ?thesis using omega_less_Om_Suc by simp
next
  case False
  hence "\<omega> \<le> Om v" using Ord_linear_le[of "Om v" \<omega>] by auto
  hence "Om v \<squnion> \<omega> = Om v" by (simp add: sup.absorb1)
  thus ?thesis using Om_less_Suc by simp
qed

text \<open>The size of each finite closure iterate is bounded by \<open>\<kappa> = \<Omega>\<^sub>v \<squnion> \<omega>\<close>.  The
  bound is independent of the parameter \<open>p\<close> (only its domain matters).\<close>

lemma vcard_Citer_le: "vcard (Citer p \<alpha> v n) \<le> Om v \<squnion> \<omega>"
proof (induction n)
  case 0
  have "vcard (Citer p \<alpha> v 0) = Om v"
    by (simp add: Card_Om_all Card_cardinal_eq)
  also have "Om v \<le> Om v \<squnion> \<omega>" by simp
  finally show ?case .
next
  case (Suc n)
  define X where "X = Citer p \<alpha> v n"
  have IH: "vcard X \<le> Om v \<squnion> \<omega>" using Suc.IH unfolding X_def .
  have infk: "InfCard (Om v \<squnion> \<omega>)" by (rule InfCard_Om_sup_omega)
  let ?A = "elts X"
  let ?B = "(\<lambda>(\<xi>,\<eta>). \<xi> + \<eta>) ` (elts X \<times> elts X)"
  let ?C = "(\<lambda>(\<xi>,u::nat). p \<xi> u) ` ((elts X \<inter> elts \<alpha>) \<times> (UNIV::nat set))"
  have smX: "small ?A" by simp
  have smB: "small ?B" by simp
  have smC: "small ?C" by (rule small_Cstep_images(2))
  \<comment> \<open>each of the three building blocks has \<open>gcard \<le> \<kappa>\<close>\<close>
  have gA: "gcard ?A \<le> Om v \<squnion> \<omega>" using IH by (simp add: gcard_eq_vcard)
  have leX: "gcard (elts X) \<le> Om v \<squnion> \<omega>" using IH by (simp add: gcard_eq_vcard)
  have gB: "gcard ?B \<le> Om v \<squnion> \<omega>"
  proof -
    have "gcard ?B \<le> gcard (elts X \<times> elts X)"
      by (rule gcard_image_le[OF small_Times[OF small_elts small_elts]])
    also have "... = gcard (elts X) \<otimes> gcard (elts X)" by (rule gcard_Times')
    also have "... \<le> (Om v \<squnion> \<omega>) \<otimes> (Om v \<squnion> \<omega>)" by (rule cmult_le_mono[OF leX leX])
    also have "... = Om v \<squnion> \<omega>" by (simp add: InfCard_csquare_eq infk)
    finally show ?thesis .
  qed
  have gC: "gcard ?C \<le> Om v \<squnion> \<omega>"
  proof -
    have "gcard ?C \<le> gcard ((elts X \<inter> elts \<alpha>) \<times> (UNIV::nat set))"
      by (rule gcard_image_le[OF small_Times[OF smaller_than_small[OF small_elts Int_lower1] small_nat_UNIV]])
    also have "... = gcard (elts X \<inter> elts \<alpha>) \<otimes> gcard (UNIV::nat set)" by (rule gcard_Times')
    also have "... = gcard (elts X \<inter> elts \<alpha>) \<otimes> \<omega>" by (simp add: gcard_UNIV_nat)
    also have "... \<le> (Om v \<squnion> \<omega>) \<otimes> (Om v \<squnion> \<omega>)"
    proof (rule cmult_le_mono)
      have "gcard (elts X \<inter> elts \<alpha>) \<le> gcard (elts X)"
        by (rule subset_imp_gcard_le[OF Int_lower1 small_elts])
      thus "gcard (elts X \<inter> elts \<alpha>) \<le> Om v \<squnion> \<omega>" using leX by simp
      show "\<omega> \<le> Om v \<squnion> \<omega>" by simp
    qed
    also have "... = Om v \<squnion> \<omega>" by (simp add: InfCard_csquare_eq infk)
    finally show ?thesis .
  qed
  \<comment> \<open>combine: \<open>elts (Citer \<dots> (Suc n)) = ?A \<union> ?B \<union> ?C = \<Union>{?A,?B,?C}\<close>\<close>
  have eqset: "elts (Citer p \<alpha> v (Suc n)) = \<Union> {?A, ?B, ?C}"
    by (auto simp: X_def elts_Cstep)
  have gU: "gcard {?A, ?B, ?C} \<le> Om v \<squnion> \<omega>"
  proof -
    have fin: "finite {?A, ?B, ?C}" by simp
    have "gcard {?A, ?B, ?C} = ord_of_nat (card {?A, ?B, ?C})" by (rule gcard_eq_card[OF fin])
    also have "... \<le> \<omega>" by (simp add: ord_of_nat_le_omega)
    also have "\<omega> \<le> Om v \<squnion> \<omega>" by simp
    finally show ?thesis .
  qed
  have bound: "gcard (\<Union> {?A, ?B, ?C}) \<le> gcard {?A, ?B, ?C} \<otimes> (Om v \<squnion> \<omega>)"
  proof (rule gcard_Union_le_cmult')
    show "small {?A, ?B, ?C}" by simp
    show "gcard x \<le> Om v \<squnion> \<omega>" if "x \<in> {?A, ?B, ?C}" for x
      using that gA gB gC by blast
    show "small x" if "x \<in> {?A, ?B, ?C}" for x
      using that smX smB smC by blast
  qed
  have "vcard (Citer p \<alpha> v (Suc n)) = gcard (\<Union> {?A, ?B, ?C})"
    using eqset by (metis gcard_eq_vcard)
  also have "... \<le> gcard {?A, ?B, ?C} \<otimes> (Om v \<squnion> \<omega>)" by (rule bound)
  also have "... \<le> (Om v \<squnion> \<omega>) \<otimes> (Om v \<squnion> \<omega>)" by (rule cmult_le_mono[OF gU order_refl])
  also have "... = Om v \<squnion> \<omega>" by (simp add: InfCard_csquare_eq infk)
  finally show ?case .
qed

text \<open>Hence \<open>|C\<^sub>v(\<alpha>)| \<le> \<kappa>\<close> over the countable union.\<close>

lemma vcard_Cset_le: "vcard (Cset p \<alpha> v) \<le> Om v \<squnion> \<omega>"
proof -
  have infk: "InfCard (Om v \<squnion> \<omega>)" by (rule InfCard_Om_sup_omega)
  have sm: "small (range (\<lambda>n. Citer p \<alpha> v n))" by simp
  have "vcard (Cset p \<alpha> v) = vcard (\<Squnion> (range (\<lambda>n. Citer p \<alpha> v n)))"
    by (simp add: Cset_def)
  also have "... \<le> vcard (set (range (\<lambda>n. Citer p \<alpha> v n))) \<otimes> (Om v \<squnion> \<omega>)"
  proof (rule vcard_Sup_le_cmult[OF sm])
    show "vcard x \<le> Om v \<squnion> \<omega>" if "x \<in> range (\<lambda>n. Citer p \<alpha> v n)" for x
    proof -
      from that obtain n where "x = Citer p \<alpha> v n" by auto
      thus ?thesis by (simp add: vcard_Citer_le)
    qed
  qed
  also have "... \<le> (Om v \<squnion> \<omega>) \<otimes> (Om v \<squnion> \<omega>)"
  proof (rule cmult_le_mono[OF _ order_refl])
    have "vcard (set (range (\<lambda>n. Citer p \<alpha> v n))) = gcard (range (\<lambda>n. Citer p \<alpha> v n))"
      by (metis gcard_eq_vcard elts_of_set sm)
    also have "... \<le> gcard (UNIV::nat set)" by (rule gcard_image_le[OF small_nat_UNIV])
    also have "... = \<omega>" by (rule gcard_UNIV_nat)
    also have "\<omega> \<le> Om v \<squnion> \<omega>" by simp
    finally show "vcard (set (range (\<lambda>n. Citer p \<alpha> v n))) \<le> Om v \<squnion> \<omega>" .
  qed
  also have "... = Om v \<squnion> \<omega>" by (simp add: InfCard_csquare_eq infk)
  finally show ?thesis .
qed

text \<open>\<^bold>\<open>Buchholz Lemma 1.2(c)\<close>: \<open>\<psi>\<^sub>v(\<alpha>) < \<Omega>\<^bsub>v+1\<^esub>\<close>.  If not, then all ordinals below
  \<open>\<Omega>\<^bsub>v+1\<^esub>\<close> would lie in \<open>C\<^sub>v(\<alpha>)\<close>, forcing \<open>\<Omega>\<^bsub>v+1\<^esub> = |\<Omega>\<^bsub>v+1\<^esub>| \<le> |C\<^sub>v(\<alpha>)| \<le> \<kappa> < \<Omega>\<^bsub>v+1\<^esub>\<close>.\<close>

lemma one_le_Om: "(1::V) \<le> Om b"
proof -
  have "(0::V) < Om b"
  proof (cases "b = 0")
    case True thus ?thesis by (simp add: Om_def)
  next
    case False
    have "(0::V) < \<omega>" by (metis OrdmemD Ord_\<omega> zero_in_omega)
    also have "\<omega> \<le> Om b" using False by (simp add: Om_def)
    finally show ?thesis .
  qed
  hence "succ 0 \<le> Om b" by (simp add: succ_le_iff)
  thus ?thesis by (simp add: succ_eq_add1)
qed

lemma Om_mono: "a \<le> b \<Longrightarrow> Om a \<le> Om b"
proof (cases "a = 0")
  case True
  show ?thesis using one_le_Om by (simp add: True Om_def)
next
  case False
  assume ab: "a \<le> b"
  from False have apos: "0 < a" by simp
  with ab have bpos: "0 < b" by simp
  have "\<aleph>(ord_of_nat a) \<le> \<aleph>(ord_of_nat b)"
  proof (cases "a = b")
    case True thus ?thesis by simp
  next
    case False with ab have "ord_of_nat a < ord_of_nat b" by simp
    thus ?thesis by (simp add: Aleph_increasing less_imp_le)
  qed
  thus ?thesis using apos bpos by (simp add: Om_def)
qed

lemma psi_lt_Om_Suc: "psi \<alpha> v < Om (Suc v)"
proof (rule ccontr)
  assume "\<not> psi \<alpha> v < Om (Suc v)"
  hence ge: "Om (Suc v) \<le> psi \<alpha> v" using Ord_not_less[OF Ord_psi Ord_Om] by blast
  have allin: "elts (Om (Suc v)) \<subseteq> elts (Cset (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v)"
  proof
    fix \<delta> assume \<delta>: "\<delta> \<in> elts (Om (Suc v))"
    have od: "Ord \<delta>" using \<delta> Ord_Om Ord_in_Ord by blast
    have "\<delta> < Om (Suc v)" using \<delta> by (simp add: OrdmemD)
    hence ltp: "\<delta> < psi \<alpha> v" using ge by simp
    show "\<delta> \<in> elts (Cset (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v)"
    proof (rule ccontr)
      assume nin: "\<delta> \<notin> elts (Cset (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v)"
      have "(LEAST \<gamma>. Ord \<gamma> \<and> \<gamma> \<notin> elts (Cset (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v)) \<le> \<delta>"
        by (rule Ord_Least_le) (use od nin in auto)
      hence "psi \<alpha> v \<le> \<delta>" by (subst psi_unfold)
      with ltp show False by simp
    qed
  qed
  have "Om (Suc v) = vcard (Om (Suc v))" by (simp add: Card_cardinal_eq Card_Om_all)
  also have "... = gcard (elts (Om (Suc v)))" by (simp add: gcard_eq_vcard)
  also have "... \<le> gcard (elts (Cset (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v))"
    by (rule subset_imp_gcard_le[OF allin small_elts])
  also have "... = vcard (Cset (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v)" by (simp add: gcard_eq_vcard)
  also have "... \<le> Om v \<squnion> \<omega>" by (rule vcard_Cset_le)
  finally have "Om (Suc v) \<le> Om v \<squnion> \<omega>" .
  with kappa_less_Suc[of v] show False by (meson leD)
qed

text \<open>\<^bold>\<open>Subscript jump\<close>: a strictly larger subscript dominates regardless of arguments
  (\<open>\<psi>\<^sub>a(\<alpha>) < \<Omega>\<^bsub>a+1\<^esub> \<le> \<Omega>\<^sub>e \<le> \<psi>\<^sub>e(\<beta>)\<close>).  This is the engine of the subscript-first
  order (Buchholz Lemma 2.2(c), subscript case).\<close>

lemma psi_subscript_jump:
  assumes "a < e" shows "psi \<alpha> a < psi \<beta> e"
proof -
  have "psi \<alpha> a < Om (Suc a)" by (rule psi_lt_Om_Suc)
  also have "Om (Suc a) \<le> Om e" using assms by (simp add: Om_mono Suc_leI)
  also have "Om e \<le> psi \<beta> e" by (rule Om_le_psi)
  finally show ?thesis .
qed

subsection \<open>Additive-principal abstraction\<close>

text \<open>An ordinal \<open>\<delta>\<close> is additive principal when it is positive and a sum of two
  ordinals below it stays below it.  Each \<open>\<psi>\<^sub>v(\<alpha>)\<close> is additive principal
  (\<open>0 < \<Omega>\<^sub>v \<le> \<psi>\<^sub>v(\<alpha>)\<close> and Lemma 1.2(b)).\<close>

definition addprinc :: "V \<Rightarrow> bool" where
  "addprinc \<delta> \<longleftrightarrow> 0 < \<delta> \<and> (\<forall>\<beta> \<gamma>. Ord \<beta> \<longrightarrow> Ord \<gamma> \<longrightarrow> \<beta> < \<delta> \<longrightarrow> \<gamma> < \<delta> \<longrightarrow> \<beta> + \<gamma> < \<delta>)"

lemma psi_addprinc: "addprinc (psi \<alpha> v)"
  unfolding addprinc_def
proof
  have "0 < (1::V)" by simp
  also have "(1::V) \<le> Om v" by (rule one_le_Om)
  also have "Om v \<le> psi \<alpha> v" by (rule Om_le_psi)
  finally show "0 < psi \<alpha> v" .
next
  show "\<forall>\<beta> \<gamma>. Ord \<beta> \<longrightarrow> Ord \<gamma> \<longrightarrow> \<beta> < psi \<alpha> v \<longrightarrow> \<gamma> < psi \<alpha> v \<longrightarrow> \<beta> + \<gamma> < psi \<alpha> v"
    using psi_add_principal by blast
qed

end
