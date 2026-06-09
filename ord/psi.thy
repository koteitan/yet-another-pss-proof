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

end
