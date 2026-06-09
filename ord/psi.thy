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

end
