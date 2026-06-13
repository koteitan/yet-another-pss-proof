theory collapsing
  imports psi
begin

text \<open>\<^bold>\<open>Buchholz Lemma 1.6(a) (the collapsing step) on the ZFC-in-HOL ordinals.\<close>

  If \<open>\<alpha> \<notin> C\<^sub>v(\<alpha>)\<close> then \<open>\<psi>\<^sub>v(\<alpha>) = \<psi>\<^sub>v(\<alpha>+1)\<close>: at a non-canonical point the
  collapsing function is constant across the gap.  This is the ordinal-side core
  of the term-level \<open>psi_proj\<close> / collapsing lemma (the value preserved by the
  projection \<open>proj\<close>), the keystone of the \<open>nrm\<close> value route shared with lean-yapss.

  Self-contained in the \<open>\<psi>\<close>/\<open>C\<close> machinery of theory \<open>psi\<close> (no term side,
  no canonicity side-condition needed): we show \<open>C\<^sub>v(\<alpha>+1) = C\<^sub>v(\<alpha>)\<close> by an
  iterate induction \<dash> the only new generator at argument \<open>\<alpha>+1\<close> is \<open>\<psi>\<^sub>\<alpha>\<close>,
  which never fires because \<open>\<alpha>\<close> itself never enters the closure.\<close>

abbreviation (input) Cv :: "V \<Rightarrow> nat \<Rightarrow> V" where
  "Cv \<alpha> v \<equiv> Cset (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v"

text \<open>Under \<open>\<alpha> \<notin> C\<^sub>v(\<alpha>)\<close>, every iterate of the \<open>\<alpha>+1\<close> closure stays inside
  \<open>C\<^sub>v(\<alpha>)\<close> and avoids \<open>\<alpha>\<close>.  (Joint induction so the \<open>\<psi>\<^sub>\<alpha>\<close>-generator case can
  use that \<open>\<alpha>\<close> is absent from the previous iterate.)  The closure parameter is
  kept abstract (\<open>p\<close> agreeing with \<open>\<psi>\<close> below \<open>\<alpha>\<close>) to dodge \<open>restrict\<close>/\<open>elts (succ \<alpha>)\<close>
  normalization noise.\<close>

lemma Citer_succ_stays:
  assumes notin: "\<alpha> \<notin> elts (Cv \<alpha> v)"
    and pagree: "\<And>\<xi> u. \<xi> \<in> elts \<alpha> \<Longrightarrow> p \<xi> u = psi \<xi> u"
  shows "elts (Citer p (succ \<alpha>) v n) \<subseteq> elts (Cv \<alpha> v)
         \<and> \<alpha> \<notin> elts (Citer p (succ \<alpha>) v n)"
proof (induction n)
  case 0
  have c0: "elts (Citer p (succ \<alpha>) v 0) = elts (Om v)" by simp
  have om: "elts (Om v) \<subseteq> elts (Cv \<alpha> v)" by (rule Om_subset_Cset)
  show ?case unfolding c0 using om notin by blast
next
  case (Suc n)
  note IHsub = Suc.IH[THEN conjunct1] and IHna = Suc.IH[THEN conjunct2]
  have step: "elts (Citer p (succ \<alpha>) v (Suc n))
              = elts (Cstep p (succ \<alpha>) (Citer p (succ \<alpha>) v n))" by simp
  have "elts (Cstep p (succ \<alpha>) (Citer p (succ \<alpha>) v n)) \<subseteq> elts (Cv \<alpha> v)"
  proof (rule subsetI)
    fix x assume "x \<in> elts (Cstep p (succ \<alpha>) (Citer p (succ \<alpha>) v n))"
    then consider
        (old) "x \<in> elts (Citer p (succ \<alpha>) v n)"
      | (sum) \<xi> \<eta> where "\<xi> \<in> elts (Citer p (succ \<alpha>) v n)"
                         "\<eta> \<in> elts (Citer p (succ \<alpha>) v n)" "x = \<xi> + \<eta>"
      | (gen) \<xi> u where "\<xi> \<in> elts (Citer p (succ \<alpha>) v n)" "\<xi> \<in> elts (succ \<alpha>)"
                        "x = p \<xi> u"
      by (auto simp: elts_Cstep)
    thus "x \<in> elts (Cv \<alpha> v)"
    proof cases
      case old thus ?thesis using IHsub by blast
    next
      case sum
      have "\<xi> \<in> elts (Cv \<alpha> v)" "\<eta> \<in> elts (Cv \<alpha> v)" using sum(1,2) IHsub by blast+
      thus ?thesis using sum(3) Cset_add_closed by blast
    next
      case gen
      have xinC: "\<xi> \<in> elts (Cv \<alpha> v)" using gen(1) IHsub by blast
      have "\<xi> \<noteq> \<alpha>" using gen(1) IHna by blast
      hence xa: "\<xi> \<in> elts \<alpha>" using gen(2) by (auto simp: elts_succ)
      have "p \<xi> u = psi \<xi> u" by (rule pagree[OF xa])
      also have "psi \<xi> u = (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<xi> u" using xa by simp
      finally have "x = (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<xi> u" using gen(3) by simp
      thus ?thesis using Cset_psi_closed[OF xinC xa] by simp
    qed
  qed
  hence sub: "elts (Citer p (succ \<alpha>) v (Suc n)) \<subseteq> elts (Cv \<alpha> v)" using step by simp
  have "\<alpha> \<notin> elts (Citer p (succ \<alpha>) v (Suc n))" using sub notin by blast
  thus ?case using sub by blast
qed

lemma Cset_succ_eq:
  assumes "\<alpha> \<notin> elts (Cv \<alpha> v)"
  shows "elts (Cv (succ \<alpha>) v) = elts (Cv \<alpha> v)"
proof
  have pagree: "\<And>\<xi> u. \<xi> \<in> elts \<alpha> \<Longrightarrow> (\<lambda>\<xi>\<in>elts (succ \<alpha>). psi \<xi>) \<xi> u = psi \<xi> u"
    by (auto simp: elts_succ)
  show "elts (Cv (succ \<alpha>) v) \<subseteq> elts (Cv \<alpha> v)"
  proof (rule subsetI)
    fix x assume "x \<in> elts (Cv (succ \<alpha>) v)"
    then obtain n where "x \<in> elts (Citer (\<lambda>\<xi>\<in>elts (succ \<alpha>). psi \<xi>) (succ \<alpha>) v n)"
      by (auto simp: Cset_mem_iff)
    thus "x \<in> elts (Cv \<alpha> v)" using Citer_succ_stays[OF assms pagree] by blast
  qed
next
  show "elts (Cv \<alpha> v) \<subseteq> elts (Cv (succ \<alpha>) v)"
    by (rule CC_mono) (auto simp: less_eq_V_def)
qed

text \<open>\<open>\<psi>\<^sub>v\<close> depends only on the \<^emph>\<open>set\<close> \<open>C\<^sub>v(\<alpha>)\<close> (it is its least non-element), so
  equal \<open>C\<close>-sets give equal \<open>\<psi>\<close>-values.  Reusable bridge for every collapsing step.\<close>

lemma psi_eq_of_Cset_eq:
  assumes "elts (Cv \<alpha> v) = elts (Cv \<beta> v)"
  shows "psi \<alpha> v = psi \<beta> v"
  by (simp add: psi_unfold[of \<alpha> v] psi_unfold[of \<beta> v] assms)

theorem collapse_succ:
  assumes "\<alpha> \<notin> elts (Cv \<alpha> v)"
  shows "psi \<alpha> v = psi (succ \<alpha>) v"
  by (rule psi_eq_of_Cset_eq[OF Cset_succ_eq[OF assms, symmetric]])

end
