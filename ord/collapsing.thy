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

text \<open>\<^bold>\<open>General argument growth.\<close>  If every ordinal in the gap \<open>elts \<beta> \<setminus> elts \<alpha>\<close>
  is \<^emph>\<open>not\<close> in \<open>C\<^sub>v(\<alpha>)\<close>, then growing the argument from \<open>\<alpha>\<close> to \<open>\<beta>\<close> adds nothing:
  the extra \<open>\<psi>\<^sub>\<xi>\<close>-generators (gap subscripts) never fire because those \<open>\<xi>\<close> never
  enter the closure.  Every iterate of the \<open>\<beta>\<close>-closure stays inside \<open>C\<^sub>v(\<alpha>)\<close> and
  avoids the gap.  (Closure parameter \<open>p\<close> kept abstract to dodge \<open>restrict\<close> noise.)\<close>

lemma Citer_grow_stays:
  assumes gap: "\<And>\<xi>. \<xi> \<in> elts \<beta> \<Longrightarrow> \<xi> \<notin> elts \<alpha> \<Longrightarrow> \<xi> \<notin> elts (Cv \<alpha> v)"
    and pagree: "\<And>\<xi> u. \<xi> \<in> elts \<alpha> \<Longrightarrow> p \<xi> u = psi \<xi> u"
  shows "elts (Citer p \<beta> v n) \<subseteq> elts (Cv \<alpha> v)
         \<and> (\<forall>\<xi>\<in>elts \<beta>. \<xi> \<notin> elts \<alpha> \<longrightarrow> \<xi> \<notin> elts (Citer p \<beta> v n))"
proof (induction n)
  case 0
  have c0: "elts (Citer p \<beta> v 0) = elts (Om v)" by simp
  have om: "elts (Om v) \<subseteq> elts (Cv \<alpha> v)" by (rule Om_subset_Cset)
  show ?case unfolding c0 using om gap by blast
next
  case (Suc n)
  note IHsub = Suc.IH[THEN conjunct1] and IHgap = Suc.IH[THEN conjunct2]
  have step: "elts (Citer p \<beta> v (Suc n)) = elts (Cstep p \<beta> (Citer p \<beta> v n))" by simp
  have sub: "elts (Cstep p \<beta> (Citer p \<beta> v n)) \<subseteq> elts (Cv \<alpha> v)"
  proof (rule subsetI)
    fix x assume "x \<in> elts (Cstep p \<beta> (Citer p \<beta> v n))"
    then consider
        (old) "x \<in> elts (Citer p \<beta> v n)"
      | (sum) \<xi> \<eta> where "\<xi> \<in> elts (Citer p \<beta> v n)" "\<eta> \<in> elts (Citer p \<beta> v n)" "x = \<xi> + \<eta>"
      | (gen) \<xi> u where "\<xi> \<in> elts (Citer p \<beta> v n)" "\<xi> \<in> elts \<beta>" "x = p \<xi> u"
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
      have xa: "\<xi> \<in> elts \<alpha>" using gen(1,2) IHgap by blast
      have "p \<xi> u = psi \<xi> u" by (rule pagree[OF xa])
      also have "psi \<xi> u = (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<xi> u" using xa by simp
      finally have "x = (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<xi> u" using gen(3) by simp
      thus ?thesis using Cset_psi_closed[OF xinC xa] by simp
    qed
  qed
  hence subS: "elts (Citer p \<beta> v (Suc n)) \<subseteq> elts (Cv \<alpha> v)" using step by simp
  have "\<forall>\<xi>\<in>elts \<beta>. \<xi> \<notin> elts \<alpha> \<longrightarrow> \<xi> \<notin> elts (Citer p \<beta> v (Suc n))"
    using subS gap by blast
  thus ?case using subS by blast
qed

lemma Cset_grow_eq:
  assumes gap: "\<And>\<xi>. \<xi> \<in> elts \<beta> \<Longrightarrow> \<xi> \<notin> elts \<alpha> \<Longrightarrow> \<xi> \<notin> elts (Cv \<alpha> v)"
    and le: "elts \<alpha> \<subseteq> elts \<beta>"
  shows "elts (Cv \<beta> v) = elts (Cv \<alpha> v)"
proof
  have pagree: "\<And>\<xi> u. \<xi> \<in> elts \<alpha> \<Longrightarrow> (\<lambda>\<xi>\<in>elts \<beta>. psi \<xi>) \<xi> u = psi \<xi> u"
    using le by auto
  show "elts (Cv \<beta> v) \<subseteq> elts (Cv \<alpha> v)"
  proof (rule subsetI)
    fix x assume "x \<in> elts (Cv \<beta> v)"
    then obtain n where "x \<in> elts (Citer (\<lambda>\<xi>\<in>elts \<beta>. psi \<xi>) \<beta> v n)"
      by (auto simp: Cset_mem_iff)
    thus "x \<in> elts (Cv \<alpha> v)" using Citer_grow_stays[OF gap pagree] by blast
  qed
next
  show "elts (Cv \<alpha> v) \<subseteq> elts (Cv \<beta> v)"
    by (rule Cset_mono_param) (use le in \<open>auto simp: subsetD\<close>)
qed

text \<open>The successor case (\<open>\<beta> = \<alpha>+1\<close>, gap \<open>= {\<alpha>}\<close>) is the original Lemma 1.6(a).\<close>

lemma Cset_succ_eq:
  assumes "\<alpha> \<notin> elts (Cv \<alpha> v)"
  shows "elts (Cv (succ \<alpha>) v) = elts (Cv \<alpha> v)"
proof (rule Cset_grow_eq)
  show "\<And>\<xi>. \<xi> \<in> elts (succ \<alpha>) \<Longrightarrow> \<xi> \<notin> elts \<alpha> \<Longrightarrow> \<xi> \<notin> elts (Cv \<alpha> v)"
    using assms by (auto simp: elts_succ)
  show "elts \<alpha> \<subseteq> elts (succ \<alpha>)" by (auto simp: elts_succ)
qed

text \<open>\<open>\<psi>\<^sub>v\<close> depends only on the \<^emph>\<open>set\<close> \<open>C\<^sub>v(\<alpha>)\<close> (it is its least non-element), so
  equal \<open>C\<close>-sets give equal \<open>\<psi>\<close>-values.  Reusable bridge for every collapsing step.\<close>

lemma psi_eq_of_Cset_eq:
  assumes "elts (Cv \<alpha> v) = elts (Cv \<beta> v)"
  shows "psi \<alpha> v = psi \<beta> v"
  by (simp add: psi_unfold[of \<alpha> v] psi_unfold[of \<beta> v] assms)

text \<open>\<^bold>\<open>General collapsing\<close>: if the whole gap up to \<open>\<beta>\<close> is non-canonical
  (absent from \<open>C\<^sub>v(\<alpha>)\<close>), then \<open>\<psi>\<^sub>v\<close> is constant from \<open>\<alpha>\<close> to \<open>\<beta>\<close>.  This is the
  argument-side collapse the term-level \<open>psi_proj\<close> needs (\<open>proj\<close> grows the value
  \<open>oV b \<le> oV(proj a b)\<close> across a non-canonical gap).\<close>

theorem collapse_grow:
  assumes "\<And>\<xi>. \<xi> \<in> elts \<beta> \<Longrightarrow> \<xi> \<notin> elts \<alpha> \<Longrightarrow> \<xi> \<notin> elts (Cv \<alpha> v)"
    and "elts \<alpha> \<subseteq> elts \<beta>"
  shows "psi \<alpha> v = psi \<beta> v"
  by (rule psi_eq_of_Cset_eq[OF Cset_grow_eq[OF assms, symmetric]])

theorem collapse_succ:
  assumes "\<alpha> \<notin> elts (Cv \<alpha> v)"
  shows "psi \<alpha> v = psi (succ \<alpha>) v"
  by (rule psi_eq_of_Cset_eq[OF Cset_succ_eq[OF assms, symmetric]])

end
