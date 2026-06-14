theory necessity
  imports otembed collapsing "ZFC_in_HOL.Cantor_NF"
begin

text \<open>\<^bold>\<open>Toward Buchholz Lemma 1.9 necessity\<close> (the converse of \<open>C_build\<close>):
  \<open>o t \<in> C\<^sub>v(\<alpha>) \<Longrightarrow> \<forall>x \<in> G\<^sub>v t. o x < \<alpha>\<close>.  This is the missing direction that
  triggers the term-level collapse (\<open>psi_proj\<close>): a principal whose argument has a
  coefficient \<open>\<ge>\<close> itself is non-canonical, so \<open>\<psi>\<close> collapses it.

  Decomposition (cf. lean-yapss advice-reply): necessity follows from
  (A) leading additive-principal (\<^const>\<open>indecomposable\<close>) component extraction from
      \<open>C\<close>-elements, and
  (B) the \<open>\<psi>\<close>-argument necessity \<open>\<psi>\<^bsub>a\<^esub>(\<beta>) \<in> C\<^sub>v(\<alpha>) \<Longrightarrow> \<beta> < \<alpha>\<close> (needs \<open>\<psi>\<close> injectivity,
      Buchholz 1.4(a)).

  Bridge below: every \<open>\<psi>\<close>-value is \<^const>\<open>indecomposable\<close> (Cantor-NF additive
  principal), giving access to the \<^theory>\<open>ZFC_in_HOL.Cantor_NF\<close> toolkit.\<close>

text \<open>\<^bold>\<open>The \<open>n\<close>-copies bound\<close> (heart of \<open>oper\<close> termination): an ordinal strictly
  below an \<^const>\<open>indecomposable\<close> (additive-principal) ordinal stays below it after
  multiplication by any finite \<open>n\<close>.  This is why expanding a block into \<open>n\<close> shifted
  copies strictly decreases the value: \<open>\<psi>\<^bsub>a\<^esub>(\<beta>)\<cdot>n < \<psi>\<^bsub>a\<^esub>(\<beta>+1)\<close> (\<open>indec_psi_mult\<close>).\<close>

lemma indec_mult_nat:
  assumes "indecomposable \<gamma>" "Ord \<alpha>" "\<alpha> < \<gamma>"
  shows "\<alpha> * ord_of_nat n < \<gamma>"
proof (induction n)
  case 0
  have "\<alpha> * ord_of_nat 0 = 0" by simp
  moreover have "(0::V) < \<gamma>" using le_less_trans[OF le_0 assms(3)] .
  ultimately show ?case by simp
next
  case (Suc n)
  have ob: "Ord (\<alpha> * ord_of_nat n)" using assms(2) by simp
  have "\<alpha> * ord_of_nat (Suc n) = \<alpha> * ord_of_nat n + \<alpha>"
    by (simp add: mult_succ)
  moreover have "\<alpha> * ord_of_nat n + \<alpha> < \<gamma>"
    by (rule indecomposableD[OF assms(1) Suc.IH assms(3) ob assms(2)])
  ultimately show ?case by simp
qed

subsection \<open>The \<open>a\<close>-canonical predicate (toward Buchholz \<section>1 canonical reps)\<close>

text \<open>\<open>acanon a \<delta>\<close>: \<open>\<delta>\<close> is its own \<open>a\<close>-coefficient-closure point, i.e. \<open>\<delta> \<in> C\<^bsub>a\<^esub>(\<delta>)\<close>.
  These are the arguments on which \<open>\<psi>\<^bsub>a\<^esub>\<close> is strictly monotone (1.3) and injective
  (1.4(a)); every value collapses to such a canonical argument (the \<section>1 core).\<close>

definition acanon :: "nat \<Rightarrow> V \<Rightarrow> bool" where
  "acanon a \<delta> \<longleftrightarrow> \<delta> \<in> elts (Cset (\<lambda>\<xi>\<in>elts \<delta>. psi \<xi>) \<delta> a)"

text \<open>Everything strictly below its own \<open>\<psi>\<close>-value is canonical (it lies in \<open>C\<close> as a
  sub-\<open>\<psi>\<close> ordinal); contrapositively, a non-canonical argument is \<open>\<ge>\<close> its value.\<close>

lemma acanon_of_lt_psi: "Ord \<delta> \<Longrightarrow> \<delta> < psi \<delta> a \<Longrightarrow> acanon a \<delta>"
  unfolding acanon_def by (rule below_psi_in_Cset)

lemma psi_le_of_not_acanon:
  assumes "Ord \<delta>" "\<not> acanon a \<delta>" shows "psi \<delta> a \<le> \<delta>"
proof (rule ccontr)
  assume "\<not> psi \<delta> a \<le> \<delta>"
  hence "\<delta> < psi \<delta> a" using Ord_not_le[OF Ord_psi[of \<delta> a] assms(1)] by simp
  from acanon_of_lt_psi[OF assms(1) this] assms(2) show False by simp
qed

text \<open>\<^bold>\<open>Subscript injectivity\<close> (part of Buchholz 1.4(a)): the subscript of a
  \<open>\<psi>\<close>-value is determined by the value, because \<open>\<psi>\<^bsub>v\<^esub>(\<alpha>) \<in> [\<Omega>\<^bsub>v\<^esub>, \<Omega>\<^bsub>v+1\<^esub>)\<close> and these
  ranges are disjoint for distinct \<open>v\<close>.\<close>

lemma psi_inj_subscript:
  assumes "psi \<alpha> v = psi \<beta> w" shows "v = w"
proof (rule ccontr)
  assume "v \<noteq> w"
  then consider (lt) "v < w" | (gt) "w < v" by linarith
  thus False
  proof cases
    case lt
    have "psi \<alpha> v < Om (Suc v)" by (rule psi_lt_Om_Suc)
    also have "Om (Suc v) \<le> Om w" using lt by (simp add: Om_mono Suc_leI)
    also have "Om w \<le> psi \<beta> w" by (rule Om_le_psi)
    finally show False using assms by simp
  next
    case gt
    have "psi \<beta> w < Om (Suc w)" by (rule psi_lt_Om_Suc)
    also have "Om (Suc w) \<le> Om v" using gt by (simp add: Om_mono Suc_leI)
    also have "Om v \<le> psi \<alpha> v" by (rule Om_le_psi)
    finally show False using assms by simp
  qed
qed

lemma indecomposable_psi: "indecomposable (psi \<alpha> v)"
proof -
  have pos: "0 < psi \<alpha> v" using psi_addprinc[of \<alpha> v] by (simp add: addprinc_def)
  have "\<beta> + \<gamma> \<in> elts (psi \<alpha> v)" if "\<beta> \<in> elts (psi \<alpha> v)" "\<gamma> \<in> elts (psi \<alpha> v)" for \<beta> \<gamma>
  proof -
    have ob: "Ord \<beta>" using that(1) Ord_psi Ord_in_Ord by blast
    have og: "Ord \<gamma>" using that(2) Ord_psi Ord_in_Ord by blast
    have "\<beta> < psi \<alpha> v" using that(1) Ord_mem_iff_lt[OF ob Ord_psi] by blast
    moreover have "\<gamma> < psi \<alpha> v" using that(2) Ord_mem_iff_lt[OF og Ord_psi] by blast
    ultimately have "\<beta> + \<gamma> < psi \<alpha> v"
      using psi_addprinc[of \<alpha> v] ob og unfolding addprinc_def by blast
    thus ?thesis using Ord_mem_iff_lt[OF Ord_add[OF ob og] Ord_psi] by blast
  qed
  thus ?thesis unfolding indecomposable_def using Ord_psi by blast
qed

text \<open>\<^bold>\<open>Indecomposable elements of the closure are generators\<close>.  An additively
  indecomposable ordinal \<open>\<gamma> \<ge> \<Omega>\<^sub>v\<close> that lies in \<open>C\<^sub>v(\<alpha>)\<close> cannot be a proper sum
  (indecomposability) nor an element of \<open>\<Omega>\<^sub>v\<close>, so it must have entered as a
  \<^emph>\<open>generator\<close> \<open>p \<xi> u\<close> with \<open>\<xi> \<in> C\<^sub>v(\<alpha>) \<inter> \<alpha>\<close>.  This is the structural half of
  Buchholz 1.9 (the part that does \<^emph>\<open>not\<close> need the simultaneous induction): it
  reduces \<open>\<psi>\<^bsub>a\<^esub>(\<beta>) \<in> C\<^sub>v(\<alpha>)\<close> to "\<open>\<psi>\<^bsub>a\<^esub>(\<beta>)\<close> is a generator value", and then
  \<open>psi_inj_subscript\<close> pins the subscript.  Proof by induction on the closure rank
  (\<open>Citer\<close> index): a fresh sum \<open>\<xi>+\<eta>=\<gamma>\<close> forces \<open>\<xi>=\<gamma>\<close> or \<open>\<eta>=\<gamma>\<close>, dropping to a lower
  rank (handled by IH); a fresh generator is the witness.\<close>

lemma indec_Cset_generator:
  assumes ordp: "\<And>\<xi> u. \<xi> \<in> elts \<alpha> \<Longrightarrow> Ord (p \<xi> u)"
    and indec: "indecomposable \<gamma>" and notOm: "\<gamma> \<notin> elts (Om v)"
    and mem: "\<gamma> \<in> elts (Cset p \<alpha> v)"
  shows "\<exists>\<xi> u. \<xi> \<in> elts (Cset p \<alpha> v) \<and> \<xi> \<in> elts \<alpha> \<and> \<gamma> = p \<xi> u"
proof -
  have ordp': "\<forall>\<xi> u. \<xi> \<in> elts \<alpha> \<longrightarrow> Ord (p \<xi> u)" using ordp by blast
  from mem obtain N where "\<gamma> \<in> elts (Citer p \<alpha> v N)" by (auto simp: Cset_mem_iff)
  thus ?thesis
  proof (induction N)
    case 0
    hence "\<gamma> \<in> elts (Om v)" by simp
    with notOm show ?case by blast
  next
    case (Suc n)
    from Suc.prems have "\<gamma> \<in> elts (Cstep p \<alpha> (Citer p \<alpha> v n))" by simp
    then consider "\<gamma> \<in> elts (Citer p \<alpha> v n)"
      | \<xi> \<eta> where "\<xi> \<in> elts (Citer p \<alpha> v n)" "\<eta> \<in> elts (Citer p \<alpha> v n)" "\<gamma> = \<xi> + \<eta>"
      | \<xi> u where "\<xi> \<in> elts (Citer p \<alpha> v n)" "\<xi> \<in> elts \<alpha>" "\<gamma> = p \<xi> u"
      by (auto simp: elts_Cstep)
    thus ?case
    proof cases
      case 1 thus ?thesis by (rule Suc.IH)
    next
      case 2
      have o\<xi>: "Ord \<xi>" by (rule Ord_Citer[OF ordp' 2(1)])
      have o\<eta>: "Ord \<eta>" by (rule Ord_Citer[OF ordp' 2(2)])
      have le\<xi>: "\<xi> \<le> \<gamma>" using 2(3) add_le_cancel_left0 by simp
      have le\<eta>: "\<eta> \<le> \<gamma>" using 2(3) add_le_left[OF o\<xi> o\<eta>] by simp
      have "\<not> (\<xi> < \<gamma> \<and> \<eta> < \<gamma>)"
      proof
        assume "\<xi> < \<gamma> \<and> \<eta> < \<gamma>"
        hence "\<xi> + \<eta> < \<gamma>" using indecomposableD[OF indec _ _ o\<xi> o\<eta>] by blast
        thus False using 2(3) by simp
      qed
      hence "\<gamma> = \<xi> \<or> \<gamma> = \<eta>" using le\<xi> le\<eta> by (auto simp: less_V_def)
      hence "\<gamma> \<in> elts (Citer p \<alpha> v n)" using 2(1,2) by auto
      thus ?thesis by (rule Suc.IH)
    next
      case 3
      have "\<xi> \<in> elts (Cset p \<alpha> v)" using 3(1) Citer_in_Cset by blast
      thus ?thesis using 3(2,3) by blast
    qed
  qed
qed

text \<open>\<^bold>\<open>The \<open>\<Omega>\<^bsub>a+1\<^esub>\<close>-band lemma\<close> (the geometric heart of the argument-side collapse):
  every element of \<open>C\<^sub>a(\<delta>)\<close> that lies in the \<open>\<psi>\<^sub>a\<close>-band \<open>[\<Omega>\<^sub>a, \<Omega>\<^bsub>a+1\<^esub>)\<close> is in fact
  \<open>< \<psi>\<^sub>a(\<delta>)\<close>.  Reason: a generator \<open>\<psi>\<^sub>u(\<xi>)\<close> with \<open>u>a\<close> is \<open>\<ge> \<Omega>\<^bsub>a+1\<^esub>\<close> (out of band),
  with \<open>u<a\<close> is \<open>< \<Omega>\<^sub>a \<le> \<psi>\<^sub>a(\<delta>)\<close>, and with \<open>u=a\<close> uses \<open>\<xi> < \<delta>\<close> so
  \<open>\<psi>\<^sub>a(\<xi>) \<le> \<psi>\<^sub>a(\<delta>)\<close> (weak monotonicity) and \<open>\<noteq>\<close> (else \<open>\<psi>\<^sub>a(\<delta>)\<close> would be a member,
  contradicting \<open>psi_notin\<close>); sums stay below by additive principality.  \<^bold>\<open>No
  necessity / simultaneous induction needed.\<close>  This is what makes the gap
  \<open>[\<psi>\<^sub>a(\<delta>)\<dots>)\<close> clean for \<open>collapse_grow\<close> once \<open>\<delta>\<close> is known non-canonical.\<close>

lemma band_lt_psi:
  assumes "Ord \<delta>"
    and "x \<in> elts (Cset (\<lambda>\<xi>\<in>elts \<delta>. psi \<xi>) \<delta> a)"
    and "x < Om (Suc a)"
  shows "x < psi \<delta> a"
proof -
  let ?p = "\<lambda>\<xi>\<in>elts \<delta>. psi \<xi>"
  have ordp': "\<forall>\<xi> u. \<xi> \<in> elts \<delta> \<longrightarrow> Ord (?p \<xi> u)" by simp
  have key: "x \<in> elts (Citer ?p \<delta> a N) \<Longrightarrow> x < Om (Suc a) \<Longrightarrow> x < psi \<delta> a" for N x
  proof (induction N arbitrary: x)
    case 0
    hence "x \<in> elts (Om a)" by simp
    hence "x < Om a" by (rule OrdmemD[OF Ord_Om])
    also have "Om a \<le> psi \<delta> a" by (rule Om_le_psi)
    finally show ?case .
  next
    case (Suc n)
    from Suc.prems(1) have "x \<in> elts (Cstep ?p \<delta> (Citer ?p \<delta> a n))"
      by (simp only: funpow.simps(2) comp_apply)
    then consider "x \<in> elts (Citer ?p \<delta> a n)"
      | \<xi> \<eta> where "\<xi> \<in> elts (Citer ?p \<delta> a n)" "\<eta> \<in> elts (Citer ?p \<delta> a n)" "x = \<xi> + \<eta>"
      | \<xi> u where "\<xi> \<in> elts (Citer ?p \<delta> a n)" "\<xi> \<in> elts \<delta>" "x = ?p \<xi> u"
      by (auto simp: elts_Cstep)
    thus ?case
    proof cases
      case 1 thus ?thesis using Suc.IH Suc.prems(2) by blast
    next
      case 2
      have o\<xi>: "Ord \<xi>" by (rule Ord_Citer[OF ordp' 2(1)])
      have o\<eta>: "Ord \<eta>" by (rule Ord_Citer[OF ordp' 2(2)])
      have "\<xi> \<le> x" using 2(3) add_le_cancel_left0 by simp
      hence lx\<xi>: "\<xi> < Om (Suc a)" using Suc.prems(2) by simp
      have "\<eta> \<le> x" using 2(3) add_le_left[OF o\<xi> o\<eta>] by simp
      hence lx\<eta>: "\<eta> < Om (Suc a)" using Suc.prems(2) by simp
      have lt\<xi>: "\<xi> < psi \<delta> a" by (rule Suc.IH[OF 2(1) lx\<xi>])
      have lt\<eta>: "\<eta> < psi \<delta> a" by (rule Suc.IH[OF 2(2) lx\<eta>])
      have "\<xi> + \<eta> < psi \<delta> a"
        by (rule indecomposableD[OF indecomposable_psi lt\<xi> lt\<eta> o\<xi> o\<eta>])
      thus ?thesis using 2(3) by simp
    next
      case 3
      have val: "x = psi \<xi> u" using 3(2,3) by simp
      consider (lt) "u < a" | (eq) "u = a" | (gt) "a < u" by linarith
      thus ?thesis
      proof cases
        case lt
        have "psi \<xi> u < Om (Suc u)" by (rule psi_lt_Om_Suc)
        also have "Om (Suc u) \<le> Om a" using lt by (simp add: Om_mono Suc_leI)
        also have "Om a \<le> psi \<delta> a" by (rule Om_le_psi)
        finally show ?thesis using val by simp
      next
        case eq
        have "\<xi> < \<delta>" by (rule OrdmemD[OF assms(1) 3(2)])
        hence "psi \<xi> a \<le> psi \<delta> a" using psi_mono_arg[of \<xi> \<delta> a] by simp
        moreover have "psi \<xi> a \<noteq> psi \<delta> a"
        proof
          assume *: "psi \<xi> a = psi \<delta> a"
          have "x \<in> elts (Cset ?p \<delta> a)" using Suc.prems(1) Citer_in_Cset by blast
          hence "psi \<delta> a \<in> elts (Cset ?p \<delta> a)" using val eq * by simp
          thus False using psi_notin by simp
        qed
        ultimately have "psi \<xi> a < psi \<delta> a" by simp
        thus ?thesis using val eq by simp
      next
        case gt
        have "Om (Suc a) \<le> Om u" using gt by (simp add: Om_mono Suc_leI)
        also have "Om u \<le> psi \<xi> u" by (rule Om_le_psi)
        finally have "Om (Suc a) \<le> psi \<xi> u" .
        with val Suc.prems(2) show ?thesis by simp
      qed
    qed
  qed
  from assms(2) obtain N where "x \<in> elts (Citer ?p \<delta> a N)" by (auto simp: Cset_mem_iff)
  thus ?thesis using key assms(3) by blast
qed

text \<open>\<^bold>\<open>Same-subscript specialization\<close>: a \<open>\<psi>\<close>-value \<open>\<psi>\<^sub>v(\<beta>)\<close> lying in \<open>C\<^sub>v(\<alpha>)\<close>
  (\<^emph>\<open>same\<close> subscript \<open>v\<close> as the closure) is necessarily a generator value
  \<open>\<psi>\<^sub>v(\<xi>) = \<psi>\<^sub>v(\<beta>)\<close> for some closure argument \<open>\<xi> \<in> C\<^sub>v(\<alpha>) \<inter> \<alpha>\<close>.  Combines
  \<open>indec_Cset_generator\<close> (\<open>\<psi>\<close>-values are indecomposable and \<open>\<ge> \<Omega>\<^sub>v\<close>) with
  \<open>psi_inj_subscript\<close> (the generator's subscript is forced to be \<open>v\<close>).  This is
  the step that feeds the necessity argument: the producing argument \<open>\<xi>\<close> is
  \<open>< \<alpha>\<close>, and \<open>\<psi>\<^sub>v\<close> is constant from \<open>\<xi>\<close> to \<open>\<beta>\<close>.\<close>

lemma psi_in_Cset_same_sub_generator:
  assumes "psi \<beta> v \<in> elts (Cset (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v)"
  shows "\<exists>\<xi>. \<xi> \<in> elts (Cset (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v) \<and> \<xi> \<in> elts \<alpha> \<and> psi \<xi> v = psi \<beta> v"
proof -
  have ordp: "\<And>\<xi> u. \<xi> \<in> elts \<alpha> \<Longrightarrow> Ord ((\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<xi> u)" by simp
  have notOm: "psi \<beta> v \<notin> elts (Om v)"
  proof
    assume "psi \<beta> v \<in> elts (Om v)"
    hence "psi \<beta> v < Om v" using Ord_mem_iff_lt[OF Ord_psi Ord_Om] by blast
    moreover have "Om v \<le> psi \<beta> v" by (rule Om_le_psi)
    ultimately show False by simp
  qed
  from indec_Cset_generator[OF ordp indecomposable_psi notOm assms]
  obtain \<xi> u where \<xi>: "\<xi> \<in> elts (Cset (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v)"
    "\<xi> \<in> elts \<alpha>" "psi \<beta> v = (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<xi> u" by blast
  have val: "psi \<beta> v = psi \<xi> u" using \<xi>(2,3) by simp
  have "v = u" by (rule psi_inj_subscript[OF val])
  with val have "psi \<xi> v = psi \<beta> v" by simp
  with \<xi>(1,2) show ?thesis by blast
qed

text \<open>\<^bold>\<open>Argument injectivity on canonical arguments\<close> (the rest of Buchholz 1.4(a)):
  for canonical \<open>\<alpha>,\<beta>\<close> (\<open>\<alpha> \<in> C\<^bsub>v\<^esub>(\<alpha>)\<close>), equal \<open>\<psi>\<close>-values force equal arguments, by
  strict monotonicity 1.3.\<close>

lemma psi_inj_arg_canonical:
  assumes "Ord \<alpha>" "Ord \<beta>"
    and "\<alpha> \<in> elts (Cset (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v)"
    and "\<beta> \<in> elts (Cset (\<lambda>\<xi>\<in>elts \<beta>. psi \<xi>) \<beta> v)"
    and "psi \<alpha> v = psi \<beta> v"
  shows "\<alpha> = \<beta>"
proof (rule ccontr)
  assume "\<alpha> \<noteq> \<beta>"
  then consider (lt) "\<alpha> < \<beta>" | (gt) "\<beta> < \<alpha>"
    using assms(1,2) Ord_linear_lt by blast
  thus False
  proof cases
    case lt
    have "psi \<alpha> v < psi \<beta> v" by (rule psi_strict_mono_arg[OF assms(1,2) lt assms(3)])
    thus False using assms(5) by simp
  next
    case gt
    have "psi \<beta> v < psi \<alpha> v" by (rule psi_strict_mono_arg[OF assms(2,1) gt assms(4)])
    thus False using assms(5) by simp
  qed
qed

text \<open>\<^bold>\<open>Buchholz 1.4(a)\<close>: on canonical arguments, \<open>\<psi>\<close> is injective in both subscript
  and argument.\<close>

theorem psi_inj_canonical:
  assumes "Ord \<alpha>" "Ord \<beta>"
    and "\<alpha> \<in> elts (Cset (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v)"
    and "\<beta> \<in> elts (Cset (\<lambda>\<xi>\<in>elts \<beta>. psi \<xi>) \<beta> w)"
    and "psi \<alpha> v = psi \<beta> w"
  shows "v = w \<and> \<alpha> = \<beta>"
proof
  show vw: "v = w" by (rule psi_inj_subscript[OF assms(5)])
  show "\<alpha> = \<beta>"
  proof (rule psi_inj_arg_canonical[OF assms(1,2)])
    show "\<alpha> \<in> elts (Cset (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> w)" using assms(3) vw by simp
    show "\<beta> \<in> elts (Cset (\<lambda>\<xi>\<in>elts \<beta>. psi \<xi>) \<beta> w)" by (rule assms(4))
    show "psi \<alpha> w = psi \<beta> w" using assms(5) vw by simp
  qed
qed

text \<open>The \<open>n\<close>-copies decrease for \<open>\<psi>\<close>: \<open>n\<close> copies of the \<open>\<beta>\<close>-block stay below the
  \<open>(\<beta>+1)\<close>-nest, when \<open>\<beta>\<close> is canonical (\<open>\<beta> \<in> C\<^bsub>v\<^esub>(\<beta>)\<close>, giving strict monotonicity 1.3).\<close>

lemma indec_psi_mult:
  assumes "Ord \<beta>" and "\<beta> \<in> elts (Cset (\<lambda>\<xi>\<in>elts \<beta>. psi \<xi>) \<beta> v)"
  shows "psi \<beta> v * ord_of_nat n < psi (succ \<beta>) v"
proof -
  have lt: "\<beta> < succ \<beta>"
    using assms(1) Ord_mem_iff_lt[OF assms(1) Ord_succ[OF assms(1)]] by (simp add: elts_succ)
  have "psi \<beta> v < psi (succ \<beta>) v"
    by (rule psi_strict_mono_arg[OF assms(1) Ord_succ[OF assms(1)] lt assms(2)])
  thus ?thesis using indec_mult_nat[OF indecomposable_psi Ord_psi] by blast
qed

text \<open>\<open>n\<close> copies plus a smaller remainder still stay below the \<open>(\<beta>+1)\<close>-nest
  (the remainder is the prefix/tail contribution in the \<open>oper\<close> step).\<close>

lemma indec_psi_mult_add:
  assumes "Ord \<beta>" and "\<beta> \<in> elts (Cset (\<lambda>\<xi>\<in>elts \<beta>. psi \<xi>) \<beta> v)"
    and "Ord \<delta>" and "\<delta> < psi (succ \<beta>) v"
  shows "psi \<beta> v * ord_of_nat n + \<delta> < psi (succ \<beta>) v"
proof (rule indecomposableD[OF indecomposable_psi _ assms(4) _ assms(3)])
  show "psi \<beta> v * ord_of_nat n < psi (succ \<beta>) v" by (rule indec_psi_mult[OF assms(1,2)])
  show "Ord (psi \<beta> v * ord_of_nat n)" by simp
qed

subsection \<open>Canonical-generator closure \<open>C\<^sup>c\<close> (Buchholz's side-condition (*), toward D-eq)\<close>

text \<open>\<open>Cstep_c\<close>/\<open>Cset_c\<close> mirror \<open>Cstep\<close>/\<open>Cset\<close> but \<^emph>\<open>restrict the generator step\<close> to
  \<^bold>\<open>canonical\<close> arguments \<open>\<xi> \<in> C\<^bsub>u\<^esub>(\<xi>)\<close> (\<^const>\<open>acanon\<close> \<open>u \<xi>\<close>) \<dash> exactly Buchholz's (*).
  The aim (Buchholz's Remark / plan group D-eq) is \<open>Cset_c = Cset\<close>: non-canonical
  generators are redundant.  Here we set up the definition and the \<^emph>\<open>easy\<close>
  inclusion \<open>Cset_c \<subseteq> Cset\<close>; the reverse (the \<section>1 core) is the simultaneous
  induction.  \<^const>\<open>acanon\<close> is kept folded throughout (no \<open>auto\<close>/\<open>simp\<close> exposure).\<close>

definition Cstep_c :: "(V \<Rightarrow> nat \<Rightarrow> V) \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V" where
  "Cstep_c p \<alpha> X =
     X \<squnion> ZFC_in_HOL.set ((\<lambda>(\<xi>,\<eta>). \<xi> + \<eta>) ` (elts X \<times> elts X))
       \<squnion> ZFC_in_HOL.set ((\<lambda>(\<xi>,u). p \<xi> u)
                 ` {q \<in> (elts X \<inter> elts \<alpha>) \<times> (UNIV::nat set). acanon (snd q) (fst q)})"

lemma small_Cstep_c_gen:
  "small ((\<lambda>(\<xi>,u::nat). p \<xi> u)
            ` {q \<in> (elts X \<inter> elts \<alpha>) \<times> (UNIV::nat set). acanon (snd q) (fst q)})"
proof -
  have nat: "small (UNIV::nat set)" using small_image_nat[of "\<lambda>x. x" UNIV] by simp
  have "small (elts X \<inter> elts \<alpha>)" using smaller_than_small[OF small_elts Int_lower1] .
  from small_Times[OF this nat] have sp: "small ((elts X \<inter> elts \<alpha>) \<times> (UNIV::nat set))" .
  have sub: "{q \<in> (elts X \<inter> elts \<alpha>) \<times> (UNIV::nat set). acanon (snd q) (fst q)}
               \<subseteq> (elts X \<inter> elts \<alpha>) \<times> UNIV" by blast
  have "small {q \<in> (elts X \<inter> elts \<alpha>) \<times> (UNIV::nat set). acanon (snd q) (fst q)}"
    using smaller_than_small[OF sp sub] .
  thus ?thesis using replacement[where f="\<lambda>(\<xi>,u::nat). p \<xi> u"] by blast
qed

lemma elts_Cstep_c:
  "elts (Cstep_c p \<alpha> X) = elts X
     \<union> (\<lambda>(\<xi>,\<eta>). \<xi> + \<eta>) ` (elts X \<times> elts X)
     \<union> (\<lambda>(\<xi>,u). p \<xi> u) ` {q \<in> (elts X \<inter> elts \<alpha>) \<times> (UNIV::nat set). acanon (snd q) (fst q)}"
  unfolding Cstep_c_def by (simp add: small_Cstep_images(1) small_Cstep_c_gen)

lemma Cstep_c_subset_Cstep: "elts (Cstep_c p \<alpha> X) \<subseteq> elts (Cstep p \<alpha> X)"
  by (auto simp: elts_Cstep_c elts_Cstep)

definition Cset_c :: "(V \<Rightarrow> nat \<Rightarrow> V) \<Rightarrow> V \<Rightarrow> nat \<Rightarrow> V" where
  "Cset_c p \<alpha> v = \<Squnion> (range (\<lambda>n. (Cstep_c p \<alpha> ^^ n) (Om v)))"

lemma elts_Cset_c: "elts (Cset_c p \<alpha> v) = (\<Union>n. elts ((Cstep_c p \<alpha> ^^ n) (Om v)))"
  by (simp add: Cset_c_def)

lemma Citer_c_subset_Citer:
  "elts ((Cstep_c p \<alpha> ^^ n) (Om v)) \<subseteq> elts ((Cstep p \<alpha> ^^ n) (Om v))"
proof (induction n)
  case 0 thus ?case by simp
next
  case (Suc n)
  have "elts ((Cstep_c p \<alpha> ^^ Suc n) (Om v))
          = elts (Cstep_c p \<alpha> ((Cstep_c p \<alpha> ^^ n) (Om v)))"
    by (simp only: funpow.simps(2) comp_apply)
  also have "\<dots> \<subseteq> elts (Cstep p \<alpha> ((Cstep_c p \<alpha> ^^ n) (Om v)))"
    by (rule Cstep_c_subset_Cstep)
  also have "\<dots> \<subseteq> elts (Cstep p \<alpha> ((Cstep p \<alpha> ^^ n) (Om v)))"
  proof (rule Cstep_mono_param[OF subset_refl _ Suc.IH])
    show "\<forall>\<xi> u. \<xi> \<in> elts \<alpha> \<longrightarrow> p \<xi> u = p \<xi> u" by simp
  qed
  also have "\<dots> = elts ((Cstep p \<alpha> ^^ Suc n) (Om v))"
    by (simp only: funpow.simps(2) comp_apply)
  finally show ?case .
qed

text \<open>\<^bold>\<open>Easy inclusion\<close>: canonical-generator closure \<open>\<subseteq>\<close> full closure (fewer
  generators).  The reverse \<open>Cset \<subseteq> Cset_c\<close> (Buchholz's Remark) is the \<section>1 core.\<close>

lemma Cset_c_subset_Cset: "elts (Cset_c p \<alpha> v) \<subseteq> elts (Cset p \<alpha> v)"
  by (auto simp: elts_Cset_c elts_Cset Citer_c_subset_Citer[THEN subsetD])

end
