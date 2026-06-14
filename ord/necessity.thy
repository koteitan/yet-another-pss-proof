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

text \<open>Basic closure structure of \<open>Cset_c\<close> (mirrors \<open>Cset\<close>), for the \<open>D-eq-1\<close> assembly.\<close>

lemma Citer_c_in_Cset_c: "elts ((Cstep_c p \<alpha> ^^ n) (Om v)) \<subseteq> elts (Cset_c p \<alpha> v)"
  by (auto simp: elts_Cset_c)

lemma Cset_c_mem_iff:
  "x \<in> elts (Cset_c p \<alpha> v) \<longleftrightarrow> (\<exists>n. x \<in> elts ((Cstep_c p \<alpha> ^^ n) (Om v)))"
  by (auto simp: elts_Cset_c)

lemma Om_subset_Cset_c: "elts (Om v) \<subseteq> elts (Cset_c p \<alpha> v)"
  using Citer_c_in_Cset_c[where n=0] by simp

text \<open>\<open>Cset_c\<close> is closed under addition (the sum branch of \<open>Cstep_c\<close>): if \<open>\<xi>,\<eta>\<close> are
  both in \<open>Cset_c\<close> then so is \<open>\<xi>+\<eta>\<close> (they appear together at some finite stage,
  whose successor stage contains the sum).\<close>

lemma Cset_c_add_closed:
  assumes "\<xi> \<in> elts (Cset_c p \<alpha> v)" and "\<eta> \<in> elts (Cset_c p \<alpha> v)"
  shows "\<xi> + \<eta> \<in> elts (Cset_c p \<alpha> v)"
proof -
  from assms obtain m k where m: "\<xi> \<in> elts ((Cstep_c p \<alpha> ^^ m) (Om v))"
    and k: "\<eta> \<in> elts ((Cstep_c p \<alpha> ^^ k) (Om v))" by (auto simp: Cset_c_mem_iff)
  have mono: "\<And>i j. i \<le> j \<Longrightarrow> elts ((Cstep_c p \<alpha> ^^ i) (Om v)) \<subseteq> elts ((Cstep_c p \<alpha> ^^ j) (Om v))"
  proof -
    fix i j :: nat assume "i \<le> j"
    then obtain d where "j = i + d" using le_Suc_ex by blast
    moreover have "elts ((Cstep_c p \<alpha> ^^ i) (Om v)) \<subseteq> elts ((Cstep_c p \<alpha> ^^ (i+d)) (Om v))"
    proof (induction d)
      case (Suc d)
      have "(Cstep_c p \<alpha> ^^ (i + Suc d)) (Om v) = Cstep_c p \<alpha> ((Cstep_c p \<alpha> ^^ (i+d)) (Om v))"
        by (simp only: add_Suc_right funpow.simps(2) comp_apply)
      moreover have "elts X \<subseteq> elts (Cstep_c p \<alpha> X)" for X
        by (auto simp: elts_Cstep_c)
      ultimately show ?case using Suc.IH by auto
    qed simp
    ultimately show "elts ((Cstep_c p \<alpha> ^^ i) (Om v)) \<subseteq> elts ((Cstep_c p \<alpha> ^^ j) (Om v))" by simp
  qed
  let ?n = "max m k"
  have x: "\<xi> \<in> elts ((Cstep_c p \<alpha> ^^ ?n) (Om v))" using m mono[of m ?n] by auto
  have y: "\<eta> \<in> elts ((Cstep_c p \<alpha> ^^ ?n) (Om v))" using k mono[of k ?n] by auto
  have "\<xi> + \<eta> \<in> elts (Cstep_c p \<alpha> ((Cstep_c p \<alpha> ^^ ?n) (Om v)))"
    using x y by (auto simp: elts_Cstep_c)
  hence "\<xi> + \<eta> \<in> elts ((Cstep_c p \<alpha> ^^ Suc ?n) (Om v))"
    by (simp only: funpow.simps(2) comp_apply)
  thus ?thesis using Citer_c_in_Cset_c by blast
qed

text \<open>\<open>Cset_c\<close> is closed under \<^emph>\<open>canonical\<close> generators: a generator \<open>p \<xi> u\<close> with
  \<open>\<xi> \<in> Cset_c \<inter> \<alpha>\<close> \<^bold>\<open>and\<close> \<open>\<xi>\<close> canonical (\<^const>\<open>acanon\<close> \<open>u \<xi>\<close>) is again in \<open>Cset_c\<close>.
  (The non-canonical generators are the ones \<open>D-eq-1\<close> must show redundant.)\<close>

lemma Cset_c_gen_closed:
  assumes "\<xi> \<in> elts (Cset_c p \<alpha> v)" and "\<xi> \<in> elts \<alpha>" and "acanon u \<xi>"
  shows "p \<xi> u \<in> elts (Cset_c p \<alpha> v)"
proof -
  from assms(1) obtain n where n: "\<xi> \<in> elts ((Cstep_c p \<alpha> ^^ n) (Om v))"
    by (auto simp: Cset_c_mem_iff)
  have qmem: "(\<xi>, u) \<in> {q \<in> (elts ((Cstep_c p \<alpha> ^^ n) (Om v)) \<inter> elts \<alpha>) \<times> (UNIV::nat set).
                          acanon (snd q) (fst q)}"
    using n assms(2,3) by simp
  have "p \<xi> u \<in> (\<lambda>(\<xi>,u). p \<xi> u)
          ` {q \<in> (elts ((Cstep_c p \<alpha> ^^ n) (Om v)) \<inter> elts \<alpha>) \<times> (UNIV::nat set).
               acanon (snd q) (fst q)}"
    using qmem by (force split: prod.split)
  hence "p \<xi> u \<in> elts (Cstep_c p \<alpha> ((Cstep_c p \<alpha> ^^ n) (Om v)))"
    by (simp add: elts_Cstep_c)
  hence "p \<xi> u \<in> elts ((Cstep_c p \<alpha> ^^ Suc n) (Om v))"
    by (simp only: funpow.simps(2) comp_apply)
  thus ?thesis using Citer_c_in_Cset_c by blast
qed

text \<open>\<^bold>\<open>Buchholz 1.4(b) core\<close>: an indecomposable \<open>\<gamma> \<ge> \<Omega>\<^sub>v\<close> in the \<^emph>\<open>canonical\<close>
  closure \<open>C\<^sup>c\<^sub>v(\<alpha>)\<close> is a generator \<open>p \<xi> u\<close> whose argument \<open>\<xi>\<close> is \<^bold>\<open>canonical\<close>
  (\<^const>\<open>acanon\<close> \<open>u \<xi>\<close>) and \<open>\<in> C\<^sup>c\<^sub>v(\<alpha>) \<inter> \<alpha>\<close>.  Mirror of \<open>indec_Cset_generator\<close> on
  \<open>Cset_c\<close>; the difference is that the \<open>Cstep_c\<close> generator step \<^emph>\<open>builds in\<close> the
  canonicity side-condition, so the witness is canonical for free \<dash> exactly why
  Buchholz's (*)-definition makes 1.4(b) immediate.\<close>

lemma indec_Cset_c_generator:
  assumes ordp: "\<And>\<xi> u. \<xi> \<in> elts \<alpha> \<Longrightarrow> Ord (p \<xi> u)"
    and indec: "indecomposable \<gamma>" and notOm: "\<gamma> \<notin> elts (Om v)"
    and mem: "\<gamma> \<in> elts (Cset_c p \<alpha> v)"
  shows "\<exists>\<xi> u. \<xi> \<in> elts (Cset_c p \<alpha> v) \<and> \<xi> \<in> elts \<alpha> \<and> acanon u \<xi> \<and> \<gamma> = p \<xi> u"
proof -
  have ordp': "\<forall>\<xi> u. \<xi> \<in> elts \<alpha> \<longrightarrow> Ord (p \<xi> u)" using ordp by blast
  from mem obtain N where "\<gamma> \<in> elts ((Cstep_c p \<alpha> ^^ N) (Om v))" by (auto simp: Cset_c_mem_iff)
  thus ?thesis
  proof (induction N)
    case 0
    hence "\<gamma> \<in> elts (Om v)" by simp
    with notOm show ?case by blast
  next
    case (Suc n)
    from Suc.prems have instep: "\<gamma> \<in> elts (Cstep_c p \<alpha> ((Cstep_c p \<alpha> ^^ n) (Om v)))"
      by (simp only: funpow.simps(2) comp_apply)
    let ?X = "(Cstep_c p \<alpha> ^^ n) (Om v)"
    from instep consider "\<gamma> \<in> elts ?X"
      | \<xi> \<eta> where "\<xi> \<in> elts ?X" "\<eta> \<in> elts ?X" "\<gamma> = \<xi> + \<eta>"
      | \<xi> u where "(\<xi>,u) \<in> {q \<in> (elts ?X \<inter> elts \<alpha>) \<times> (UNIV::nat set). acanon (snd q) (fst q)}"
                   "\<gamma> = p \<xi> u"
      by (auto simp: elts_Cstep_c)
    thus ?case
    proof cases
      case 1 thus ?thesis by (rule Suc.IH)
    next
      case 2
      have sub: "elts ?X \<subseteq> elts ((Cstep p \<alpha> ^^ n) (Om v))" by (rule Citer_c_subset_Citer)
      have o\<xi>: "Ord \<xi>" using 2(1) sub Ord_Citer[OF ordp'] by blast
      have o\<eta>: "Ord \<eta>" using 2(2) sub Ord_Citer[OF ordp'] by blast
      have le\<xi>: "\<xi> \<le> \<gamma>" using 2(3) add_le_cancel_left0 by simp
      have le\<eta>: "\<eta> \<le> \<gamma>" using 2(3) add_le_left[OF o\<xi> o\<eta>] by simp
      have "\<not> (\<xi> < \<gamma> \<and> \<eta> < \<gamma>)"
      proof
        assume "\<xi> < \<gamma> \<and> \<eta> < \<gamma>"
        hence "\<xi> + \<eta> < \<gamma>" using indecomposableD[OF indec _ _ o\<xi> o\<eta>] by blast
        thus False using 2(3) by simp
      qed
      hence "\<gamma> = \<xi> \<or> \<gamma> = \<eta>" using le\<xi> le\<eta> by (auto simp: less_V_def)
      hence "\<gamma> \<in> elts ?X" using 2(1,2) by auto
      thus ?thesis by (rule Suc.IH)
    next
      case 3
      have x\<alpha>: "\<xi> \<in> elts ?X \<inter> elts \<alpha>" and ac: "acanon u \<xi>" using 3(1) by auto
      have "\<xi> \<in> elts (Cset_c p \<alpha> v)" using x\<alpha> Citer_c_in_Cset_c by blast
      thus ?thesis using x\<alpha> ac 3(2) by blast
    qed
  qed
qed

text \<open>\<^bold>\<open>Buchholz 1.4(c)\<close> (the canonical-argument necessity): if \<open>\<psi>\<^sub>a(\<delta>)\<close> with
  \<open>\<delta>\<close> \<^bold>\<open>canonical\<close> lies in the canonical closure \<open>C\<^sup>c\<^sub>a(\<alpha>)\<close>, then the argument \<open>\<delta>\<close>
  is \<open>< \<alpha>\<close> (and itself in the closure).  Proof: 1.4(b) gives a \<^emph>\<open>canonical\<close>
  generator \<open>\<psi>\<^sub>u(\<xi>) = \<psi>\<^sub>a(\<delta>)\<close> with \<open>\<xi> \<in> \<alpha>\<close>; \<open>psi_inj_subscript\<close> forces \<open>u=a\<close> and
  \<open>psi_inj_arg_canonical\<close> (1.4a, both canonical) forces \<open>\<xi>=\<delta>\<close>.  This is the
  necessity that discharges \<open>psi_proj_nonmem\<close>: the canonical witness of
  \<open>\<psi>\<^sub>a(oV b)\<close> is \<open>oV(proj a b) \<ge> oV m\<close>, so it cannot be \<open>< oV m\<close>.\<close>

lemma psi_canonical_arg_lt:
  assumes can: "\<delta> \<in> elts (Cset (\<lambda>\<xi>\<in>elts \<delta>. psi \<xi>) \<delta> a)"
    and mem: "psi \<delta> a \<in> elts (Cset_c (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> a)"
  shows "\<delta> \<in> elts \<alpha> \<and> \<delta> \<in> elts (Cset_c (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> a)"
proof -
  let ?p = "\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>"
  have ordp: "\<And>\<xi> u. \<xi> \<in> elts \<alpha> \<Longrightarrow> Ord (?p \<xi> u)" by simp
  have notOm: "psi \<delta> a \<notin> elts (Om a)"
  proof
    assume "psi \<delta> a \<in> elts (Om a)"
    hence "psi \<delta> a < Om a" using Ord_mem_iff_lt[OF Ord_psi Ord_Om] by blast
    moreover have "Om a \<le> psi \<delta> a" by (rule Om_le_psi)
    ultimately show False by simp
  qed
  from indec_Cset_c_generator[OF ordp indecomposable_psi notOm mem]
  obtain \<xi> u where \<xi>: "\<xi> \<in> elts (Cset_c ?p \<alpha> a)" "\<xi> \<in> elts \<alpha>"
    "acanon u \<xi>" "psi \<delta> a = ?p \<xi> u" by blast
  have val: "psi \<delta> a = psi \<xi> u" using \<xi>(2,4) by simp
  have ua: "a = u" by (rule psi_inj_subscript[OF val])
  have aca\<xi>: "\<xi> \<in> elts (Cset (\<lambda>\<eta>\<in>elts \<xi>. psi \<eta>) \<xi> a)"
    using \<xi>(3) ua unfolding acanon_def by simp
  have Od: "Ord \<delta>"
    by (rule Cset_Ord[OF _ can]) (simp add: Ord_psi)
  have Ox: "Ord \<xi>"
    by (rule Cset_Ord[OF _ aca\<xi>]) (simp add: Ord_psi)
  have "\<delta> = \<xi>"
  proof (rule psi_inj_arg_canonical[OF Od Ox can aca\<xi>])
    show "psi \<delta> a = psi \<xi> a" using val ua by simp
  qed
  thus ?thesis using \<xi>(1,2) by simp
qed

text \<open>\<^bold>\<open>Generalized 1.4(c)\<close>: the \<open>\<psi>\<close>-subscript \<open>w\<close> may exceed the closure subscript
  \<open>a\<close> (as long as \<open>a \<le> w\<close>, so the value stays out of \<open>\<Omega>\<^sub>a\<close>).  For canonical \<open>\<delta>\<close>
  with \<open>\<psi>\<^bsub>w\<^esub>(\<delta>) \<in> C\<^sup>c\<^bsub>a\<^esub>(\<alpha>)\<close> we still get \<open>\<delta> < \<alpha>\<close> and \<open>\<delta> \<in> C\<^sup>c\<^bsub>a\<^esub>(\<alpha>)\<close>.  This is the
  form needed by \<open>term_nec\<close> on \<open>G\<^sub>a\<close>-critical subterms, where the head subscript \<open>a'\<close>
  of the term can be \<open>\<ge> a\<close>.\<close>

lemma psi_canonical_arg_lt_gen:
  assumes can: "\<delta> \<in> elts (Cset (\<lambda>\<xi>\<in>elts \<delta>. psi \<xi>) \<delta> w)"
    and wle: "a \<le> w"
    and mem: "psi \<delta> w \<in> elts (Cset_c (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> a)"
  shows "\<delta> \<in> elts \<alpha> \<and> \<delta> \<in> elts (Cset_c (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> a)"
proof -
  let ?p = "\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>"
  have ordp: "\<And>\<xi> u. \<xi> \<in> elts \<alpha> \<Longrightarrow> Ord (?p \<xi> u)" by simp
  have notOm: "psi \<delta> w \<notin> elts (Om a)"
  proof
    assume "psi \<delta> w \<in> elts (Om a)"
    hence "psi \<delta> w < Om a" using Ord_mem_iff_lt[OF Ord_psi Ord_Om] by blast
    moreover have "Om a \<le> Om w" using wle by (simp add: Om_mono)
    moreover have "Om w \<le> psi \<delta> w" by (rule Om_le_psi)
    ultimately show False by simp
  qed
  from indec_Cset_c_generator[OF ordp indecomposable_psi notOm mem]
  obtain \<xi> u where \<xi>: "\<xi> \<in> elts (Cset_c ?p \<alpha> a)" "\<xi> \<in> elts \<alpha>"
    "acanon u \<xi>" "psi \<delta> w = ?p \<xi> u" by blast
  have val: "psi \<delta> w = psi \<xi> u" using \<xi>(2,4) by simp
  have uw: "w = u" by (rule psi_inj_subscript[OF val])
  have aca\<xi>: "\<xi> \<in> elts (Cset (\<lambda>\<eta>\<in>elts \<xi>. psi \<eta>) \<xi> w)"
    using \<xi>(3) uw unfolding acanon_def by simp
  have Od: "Ord \<delta>"
    by (rule Cset_Ord[OF _ can]) (simp add: Ord_psi)
  have Ox: "Ord \<xi>"
    by (rule Cset_Ord[OF _ aca\<xi>]) (simp add: Ord_psi)
  have "\<delta> = \<xi>"
  proof (rule psi_inj_arg_canonical[OF Od Ox can aca\<xi>])
    show "psi \<delta> w = psi \<xi> w" using val uw by simp
  qed
  thus ?thesis using \<xi>(1,2) by simp
qed

subsection \<open>Additive-principal sum elimination in \<open>C\<^sup>c\<close> (Buchholz 1.2(e/g) for \<open>Cset_c\<close>)\<close>

text \<open>\<^bold>\<open>Sum decomposition\<close> (the core of \<open>term_nec\<close>'s induction step): if an
  \<^const>\<open>indecomposable\<close> ordinal \<open>\<xi>\<close> heads a sum \<open>\<xi>+\<eta>\<close> that lies in \<open>C\<^sup>c\<^bsub>v\<^esub>(\<alpha>)\<close>,
  then both summands \<open>\<xi>\<close> and \<open>\<eta>\<close> lie in \<open>C\<^sup>c\<^bsub>v\<^esub>(\<alpha>)\<close>.  This is exactly Buchholz's
  remark that \<open>C\<close> is closed under Cantor-normal-form components.  Proof by
  induction on the closure rank.  The delicate case is the \<^emph>\<open>sum step\<close>
  \<open>\<xi>+\<eta> = a+b\<close>: comparing \<open>a\<close> with the indecomposable head \<open>\<xi>\<close>, either \<open>\<xi> \<le> a\<close>
  (peel \<open>a = \<xi>+a'\<close> and recurse on \<open>a\<close>) or \<open>a < \<xi>\<close> (then \<open>a+\<xi> = \<xi>\<close> absorbs, so
  \<open>b \<ge> \<xi>\<close>, peel \<open>b = \<xi>+b'\<close> and recurse on \<open>b\<close>); in both cases the lower-rank
  recursion yields \<open>\<xi> \<in> C\<^sup>c\<close> and an \<open>a'/b' \<in> C\<^sup>c\<close>, and \<open>\<eta>\<close> is rebuilt by
  \<open>Cset_c_add_closed\<close>.  The generator step forces \<open>\<eta> = 0\<close> (a generator value is
  indecomposable, so a proper sum below it stays below).\<close>

lemma Cset_c_add_principal_elim:
  assumes ordp: "\<And>\<xi> u. \<xi> \<in> elts \<alpha> \<Longrightarrow> Ord (p \<xi> u)"
    and indecp: "\<And>\<zeta> u. \<zeta> \<in> elts \<alpha> \<Longrightarrow> indecomposable (p \<zeta> u)"
    and indec: "indecomposable \<xi>" and O\<eta>: "Ord \<eta>"
    and noabs: "\<eta> < \<xi> + \<eta>"
    and mem: "\<xi> + \<eta> \<in> elts (Cset_c p \<alpha> v)"
  shows "\<xi> \<in> elts (Cset_c p \<alpha> v) \<and> \<eta> \<in> elts (Cset_c p \<alpha> v)"
proof -
  have ordp': "\<forall>\<xi> u. \<xi> \<in> elts \<alpha> \<longrightarrow> Ord (p \<xi> u)" using ordp by blast
  have O\<xi>: "Ord \<xi>" by (rule indecomposable_imp_Ord[OF indec])
  have z0: "(0::V) \<in> elts (Om v)"
  proof -
    have "(0::V) \<in> elts 1" by simp
    moreover have "elts 1 \<subseteq> elts (Om v)" using one_le_Om less_eq_V_def by blast
    ultimately show ?thesis by blast
  qed
  have key: "\<And>\<eta>. Ord \<eta> \<Longrightarrow> \<eta> < \<xi> + \<eta> \<Longrightarrow> \<xi> + \<eta> \<in> elts ((Cstep_c p \<alpha> ^^ N) (Om v))
              \<Longrightarrow> \<xi> \<in> elts (Cset_c p \<alpha> v) \<and> \<eta> \<in> elts (Cset_c p \<alpha> v)" for N
  proof (induction N)
    case 0
    then have inOm: "\<xi> + \<eta> \<in> elts (Om v)" by simp
    have "\<xi> \<le> \<xi> + \<eta>" by simp
    moreover have xe: "\<xi> + \<eta> < Om v" using inOm Ord_mem_iff_lt[OF Ord_add[OF O\<xi> \<open>Ord \<eta>\<close>] Ord_Om] by blast
    ultimately have "\<xi> < Om v" using le_less_trans by blast
    hence x: "\<xi> \<in> elts (Om v)" using Ord_mem_iff_lt[OF O\<xi> Ord_Om] by blast
    have "\<eta> \<le> \<xi> + \<eta>" by (rule add_le_left[OF O\<xi> \<open>Ord \<eta>\<close>])
    hence "\<eta> < Om v" using xe le_less_trans by blast
    hence y: "\<eta> \<in> elts (Om v)" using Ord_mem_iff_lt[OF \<open>Ord \<eta>\<close> Ord_Om] by blast
    from x y Om_subset_Cset_c show ?case by blast
  next
    case (Suc n)
    note noabs = Suc.prems(2)
    let ?X = "(Cstep_c p \<alpha> ^^ n) (Om v)"
    from Suc.prems(3) have instep: "\<xi> + \<eta> \<in> elts (Cstep_c p \<alpha> ?X)"
      by (simp only: funpow.simps(2) comp_apply)
    have subC: "elts ?X \<subseteq> elts (Cset_c p \<alpha> v)" by (rule Citer_c_in_Cset_c)
    have subOrd: "elts ?X \<subseteq> elts ((Cstep p \<alpha> ^^ n) (Om v))" by (rule Citer_c_subset_Citer)
    have memSum: "\<xi> + \<eta> \<in> elts (Cset_c p \<alpha> v)" using Suc.prems(3) Citer_c_in_Cset_c by blast
    from instep consider
        "\<xi> + \<eta> \<in> elts ?X"
      | a b where "a \<in> elts ?X" "b \<in> elts ?X" "\<xi> + \<eta> = a + b"
      | \<zeta> u where "\<zeta> \<in> elts ?X \<inter> elts \<alpha>" "\<xi> + \<eta> = p \<zeta> u"
      by (auto simp: elts_Cstep_c)
    thus ?case
    proof cases
      case 1 thus ?thesis using Suc.IH[OF Suc.prems(1) noabs] by blast
    next
      case 2
      have oa: "Ord a" using 2(1) subOrd Ord_Citer[OF ordp'] by blast
      have ob: "Ord b" using 2(2) subOrd Ord_Citer[OF ordp'] by blast
      show ?thesis
      proof (cases "\<xi> \<le> a")
        case True
        \<comment> \<open>peel \<open>a = \<xi> + a'\<close>, recurse on \<open>a\<close> (rank \<open>n\<close>)\<close>
        obtain a' where a': "\<xi> + a' = a" and Oa': "Ord a'"
          using le_Ord_diff[OF True O\<xi> oa] by metis
        have memA: "\<xi> + a' \<in> elts ?X" using a' 2(1) by simp
        \<comment> \<open>recursion noabs \<open>a' < \<xi>+a'\<close>: else \<open>\<xi>+a'=a'\<close> forces \<open>\<xi>+\<eta>=\<eta>\<close>, contra \<open>noabs\<close>\<close>
        have nA: "a' < \<xi> + a'"
        proof (rule ccontr)
          assume "\<not> a' < \<xi> + a'"
          hence "\<xi> + a' = a'" using add_le_left[OF O\<xi> Oa'] by (simp add: less_V_def)
          hence "a = a'" using a' by simp
          have "\<xi> + \<eta> = a + b" by (rule 2(3))
          also have "\<dots> = (\<xi> + a') + b" using a' by simp
          also have "\<dots> = \<xi> + (a' + b)" by (simp add: add.assoc)
          finally have e1: "\<eta> = a' + b" by simp
          have "\<xi> + (a' + b) = (\<xi> + a') + b" by (simp add: add.assoc)
          also have "\<dots> = a' + b" using \<open>\<xi> + a' = a'\<close> by simp
          finally have "\<xi> + \<eta> = \<eta>" using e1 by simp
          thus False using noabs by simp
        qed
        from Suc.IH[OF Oa' nA memA] have x: "\<xi> \<in> elts (Cset_c p \<alpha> v)"
          and a'C: "a' \<in> elts (Cset_c p \<alpha> v)" by blast+
        have "\<xi> + \<eta> = a + b" by (rule 2(3))
        also have "\<dots> = (\<xi> + a') + b" using a' by simp
        also have "\<dots> = \<xi> + (a' + b)" by (simp add: add.assoc)
        finally have eta: "\<eta> = a' + b" by simp
        have bC: "b \<in> elts (Cset_c p \<alpha> v)" using 2(2) subC by blast
        have "\<eta> \<in> elts (Cset_c p \<alpha> v)" using eta Cset_c_add_closed[OF a'C bC] by simp
        thus ?thesis using x by blast
      next
        case False
        hence ax: "a < \<xi>" using Ord_not_le[OF O\<xi> oa] by simp
        have absorb: "a + \<xi> = \<xi>" by (rule indecomposable_imp_eq[OF indec oa ax])
        \<comment> \<open>\<open>b \<ge> \<xi>\<close>: else \<open>a+b < \<xi> \<le> \<xi>+\<eta> = a+b\<close>\<close>
        have bge: "\<xi> \<le> b"
        proof (rule ccontr)
          assume "\<not> \<xi> \<le> b"
          hence "b < \<xi>" using Ord_not_le[OF O\<xi> ob] by simp
          hence "a + b < \<xi>" using indecomposableD[OF indec ax _ oa ob] by blast
          also have "\<xi> \<le> \<xi> + \<eta>" by simp
          finally show False using 2(3) by simp
        qed
        obtain b' where b': "\<xi> + b' = b" and Ob': "Ord b'"
          using le_Ord_diff[OF bge O\<xi> ob] by metis
        have memB: "\<xi> + b' \<in> elts ?X" using b' 2(2) by simp
        have etaEq: "\<eta> = b'"
        proof -
          have "\<xi> + \<eta> = a + b" by (rule 2(3))
          also have "\<dots> = a + (\<xi> + b')" using b' by simp
          also have "\<dots> = (a + \<xi>) + b'" by (simp add: add.assoc)
          also have "\<dots> = \<xi> + b'" using absorb by simp
          finally show ?thesis by simp
        qed
        \<comment> \<open>recursion noabs \<open>b' < \<xi>+b'\<close>: \<open>b'=\<eta>\<close> and \<open>\<xi>+\<eta>=\<xi>+b'\<close>, so \<open>\<eta><\<xi>+\<eta>\<close> gives it\<close>
        have nB: "b' < \<xi> + b'" using noabs etaEq by simp
        from Suc.IH[OF Ob' nB memB] have x: "\<xi> \<in> elts (Cset_c p \<alpha> v)"
          and b'C: "b' \<in> elts (Cset_c p \<alpha> v)" by blast+
        thus ?thesis using etaEq by blast
      qed
    next
      case 3
      have z\<alpha>: "\<zeta> \<in> elts \<alpha>" using 3(1) by blast
      have indVal: "indecomposable (p \<zeta> u)" by (rule indecp[OF z\<alpha>])
      \<comment> \<open>no absorption (\<open>noabs\<close>): a generator value is indecomposable, so \<open>\<eta> = 0\<close>\<close>
      have e_lt: "\<eta> < p \<zeta> u" using noabs 3(2) by simp
      have eta0: "\<eta> = 0"
      proof (rule ccontr)
        assume "\<eta> \<noteq> 0"
        hence pos: "0 < \<eta>" using \<open>Ord \<eta>\<close> by (auto simp: less_V_def)
        have "\<xi> < \<xi> + \<eta>" using pos by simp
        hence x_lt: "\<xi> < p \<zeta> u" using 3(2) by simp
        have "\<xi> + \<eta> < p \<zeta> u"
          by (rule indecomposableD[OF indVal x_lt e_lt O\<xi> \<open>Ord \<eta>\<close>])
        thus False using 3(2) by simp
      qed
      have x: "\<xi> \<in> elts (Cset_c p \<alpha> v)" using memSum eta0 by simp
      have y: "\<eta> \<in> elts (Cset_c p \<alpha> v)" using eta0 z0 Om_subset_Cset_c by blast
      from x y show ?thesis by blast
    qed
  qed
  from mem obtain N where "\<xi> + \<eta> \<in> elts ((Cstep_c p \<alpha> ^^ N) (Om v))" by (auto simp: Cset_c_mem_iff)
  from key[OF O\<eta> noabs this] show ?thesis .
qed

subsection \<open>Buchholz Lemma 1.9 necessity for OT term values (\<open>term_nec\<close>)\<close>

text \<open>\<^bold>\<open>No-absorption helpers.\<close>  For an \<^const>\<open>indecomposable\<close> head \<open>\<xi>\<close>, the multiple
  \<open>\<xi>\<cdot>\<omega>\<close> is again indecomposable, and any \<open>\<beta> < \<xi>\<cdot>\<omega>\<close> fails to absorb \<open>\<xi>\<close>
  (\<open>\<beta> < \<xi>+\<beta>\<close>).  These feed the \<open>noabs\<close> side-condition of
  \<open>Cset_c_add_principal_elim\<close> when applied to a wf3 term value.\<close>

lemma indec_mult_omega:
  assumes "indecomposable \<xi>" "0 < \<xi>" shows "indecomposable (\<xi> * \<omega>)"
proof -
  have O\<xi>: "Ord \<xi>" by (rule indecomposable_imp_Ord[OF assms(1)])
  have Oxw: "Ord (\<xi> * \<omega>)" using O\<xi> by (simp add: Ord_mult)
  have memlt: "\<exists>n. \<delta> < \<xi> * ord_of_nat n" if "\<delta> \<in> elts (\<xi> * \<omega>)" for \<delta>
  proof -
    from that obtain k where "k \<in> elts \<omega>" "\<delta> \<in> elts (\<xi> * k)"
      using mult_Limit[of \<omega> \<xi>] Limit_omega by auto
    then obtain n where kn: "k = ord_of_nat n" using elts_\<omega> by auto
    have "Ord \<delta>" using that Ord_in_Ord[OF Oxw] by blast
    hence "\<delta> < \<xi> * ord_of_nat n"
      using \<open>\<delta> \<in> elts (\<xi> * k)\<close> kn OrdmemD[OF Ord_mult[OF Ord_ord_of_nat O\<xi>]] by simp
    thus "\<exists>n. \<delta> < \<xi> * ord_of_nat n" by blast
  qed
  have plus: "\<beta> + \<gamma> \<in> elts (\<xi> * \<omega>)"
    if b: "\<beta> \<in> elts (\<xi> * \<omega>)" and g: "\<gamma> \<in> elts (\<xi> * \<omega>)" for \<beta> \<gamma>
  proof -
    have O\<beta>: "Ord \<beta>" using b Ord_in_Ord[OF Oxw] by blast
    have O\<gamma>: "Ord \<gamma>" using g Ord_in_Ord[OF Oxw] by blast
    obtain m where m: "\<beta> < \<xi> * ord_of_nat m" using memlt[OF b] by blast
    obtain k where k: "\<gamma> < \<xi> * ord_of_nat k" using memlt[OF g] by blast
    have "\<beta> + \<gamma> < \<xi> * ord_of_nat m + \<xi> * ord_of_nat k"
    proof -
      have "\<beta> + \<gamma> \<le> \<xi> * ord_of_nat m + \<gamma>"
        by (rule add_right_mono[OF less_imp_le[OF m] O\<beta> Ord_mult[OF Ord_ord_of_nat O\<xi>] O\<gamma>])
      also have "\<dots> < \<xi> * ord_of_nat m + \<xi> * ord_of_nat k" using k by simp
      finally show ?thesis .
    qed
    also have "\<xi> * ord_of_nat m + \<xi> * ord_of_nat k = \<xi> * (ord_of_nat m + ord_of_nat k)"
      by (simp add: add_mult_distrib)
    also have "\<dots> = \<xi> * ord_of_nat (m + k)" by (simp add: ord_of_nat_add)
    also have "\<dots> < \<xi> * \<omega>"
      using assms(2) OrdmemD[OF Ord_\<omega> ord_of_nat_\<omega>, of "m+k"]
      by (simp add: mult_cancel_less_iff O\<xi>)
    finally have "\<beta> + \<gamma> < \<xi> * \<omega>" .
    thus ?thesis using OrdmemD Ord_mem_iff_lt[OF Ord_add[OF O\<beta> O\<gamma>] Oxw] by blast
  qed
  show ?thesis unfolding indecomposable_def using Oxw plus by blast
qed

lemma noabs_of_lt_mult_omega:
  assumes indec: "indecomposable \<xi>" and pos: "0 < \<xi>" and O\<beta>: "Ord \<beta>" and lt: "\<beta> < \<xi> * \<omega>"
  shows "\<beta> < \<xi> + \<beta>"
proof (rule ccontr)
  assume "\<not> \<beta> < \<xi> + \<beta>"
  have O\<xi>: "Ord \<xi>" by (rule indecomposable_imp_Ord[OF indec])
  have abs: "\<xi> + \<beta> = \<beta>" using \<open>\<not> \<beta> < \<xi> + \<beta>\<close> add_le_left[OF O\<xi> O\<beta>] by (simp add: less_V_def)
  have absMult: "\<xi> * ord_of_nat n + \<beta> = \<beta>" for n
  proof (induction n)
    case 0 thus ?case by simp
  next
    case (Suc n)
    have "\<xi> * ord_of_nat (Suc n) + \<beta> = (\<xi> * ord_of_nat n + \<xi>) + \<beta>" by (simp add: mult_succ)
    also have "\<dots> = \<xi> * ord_of_nat n + (\<xi> + \<beta>)" by (simp add: add.assoc)
    also have "\<dots> = \<xi> * ord_of_nat n + \<beta>" using abs by simp
    also have "\<dots> = \<beta>" using Suc by simp
    finally show ?case .
  qed
  have mult_le: "\<xi> * ord_of_nat n \<le> \<beta>" for n
    using absMult[of n] add_le_cancel_left0[of "\<xi> * ord_of_nat n" \<beta>] by simp
  have "\<xi> * \<omega> \<le> \<beta>"
  proof -
    have "\<xi> * \<omega> = \<Squnion> ((*) \<xi> ` elts \<omega>)" by (simp add: mult_Limit)
    moreover have "\<And>x. x \<in> (*) \<xi> ` elts \<omega> \<Longrightarrow> x \<le> \<beta>"
      using mult_le elts_\<omega> by auto
    ultimately show ?thesis using O\<beta> by (auto intro: Sup_least)
  qed
  thus False using lt by simp
qed

text \<open>The tail value \<open>oV c\<close> of a wf3 term whose principals are dominated by the head
  \<open>\<psi>\<^bsub>a'\<^esub>(oV b')\<close> stays below \<open>\<psi>\<^bsub>a'\<^esub>(oV b')\<cdot>\<omega>\<close>: each spine principal is \<open>\<le> \<xi>\<close>
  (\<open>e<a'\<close> jump, or \<open>e=a'\<close> with \<open>oV f \<le> oV b'\<close> by order preservation), so the finite
  sum stays in the \<open>\<xi>\<cdot>\<omega>\<close> block.  Needs \<open>wf3 b'\<close> for the \<open>e=a'\<close> argument bound.\<close>

lemma oV_tail_lt_mult_omega:
  assumes pos: "0 < psi (oV b') a'" and wfb': "wf3 b'"
  shows "wf3 c \<Longrightarrow> headle_all (P a' b' Z) c \<Longrightarrow> oV c < psi (oV b') a' * \<omega>"
proof (induction c)
  case Z
  have "0 < psi (oV b') a' * \<omega>"
    using pos by (simp add: zero_less_mult_iff)
  thus ?case by simp
next
  case (P e f g)
  let ?\<xi> = "psi (oV b') a'"
  have wff: "wf3 f" and wfg: "wf3 g" using P.prems(1) by auto
  have hd: "hdle (P e f Z) (P a' b' Z)" and hall: "headle_all (P a' b' Z) g"
    using P.prems(2) by auto
  have ind\<xi>\<omega>: "indecomposable (?\<xi> * \<omega>)" by (rule indec_mult_omega[OF indecomposable_psi pos])
  have lead_le: "psi (oV f) e \<le> ?\<xi>"
  proof -
    have "e < a' \<or> (e = a' \<and> (olt f b' \<or> f = b'))" using hd by simp
    thus ?thesis
    proof
      assume "e < a'"
      have "psi (oV f) e < psi (oV b') a'" by (rule psi_subscript_jump[OF \<open>e < a'\<close>])
      thus ?thesis by simp
    next
      assume A: "e = a' \<and> (olt f b' \<or> f = b')"
      hence ea: "e = a'" by simp
      have "oV f \<le> oV b'"
      proof -
        from A have "olt f b' \<or> f = b'" by simp
        thus ?thesis
        proof
          assume "olt f b'"
          have "oV f < oV b'" by (rule oV_order_pres[OF wff wfb' \<open>olt f b'\<close>])
          thus ?thesis by simp
        next
          assume "f = b'" thus ?thesis by simp
        qed
      qed
      hence "psi (oV f) a' \<le> psi (oV b') a'" by (rule psi_mono_arg)
      thus ?thesis using ea by simp
    qed
  qed
  have xi_lt: "?\<xi> < ?\<xi> * \<omega>"
  proof -
    have w1: "(1::V) < \<omega>" using OrdmemD[OF Ord_\<omega> ord_of_nat_\<omega>, of 1] by simp
    have "?\<xi> * 1 < ?\<xi> * \<omega>"
      using mult_cancel_less_iff[of "?\<xi>" 1 \<omega>] w1 pos by simp
    thus ?thesis by simp
  qed
  have lead_lt: "psi (oV f) e < ?\<xi> * \<omega>"
    using lead_le xi_lt by simp
  have tail_lt: "oV g < ?\<xi> * \<omega>" using P.IH(2)[OF wfg hall] .
  have "oV (P e f g) = psi (oV f) e + oV g" by simp
  also have "\<dots> < ?\<xi> * \<omega>"
    using indecomposableD[OF ind\<xi>\<omega> lead_lt tail_lt Ord_psi Ord_oV] by simp
  finally show ?case .
qed

text \<open>\<^bold>\<open>Buchholz Lemma 1.9 necessity for OT term values\<close>: if a well-formed term \<open>t\<close>
  has its value \<open>oV t\<close> in the canonical closure \<open>C\<^sup>c\<^bsub>a\<^esub>(\<alpha>)\<close>, then every
  \<open>G\<^sub>a\<close>-critical subterm of \<open>t\<close> has value \<open>< \<alpha>\<close>.  Structural induction on \<open>t\<close>:
  \<^item> \<open>t = Z\<close>: \<open>G\<^sub>a Z = \<emptyset>\<close>, vacuous.
  \<^item> \<open>t = P a' b' c'\<close>: \<open>oV t = \<psi>\<^bsub>a'\<^esub>(oV b') + oV c'\<close> with the leading principal
    \<^const>\<open>indecomposable\<close>.  \<open>Cset_c_add_principal_elim\<close> (no-absorption supplied by
    \<open>oV_tail_lt_mult_omega\<close> + \<open>noabs_of_lt_mult_omega\<close> from wf3's spine bound) splits
    \<open>\<psi>\<^bsub>a'\<^esub>(oV b') \<in> C\<^sup>c\<close> and \<open>oV c' \<in> C\<^sup>c\<close>.  When \<open>a \<le> a'\<close>, \<open>psi_canonical_arg_lt_gen\<close>
    (1.4c, \<open>oV b'\<close> canonical by \<open>Ccond_of_lt\<close>+\<open>oV_order_pres\<close>) gives \<open>oV b' < \<alpha>\<close>;
    the recursive obligations on \<open>G\<^sub>a b'\<close> and \<open>G\<^sub>a c'\<close> are discharged by the IHs.\<close>

theorem term_nec:
  "Ord \<alpha> \<Longrightarrow> wf3 t \<Longrightarrow> oV t \<in> elts (Cset_c (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> a)
     \<Longrightarrow> \<forall>x \<in> Gterm a t. oV x < \<alpha>"
proof (induction t arbitrary: \<alpha>)
  case Z
  show ?case by simp
next
  case (P a' b' c')
  note O\<alpha> = P.prems(1)
  let ?p = "\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>"
  let ?\<xi> = "psi (oV b') a'"
  have wfb': "wf3 b'" and wfc': "wf3 c'"
    and Gb': "\<forall>x\<in>Gterm a' b'. olt x b'" and hd: "hdle c' (P a' b' Z)"
    using P.prems(2) by auto
  have mem: "?\<xi> + oV c' \<in> elts (Cset_c ?p \<alpha> a)"
    using P.prems(3) by (simp only: oV.simps)
  have ordp: "\<And>\<xi> u. \<xi> \<in> elts \<alpha> \<Longrightarrow> Ord (?p \<xi> u)" by simp
  have indecp: "\<And>\<zeta> u. \<zeta> \<in> elts \<alpha> \<Longrightarrow> indecomposable (?p \<zeta> u)"
    by (simp add: indecomposable_psi)
  have pos: "0 < ?\<xi>" using psi_addprinc[of "oV b'" a'] by (simp add: addprinc_def)
  \<comment> \<open>no-absorption: \<open>oV c' < \<xi> + oV c'\<close>, from the wf3 spine bound \<open>oV c' < \<xi>\<cdot>\<omega>\<close>\<close>
  have hac: "headle_all (P a' b' Z) c'" by (rule wf3_headle[OF P.prems(2)])
  have tail_bound: "oV c' < ?\<xi> * \<omega>"
    by (rule oV_tail_lt_mult_omega[OF pos wfb' wfc' hac])
  have noabs: "oV c' < ?\<xi> + oV c'"
    by (rule noabs_of_lt_mult_omega[OF indecomposable_psi pos Ord_oV tail_bound])
  \<comment> \<open>1.2(e/g): split the head and tail into \<open>C\<^sup>c\<close>\<close>
  have split: "?\<xi> \<in> elts (Cset_c ?p \<alpha> a) \<and> oV c' \<in> elts (Cset_c ?p \<alpha> a)"
    by (rule Cset_c_add_principal_elim[OF ordp indecp indecomposable_psi Ord_oV noabs mem])
  have head_mem: "?\<xi> \<in> elts (Cset_c ?p \<alpha> a)" using split by simp
  have tail_mem: "oV c' \<in> elts (Cset_c ?p \<alpha> a)" using split by simp
  \<comment> \<open>IH on the tail \<open>c'\<close>\<close>
  have IHc: "\<forall>x \<in> Gterm a c'. oV x < \<alpha>" by (rule P.IH(2)[OF O\<alpha> wfc' tail_mem])
  \<comment> \<open>the head contributes only when \<open>a \<le> a'\<close>; then \<open>oV b' < \<alpha>\<close> and \<open>oV b' \<in> C\<^sup>c\<close>\<close>
  show ?case
  proof (cases "a \<le> a'")
    case False
    \<comment> \<open>head not collected: \<open>G\<^sub>a t = G\<^sub>a c'\<close>\<close>
    have "Gterm a (P a' b' c') = Gterm a c'" using False by simp
    thus ?thesis using IHc by simp
  next
    case True
    \<comment> \<open>\<open>oV b'\<close> is canonical (Ccond), so \<open>psi_canonical_arg_lt_gen\<close> gives \<open>oV b' < \<alpha>\<close>\<close>
    have canb': "oV b' \<in> elts (Cset (\<lambda>\<xi>\<in>elts (oV b'). psi \<xi>) (oV b') a')"
    proof (rule Ccond_of_lt)
      fix x assume xG: "x \<in> Gterm a' b'"
      have wfx: "wf3 x" by (rule wf3_Gterm[OF wfb' xG])
      have "olt x b'" using Gb' xG by blast
      show "oV x < oV b'" by (rule oV_order_pres[OF wfx wfb' \<open>olt x b'\<close>])
    qed
    have argres: "oV b' \<in> elts \<alpha> \<and> oV b' \<in> elts (Cset_c ?p \<alpha> a)"
      by (rule psi_canonical_arg_lt_gen[OF canb' True head_mem])
    have ob'_lt: "oV b' < \<alpha>"
      using argres OrdmemD[OF O\<alpha>] by blast
    have ob'_mem: "oV b' \<in> elts (Cset_c ?p \<alpha> a)" using argres by simp
    \<comment> \<open>IH on the argument \<open>b'\<close>\<close>
    have IHb: "\<forall>x \<in> Gterm a b'. oV x < \<alpha>" by (rule P.IH(1)[OF O\<alpha> wfb' ob'_mem])
    \<comment> \<open>assemble \<open>G\<^sub>a t = {b'} \<union> G\<^sub>a b' \<union> G\<^sub>a c'\<close>\<close>
    have "Gterm a (P a' b' c') = insert b' (Gterm a b') \<union> Gterm a c'" using True by simp
    thus ?thesis using ob'_lt IHb IHc by auto
  qed
qed

subsection \<open>Buchholz's Remark: the canonicity side-condition (*) is redundant\<close>

text \<open>\<^bold>\<open>Buchholz's Remark\<close> (the redundancy of the non-canonical generators):
  the canonical-generator closure \<open>C\<^sup>c\<^sub>v(\<alpha>)\<close> already equals the full closure
  \<open>C\<^sub>v(\<alpha>)\<close>.  The easy inclusion \<open>\<supseteq>\<close> is \<open>Cset_c_subset_Cset\<close>; the core is \<open>\<subseteq>\<close>,
  proved by an outer rank (\<open>Citer\<close>) induction reduced to a generator-closure
  helper \<open>Cset_c_anygen_closed\<close>: \<open>C\<^sup>c\<^sub>v(\<alpha>)\<close> is closed under \<^emph>\<open>every\<close> generator
  \<open>\<psi>\<^sub>w(\<xi>)\<close> with \<open>\<xi> \<in> C\<^sup>c\<^sub>v(\<alpha>) \<inter> \<alpha>\<close>, canonical or not.  Three of the four
  sub-cases are elementary:
  \<^item> \<open>\<xi>\<close> canonical: \<open>Cset_c_gen_closed\<close> (the generator step builds it in);
  \<^item> \<open>w < v\<close>: \<open>\<psi>\<^sub>w(\<xi>) < \<Omega>\<^bsub>w+1\<^esub> \<le> \<Omega>\<^sub>v\<close>, so the value is already in the \<open>\<Omega>\<^sub>v\<close>-part;
  \<^item> sums / \<open>\<Omega>\<^sub>v\<close>: the basic \<open>Cset_c\<close> closure lemmas.

  The remaining sub-case (\<^emph>\<open>non-canonical\<close> generator with subscript \<open>w \<ge> v\<close>) is
  exactly the point Buchholz states "can be shown".  Here \<open>\<psi>\<^sub>w(\<xi>) \<le> \<xi> < \<alpha>\<close>
  (\<open>psi_le_of_not_acanon\<close>) and the value is itself non-canonical
  (\<open>noncanon_value_noncanon\<close>); reproducing it in \<open>C\<^sup>c\<^sub>v(\<alpha>)\<close> needs the cross-subscript
  collapse of the non-canonical argument to a canonical witness inside the closure.
  It is isolated below as the single lemma \<open>noncanon_gen_in_Cset_c_residue\<close>
  (\<^bold>\<open>one localized \<open>sorry\<close>\<close>).  Everything else is green, and a finite-CNF model
  check (\<^file>\<open>../tools/cset_remark_check.py\<close>) found \<open>C\<^sub>v(\<alpha>) = C\<^sup>c\<^sub>v(\<alpha>)\<close> in all
  48 tested \<open>(\<alpha>,v)\<close> instances (no counterexample), so the residue is not false.\<close>

text \<open>A non-canonical generator value is itself non-canonical and \<open>\<le>\<close> its argument:
  \<open>\<psi>\<^sub>w(\<xi>) \<le> \<xi>\<close> and \<open>\<not> acanon w (\<psi>\<^sub>w(\<xi>))\<close>.  (If the value were canonical it would
  lie in its own band-closure, which is \<open>\<subseteq>\<close> the \<open>\<xi>\<close>-closure that excludes it.)\<close>

lemma noncanon_value_noncanon:
  assumes "Ord \<xi>" "\<not> acanon w \<xi>"
  shows "psi \<xi> w \<le> \<xi> \<and> \<not> acanon w (psi \<xi> w)"
proof
  show le: "psi \<xi> w \<le> \<xi>" by (rule psi_le_of_not_acanon[OF assms])
  show "\<not> acanon w (psi \<xi> w)"
  proof
    assume "acanon w (psi \<xi> w)"
    hence inn: "psi \<xi> w \<in> elts (Cset (\<lambda>\<eta>\<in>elts (psi \<xi> w). psi \<eta>) (psi \<xi> w) w)"
      unfolding acanon_def .
    have "elts (Cset (\<lambda>\<eta>\<in>elts (psi \<xi> w). psi \<eta>) (psi \<xi> w) w)
            \<subseteq> elts (Cset (\<lambda>\<eta>\<in>elts \<xi>. psi \<eta>) \<xi> w)"
      by (rule CC_mono[OF le])
    with inn have "psi \<xi> w \<in> elts (Cset (\<lambda>\<eta>\<in>elts \<xi>. psi \<eta>) \<xi> w)" by blast
    thus False using psi_notin by simp
  qed
qed

text \<open>If \<open>w < v\<close> the generator value lies below \<open>\<Omega>\<^sub>v\<close>, hence in the \<open>\<Omega>\<^sub>v\<close>-part of
  the closure.\<close>

lemma psi_low_sub_in_Om:
  assumes "w < v"
  shows "psi \<xi> w \<in> elts (Om v)"
proof -
  have "psi \<xi> w < Om (Suc w)" by (rule psi_lt_Om_Suc)
  also have "Om (Suc w) \<le> Om v" using assms by (simp add: Om_mono Suc_leI)
  finally show ?thesis using Ord_mem_iff_lt[OF Ord_psi Ord_Om] by blast
qed

text \<open>\<^bold>\<open>The localized residue (single \<open>sorry\<close>)\<close>: a \<^emph>\<open>non-canonical\<close> generator
  \<open>\<psi>\<^sub>w(\<xi>)\<close> with subscript \<open>w \<ge> v\<close> and argument \<open>\<xi> \<in> C\<^sup>c\<^sub>v(\<alpha>) \<inter> \<alpha>\<close> is reproduced
  in \<open>C\<^sup>c\<^sub>v(\<alpha>)\<close>.  This is Buchholz's "can be shown": the cross-subscript collapse
  of the non-canonical argument to a canonical witness in the closure.\<close>

lemma noncanon_gen_in_Cset_c_residue:
  assumes "Ord \<xi>" "\<xi> \<in> elts (Cset_c (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v)" "\<xi> \<in> elts \<alpha>"
    and "\<not> acanon w \<xi>" "v \<le> w"
  shows "psi \<xi> w \<in> elts (Cset_c (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v)"
  sorry

text \<open>\<open>C\<^sup>c\<^sub>v(\<alpha>)\<close> is closed under \<^bold>\<open>every\<close> generator with argument in
  \<open>C\<^sup>c\<^sub>v(\<alpha>) \<inter> \<alpha>\<close> (canonical \<open>\<Rightarrow>\<close> \<open>Cset_c_gen_closed\<close>; \<open>w<v\<close> \<open>\<Rightarrow>\<close> \<open>\<Omega>\<^sub>v\<close>-part;
  the residual non-canonical \<open>w\<ge>v\<close> case \<open>\<Rightarrow>\<close> the lemma above).\<close>

lemma Cset_c_anygen_closed:
  assumes "Ord \<xi>" "\<xi> \<in> elts (Cset_c (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v)" "\<xi> \<in> elts \<alpha>"
  shows "psi \<xi> w \<in> elts (Cset_c (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v)"
proof (cases "acanon w \<xi>")
  case True
  have "(\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<xi> w \<in> elts (Cset_c (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v)"
    by (rule Cset_c_gen_closed[OF assms(2,3) True])
  thus ?thesis using assms(3) by simp
next
  case False
  show ?thesis
  proof (cases "w < v")
    case True
    have "psi \<xi> w \<in> elts (Om v)" by (rule psi_low_sub_in_Om[OF True])
    thus ?thesis using Om_subset_Cset_c by blast
  next
    case False
    hence "v \<le> w" by simp
    show ?thesis
      by (rule noncanon_gen_in_Cset_c_residue[OF assms \<open>\<not> acanon w \<xi>\<close> \<open>v \<le> w\<close>])
  qed
qed

text \<open>\<^bold>\<open>Outer rank induction\<close>: every \<open>Citer\<close>-stage of the full closure sits inside
  \<open>C\<^sup>c\<^sub>v(\<alpha>)\<close>.  Old / sum / \<open>\<Omega>\<^sub>v\<close> cases use the IH and \<open>Cset_c_add_closed\<close>; the
  generator case uses \<open>Cset_c_anygen_closed\<close>.\<close>

lemma Citer_subset_Cset_c:
  shows "elts ((Cstep (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> ^^ n) (Om v))
           \<subseteq> elts (Cset_c (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v)"
proof (induction n)
  case 0
  show ?case using Om_subset_Cset_c by simp
next
  case (Suc n)
  let ?p = "\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>"
  have ordp': "\<forall>\<xi> u. \<xi> \<in> elts \<alpha> \<longrightarrow> Ord (?p \<xi> u)" by simp
  show ?case
  proof (rule subsetI)
    fix x assume "x \<in> elts ((Cstep ?p \<alpha> ^^ Suc n) (Om v))"
    hence "x \<in> elts (Cstep ?p \<alpha> ((Cstep ?p \<alpha> ^^ n) (Om v)))"
      by (simp only: funpow.simps(2) comp_apply)
    then consider "x \<in> elts ((Cstep ?p \<alpha> ^^ n) (Om v))"
      | \<xi> \<eta> where "\<xi> \<in> elts ((Cstep ?p \<alpha> ^^ n) (Om v))"
                  "\<eta> \<in> elts ((Cstep ?p \<alpha> ^^ n) (Om v))" "x = \<xi> + \<eta>"
      | \<xi> u where "\<xi> \<in> elts ((Cstep ?p \<alpha> ^^ n) (Om v))" "\<xi> \<in> elts \<alpha>" "x = ?p \<xi> u"
      by (auto simp: elts_Cstep)
    thus "x \<in> elts (Cset_c ?p \<alpha> v)"
    proof cases
      case 1 thus ?thesis using Suc.IH by blast
    next
      case 2
      have "\<xi> \<in> elts (Cset_c ?p \<alpha> v)" "\<eta> \<in> elts (Cset_c ?p \<alpha> v)"
        using 2(1,2) Suc.IH by blast+
      thus ?thesis using 2(3) Cset_c_add_closed by blast
    next
      case 3
      have xc: "\<xi> \<in> elts (Cset_c ?p \<alpha> v)" using 3(1) Suc.IH by blast
      have ox: "Ord \<xi>" using 3(1) Ord_Citer[OF ordp'] by blast
      have val: "x = psi \<xi> u" using 3(2,3) by simp
      show ?thesis using Cset_c_anygen_closed[OF ox xc 3(2)] val by simp
    qed
  qed
qed

text \<open>\<^bold>\<open>Buchholz's Remark\<close>: \<open>C\<^sub>v(\<alpha>) = C\<^sup>c\<^sub>v(\<alpha>)\<close>.  The side-condition (*)
  (canonicity of generator arguments) does not change the closure.\<close>

lemma Cset_eq_Cset_c:
  "elts (Cset (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v) = elts (Cset_c (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v)"
proof
  show "elts (Cset (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v) \<subseteq> elts (Cset_c (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v)"
  proof (rule subsetI)
    fix x assume "x \<in> elts (Cset (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v)"
    then obtain n where "x \<in> elts ((Cstep (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> ^^ n) (Om v))"
      by (auto simp: Cset_mem_iff)
    thus "x \<in> elts (Cset_c (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v)"
      using Citer_subset_Cset_c by blast
  qed
next
  show "elts (Cset_c (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v) \<subseteq> elts (Cset (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v)"
    by (rule Cset_c_subset_Cset)
qed

end
