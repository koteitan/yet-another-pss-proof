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

end
