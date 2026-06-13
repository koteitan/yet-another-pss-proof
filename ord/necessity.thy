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

end
