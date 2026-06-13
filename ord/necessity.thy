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

end
