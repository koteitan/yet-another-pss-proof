theory otembed
  imports psi "YAPSS.mechanized"
begin

text \<open>Cross-session sanity test: can we use both \<^typ>\<open>three\<close> (from \<open>mechanized\<close>,
  HOL side) and \<^typ>\<open>V\<close> (from \<open>psi\<close>, ZFC-in-HOL side) in one theory?  The name
  \<^const>\<open>set\<close> is overloaded (\<open>List.set\<close> vs \<open>ZFC_in_HOL.set\<close>); use qualified names.\<close>

definition otest :: "three \<Rightarrow> V" where
  "otest t = (case t of Z \<Rightarrow> 0 | P a b c \<Rightarrow> Om a)"

lemma otest_Z: "otest Z = 0" by (simp add: otest_def)

lemma Ord_otest: "Ord (otest t)" by (cases t) (auto simp: otest_def)

end
