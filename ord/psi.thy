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

end
