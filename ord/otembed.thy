theory otembed
  imports psi "YAPSS.proofs"
begin

text \<open>\<^bold>\<open>The order embedding \<open>o : three \<Rightarrow> V\<close>\<close> (Buchholz \<section>2) and the resulting
  well-foundedness of \<open>olt\<close> on the standard-form image \<open>NF\<close>, which discharges the
  last hypothesis of \<open>proofs\<close>'s \<open>step_terminates\<close>.

  \<open>three\<close> (from \<open>mechanized\<close>, HOL side) and \<open>V\<close> (from \<open>psi\<close>, ZFC-in-HOL side)
  coexist here.  Note: the infix \<open><o\<close> is ambiguous in this merged context
  (\<open>mechanized.olt\<close> vs HOL's \<open>ordLess2\<close>), so we always write \<open>olt\<close> explicitly.

  \<open>P a b c\<close> is Buchholz's \<open>D\<^bsub>a\<^esub>(b) + c\<close>, so \<open>o (P a b c) = \<psi>\<^bsub>a\<^esub>(o b) + o c\<close>
  and \<open>o Z = 0\<close>.\<close>

fun oV :: "three \<Rightarrow> V" where
  "oV Z = 0"
| "oV (P a b c) = psi (oV b) a + oV c"

lemma Ord_oV [simp, intro]: "Ord (oV t)"
  by (induction t) (auto simp: Ord_add)

lemma psi_le_oV: "psi (oV b) a \<le> oV (P a b c)"
  by (simp add: add_le_cancel_left0)

subsection \<open>Additive-principal sums and the subscript bound\<close>

text \<open>\<open>allprinc_lt d t\<close>: every principal \<open>\<psi>\<^bsub>a'\<^esub>(o b')\<close> along the spine of \<open>t\<close> is \<open>< d\<close>.
  If \<open>d\<close> is additive principal, the whole value \<open>o t\<close> stays \<open>< d\<close>.\<close>

fun allprinc_lt :: "V \<Rightarrow> three \<Rightarrow> bool" where
  "allprinc_lt d Z = True"
| "allprinc_lt d (P a b c) = (psi (oV b) a < d \<and> allprinc_lt d c)"

lemma oV_lt_of_allprinc:
  assumes "addprinc d" "allprinc_lt d t" shows "oV t < d"
  using assms(2)
proof (induction t)
  case Z
  thus ?case using assms(1) by (simp add: addprinc_def)
next
  case (P a b c)
  have h: "psi (oV b) a < d" and t: "allprinc_lt d c" using P.prems by auto
  have "oV c < d" using P.IH t by simp
  hence "psi (oV b) a + oV c < d"
    using assms(1) h Ord_psi Ord_oV unfolding addprinc_def by blast
  thus ?case by simp
qed

text \<open>\<open>spinesub_le m t\<close>: every spine subscript of \<open>t\<close> is \<open>\<le> m\<close>.\<close>

fun spinesub_le :: "nat \<Rightarrow> three \<Rightarrow> bool" where
  "spinesub_le m Z = True"
| "spinesub_le m (P a b c) = (a \<le> m \<and> spinesub_le m c)"

lemma spinesub_le_mono: "spinesub_le m t \<Longrightarrow> m \<le> m' \<Longrightarrow> spinesub_le m' t"
  by (induction t) auto

lemma allprinc_lt_jump:
  "spinesub_le m t \<Longrightarrow> m < e \<Longrightarrow> allprinc_lt (psi \<beta> e) t"
proof (induction t)
  case Z thus ?case by simp
next
  case (P a b c)
  have "a \<le> m" and sc: "spinesub_le m c" using P.prems(1) by auto
  hence "a < e" using P.prems(2) by simp
  hence "psi (oV b) a < psi \<beta> e" by (rule psi_subscript_jump)
  moreover have "allprinc_lt (psi \<beta> e) c" using P.IH sc P.prems(2) by simp
  ultimately show ?case by simp
qed

subsection \<open>Buchholz coefficient sets \<open>G\<^sub>u\<close> and the OT well-formedness predicate\<close>

text \<open>\<open>Gterm u t\<close> = Buchholz's \<open>G\<^sub>u\<close> on terms: for the principal \<open>D\<^bsub>a\<^esub>(b)\<close>, it is
  \<open>{b} \<union> G\<^sub>u b\<close> when \<open>u \<le> a\<close>, else \<open>\<emptyset>\<close>; on a sum it is the union.\<close>

fun Gterm :: "nat \<Rightarrow> three \<Rightarrow> three set" where
  "Gterm u Z = {}"
| "Gterm u (P a b c) = (if u \<le> a then insert b (Gterm u b) else {}) \<union> Gterm u c"

text \<open>\<open>hdle x y\<close>: the principal head of \<open>x\<close> is \<open>\<le>\<close> that of \<open>y\<close> (subscript-first, tails ignored).\<close>

fun hdle :: "three \<Rightarrow> three \<Rightarrow> bool" where
  "hdle Z y = True"
| "hdle (P a b c) Z = False"
| "hdle (P a b c) (P e f g) = (a < e \<or> (a = e \<and> (olt b f \<or> b = f)))"

text \<open>\<open>wf3 t\<close>: \<open>t\<close> is a Buchholz OT term — recursively well-formed, the OT3 condition
  \<open>G\<^sub>a b < b\<close> for each principal \<open>D\<^bsub>a\<^esub>(b)\<close>, and OT2 non-increasing spine.\<close>

fun wf3 :: "three \<Rightarrow> bool" where
  "wf3 Z = True"
| "wf3 (P a b c) = (wf3 b \<and> wf3 c \<and> (\<forall>x\<in>Gterm a b. olt x b) \<and> hdle c (P a b Z))"

lemma wf3_spinesub_le: "wf3 t \<Longrightarrow> spinesub_le (lead t) t"
proof (induction t)
  case Z thus ?case by simp
next
  case (P a b c)
  note IHc = P.IH(2)
  have wfc: "wf3 c" and hd: "hdle c (P a b Z)" using P.prems by auto
  have "spinesub_le a c"
  proof (cases c)
    case Z thus ?thesis by simp
  next
    case (P a' b' c')
    have "a' \<le> a" using hd P by auto
    have "spinesub_le a' c" using IHc[OF wfc] P by simp
    thus ?thesis using \<open>a' \<le> a\<close> spinesub_le_mono by blast
  qed
  thus ?case by simp
qed

subsection \<open>Order preservation on the standard-form image (Buchholz Lemma 2.2(c))\<close>

text \<open>\<^bold>\<open>Residual obligation\<close> (the genuine Buchholz-level core): the embedding is
  strictly monotone on \<open>NF = translate ` ST_PS\<close>.  To be proved from \<section>1
  (\<open>\<psi>\<^sub>v\<close> additive-principal 1.2(b), the bound 1.2(c) \<open>psi_lt_Om_Suc\<close>, and strict
  monotonicity 1.3 \<open>psi_strict_mono_arg\<close>) together with the standard-form
  (Buchholz OT) well-formedness of \<open>translate ` ST_PS\<close>.\<close>

lemma oV_pos: "0 < oV (P a b c)"
proof -
  have "0 < psi (oV b) a" using psi_addprinc[of "oV b" a] by (simp add: addprinc_def)
  also have "psi (oV b) a \<le> oV (P a b c)" by (rule psi_le_oV)
  finally show ?thesis .
qed

text \<open>\<^bold>\<open>Buchholz Lemma 2.2(c)\<close> on well-formed (OT) terms: \<open>o\<close> is strictly monotone.
  Subscript and tail cases are direct; the argument case uses strict monotonicity
  1.3 via the C-membership \<open>o b \<in> C\<^sub>a(o b)\<close> (Buchholz OT3, lemma \<open>Ccond\<close>).\<close>

lemma Ccond:
  assumes "wf3 (P a b c)"
  shows "oV b \<in> elts (Cset (\<lambda>\<xi>\<in>elts (oV b). psi \<xi>) (oV b) a)"
  sorry

lemma oV_order_pres:
  "wf3 v \<Longrightarrow> wf3 u \<Longrightarrow> olt v u \<Longrightarrow> oV v < oV u"
proof (induction "size u + size v" arbitrary: u v rule: less_induct)
  case less
  show ?case
  proof (cases v)
    case Z
    have "u \<noteq> Z" using less.prems(3) Z by (cases u) auto
    then obtain e f g where u: "u = P e f g" by (cases u) auto
    show ?thesis using Z u oV_pos by simp
  next
    case (P a b c)
    have "u \<noteq> Z" using less.prems(3) P by (cases u) auto
    then obtain e f g where u: "u = P e f g" by (cases u) auto
    have wfv: "wf3 (P a b c)" using less.prems(1) P by simp
    have wfu: "wf3 (P e f g)" using less.prems(2) u by simp
    have olt: "olt (P a b c) (P e f g)" using less.prems(3) P u by simp
    consider (sub) "a < e" | (arg) "a = e" "olt b f" | (tail) "a = e" "b = f" "olt c g"
      using olt by auto
    then show ?thesis
    proof cases
      case sub
      have sple: "spinesub_le a (P a b c)" using wf3_spinesub_le[OF wfv] by simp
      have "allprinc_lt (psi (oV f) e) (P a b c)"
        by (rule allprinc_lt_jump[OF sple sub])
      hence "oV (P a b c) < psi (oV f) e"
        by (rule oV_lt_of_allprinc[OF psi_addprinc])
      also have "psi (oV f) e \<le> oV (P e f g)" by (rule psi_le_oV)
      finally show ?thesis using P u by simp
    next
      case arg
      show ?thesis sorry
    next
      case tail
      have wfc: "wf3 c" using wfv by simp
      have wfg: "wf3 g" using wfu by simp
      have "oV c < oV g"
      proof (rule less.hyps)
        show "size g + size c < size u + size v" using P u by simp
        show "wf3 c" by (rule wfc)
        show "wf3 g" by (rule wfg)
        show "olt c g" using tail by simp
      qed
      hence "psi (oV b) a + oV c < psi (oV b) a + oV g" by simp
      thus ?thesis using P u tail by simp
    qed
  qed
qed

lemma NF_wf3: "t \<in> NF \<Longrightarrow> wf3 t"
  sorry

lemma oV_order_pres_NF:
  assumes "u \<in> NF" "v \<in> NF" "olt v u"
  shows "oV v < oV u"
  using oV_order_pres[OF NF_wf3[OF assms(2)] NF_wf3[OF assms(1)] assms(3)] .

subsection \<open>Well-foundedness of \<open>olt\<close> on \<open>NF\<close>, and PSS termination\<close>

theorem wf_Rnf: "wf {(v,u). olt v u \<and> u \<in> NF \<and> v \<in> NF}"
proof (rule wf_subset[OF wf_inv_image[OF wf_VWF, of oV]])
  show "{(v,u). olt v u \<and> u \<in> NF \<and> v \<in> NF} \<subseteq> inv_image VWF oV"
  proof (rule subrelI)
    fix v u assume "(v,u) \<in> {(v,u). olt v u \<and> u \<in> NF \<and> v \<in> NF}"
    then have "olt v u" "u \<in> NF" "v \<in> NF" by auto
    then have "oV v < oV u" using oV_order_pres_NF by blast
    thus "(v,u) \<in> inv_image VWF oV"
      by (simp add: inv_image_def VWF_iff_Ord_less)
  qed
qed

theorem PSS_terminates: "wf {(T,M). M \<in> ST_PS \<and> step M T}"
  by (rule step_terminates[OF wf_Rnf])

end
