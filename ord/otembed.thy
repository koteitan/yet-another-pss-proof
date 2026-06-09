theory otembed
  imports psi "YAPSS.mechanized"
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

text \<open>The head order \<open>hdle\<close> is transitive, so in a well-formed term every spine
  principal is dominated by the leading one.\<close>

lemma hdle_trans:
  assumes "hdle x y" "hdle y z" shows "hdle x z"
proof (cases x)
  case Z thus ?thesis by simp
next
  case (P ax bx cx)
  obtain ay byy cy where y: "y = P ay byy cy" using assms(1) P by (cases y) auto
  obtain az bz cz where z: "z = P az bz cz" using assms(2) y by (cases z) auto
  have H1: "ax < ay \<or> (ax = ay \<and> (olt bx byy \<or> bx = byy))" using assms(1) P y by simp
  have H2: "ay < az \<or> (ay = az \<and> (olt byy bz \<or> byy = bz))" using assms(2) y z by simp
  have "ax < az \<or> (ax = az \<and> (olt bx bz \<or> bx = bz))"
  proof -
    consider (lt) "ax < ay" | (eq) "ax = ay" "olt bx byy \<or> bx = byy" using H1 by blast
    thus ?thesis
    proof cases
      case lt
      have "ay \<le> az" using H2 by auto
      hence "ax < az" using less_le_trans[OF lt] by blast
      thus ?thesis ..
    next
      case eq
      consider (lt2) "ay < az" | (eq2) "ay = az" "olt byy bz \<or> byy = bz" using H2 by blast
      thus ?thesis
      proof cases
        case lt2
        have "ax < az" using eq(1) lt2 by simp
        thus ?thesis ..
      next
        case eq2
        have "ax = az" using eq(1) eq2(1) by simp
        moreover have "olt bx bz \<or> bx = bz" using eq(2) eq2(2) by (metis olt_trans)
        ultimately show ?thesis by simp
      qed
    qed
  qed
  thus ?thesis using P z by simp
qed

fun headle_all :: "three \<Rightarrow> three \<Rightarrow> bool" where
  "headle_all bnd Z = True"
| "headle_all bnd (P a b c) = (hdle (P a b Z) bnd \<and> headle_all bnd c)"

lemma hdle_head_ignores_tail: "hdle (P a b c) z = hdle (P a b Z) z"
  by (cases z) auto

lemma wf3_headle_aux: "wf3 t \<Longrightarrow> hdle t bnd \<Longrightarrow> headle_all bnd t"
proof (induction t)
  case Z thus ?case by simp
next
  case (P a b c)
  note IHc = P.IH(2)
  have wfc: "wf3 c" and hdc: "hdle c (P a b Z)" using P.prems(1) by auto
  have hd: "hdle (P a b Z) bnd" by (metis P.prems(2) hdle_head_ignores_tail)
  have "hdle c bnd" using hdc hd by (rule hdle_trans)
  hence "headle_all bnd c" using IHc[OF wfc] by simp
  thus ?case using hd by simp
qed

lemma wf3_headle: "wf3 (P a b c) \<Longrightarrow> headle_all (P a b Z) c"
proof -
  assume w: "wf3 (P a b c)"
  hence "wf3 c" and "hdle c (P a b Z)" by auto
  thus ?thesis by (rule wf3_headle_aux)
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

text \<open>\<^bold>\<open>Building values inside \<open>C\<close>\<close>: if every \<open>G\<^sub>v\<close>-critical subterm of \<open>t\<close> has value
  \<open>< \<alpha>\<close>, then \<open>o(t) \<in> C\<^sub>v(\<alpha>)\<close>.  (Subscripts \<open>< v\<close> contribute \<open>\<psi>\<^sub>a(\<cdot>) < \<Omega>\<^bsub>a+1\<^esub> \<le> \<Omega>\<^sub>v \<subseteq> C\<close>;
  subscripts \<open>\<ge> v\<close> are \<open>G\<close>-collected, so their arguments are below \<open>\<alpha>\<close> and the
  \<open>\<psi>\<close>-closure of \<open>C\<close> applies; sums by \<open>+\<close>-closure.)  No well-formedness needed.\<close>

lemma C_build:
  assumes "\<And>x. x \<in> Gterm v t \<Longrightarrow> oV x \<in> elts \<alpha>"
  shows "oV t \<in> elts (Cset (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v)"
  using assms
proof (induction t)
  case Z
  have z0: "(0::V) \<in> elts (Om v)"
  proof -
    have "(0::V) \<in> elts 1" by simp
    moreover have "elts 1 \<subseteq> elts (Om v)" using one_le_Om less_eq_V_def by blast
    ultimately show ?thesis by blast
  qed
  have "oV Z = 0" by simp
  thus ?case using z0 Om_subset_Cset by fastforce
next
  case (P a b c)
  have IHc: "oV c \<in> elts (Cset (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v)"
    using P.IH(2) P.prems by (simp add: restrict_def)
  have head: "psi (oV b) a \<in> elts (Cset (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v)"
  proof (cases "v \<le> a")
    case True
    have bG: "b \<in> Gterm v (P a b c)" using True by simp
    have bmem: "oV b \<in> elts \<alpha>" using P.prems[OF bG] .
    have IHb: "oV b \<in> elts (Cset (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v)"
      using P.IH(1) P.prems True by (simp add: restrict_def)
    have "(\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) (oV b) a \<in> elts (Cset (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v)"
      by (rule Cset_psi_closed[OF IHb bmem])
    thus ?thesis using bmem by (simp add: restrict_def)
  next
    case False
    have av: "a < v" using False by simp
    have "psi (oV b) a < Om (Suc a)" by (rule psi_lt_Om_Suc)
    also have "Om (Suc a) \<le> Om v" using av by (simp add: Om_mono Suc_leI)
    finally have "psi (oV b) a < Om v" .
    hence "psi (oV b) a \<in> elts (Om v)"
      using Ord_mem_iff_lt[OF Ord_psi Ord_Om] by blast
    thus ?thesis using Om_subset_Cset by blast
  qed
  have "psi (oV b) a + oV c \<in> elts (Cset (\<lambda>\<xi>\<in>elts \<alpha>. psi \<xi>) \<alpha> v)"
    by (rule Cset_add_closed[OF head IHc])
  thus ?case by (simp add: restrict_def)
qed

text \<open>The C-membership needed by 1.3, from order-preservation below the argument:
  if every critical subterm's value is \<open>< o(b)\<close>, then \<open>o(b) \<in> C\<^sub>a(o(b))\<close>.\<close>

lemma Ccond_of_lt:
  assumes "\<And>x. x \<in> Gterm a b \<Longrightarrow> oV x < oV b"
  shows "oV b \<in> elts (Cset (\<lambda>\<xi>\<in>elts (oV b). psi \<xi>) (oV b) a)"
proof (rule C_build)
  fix x assume "x \<in> Gterm a b"
  hence "oV x < oV b" by (rule assms)
  thus "oV x \<in> elts (oV b)" using Ord_mem_iff_lt[OF Ord_oV Ord_oV] by blast
qed

text \<open>\<open>G\<close>-critical subterms are well-formed and structurally smaller
  (Buchholz's Proposition \<open>a \<in> OT \<Rightarrow> G\<^sub>ua \<subseteq> OT\<close>).\<close>

lemma wf3_Gterm: "wf3 t \<Longrightarrow> x \<in> Gterm v t \<Longrightarrow> wf3 x"
proof (induction t)
  case Z thus ?case by simp
next
  case (P a b c)
  have wfb: "wf3 b" and wfc: "wf3 c" using P.prems(1) by auto
  from P.prems(2) consider "v \<le> a \<and> x = b" | "v \<le> a \<and> x \<in> Gterm v b" | "x \<in> Gterm v c"
    by (auto split: if_split_asm)
  thus ?case
  proof cases
    case 1 thus ?thesis using wfb by simp
  next
    case 2 thus ?thesis using P.IH(1) wfb by blast
  next
    case 3 thus ?thesis using P.IH(2) wfc by blast
  qed
qed

lemma Gterm_size: "x \<in> Gterm v t \<Longrightarrow> size x < size t"
proof (induction t)
  case Z thus ?case by simp
next
  case (P a b c)
  from P.prems consider "v \<le> a \<and> x = b" | "v \<le> a \<and> x \<in> Gterm v b" | "x \<in> Gterm v c"
    by (auto split: if_split_asm)
  thus ?case
  proof cases
    case 1 thus ?thesis by simp
  next
    case 2 thus ?thesis using P.IH(1) by fastforce
  next
    case 3 thus ?thesis using P.IH(2) by fastforce
  qed
qed

text \<open>Every spine principal of a well-formed term whose head is dominated by \<open>D\<^bsub>a\<^esub>(b)\<close>
  (with \<open>b \<prec> f\<close>) is \<open>< \<psi>\<^bsub>a\<^esub>(o f)\<close>: subscript-smaller ones by the jump, subscript-equal
  ones by strict monotonicity 1.3 (\<open>mono\<close> supplies \<open>o b' < o f\<close> from the outer IH,
  \<open>Ccond\<close> the C-membership).\<close>

lemma allprinc_lt_spine:
  assumes mono: "\<And>b'. olt b' f \<Longrightarrow> wf3 b' \<Longrightarrow> size b' < n \<Longrightarrow> oV b' < oV f"
    and ccnd: "\<And>a' b' c''. wf3 (P a' b' c'') \<Longrightarrow> size b' < n
                  \<Longrightarrow> oV b' \<in> elts (Cset (\<lambda>\<xi>\<in>elts (oV b'). psi \<xi>) (oV b') a')"
    and bf: "olt b f"
  shows "headle_all (P a b Z) c \<Longrightarrow> wf3 c \<Longrightarrow> size c < n \<Longrightarrow> allprinc_lt (psi (oV f) a) c"
proof (induction c)
  case Z thus ?case by simp
next
  case (P a' b' c'')
  have hd: "hdle (P a' b' Z) (P a b Z)" and hall: "headle_all (P a b Z) c''"
    using P.prems(1) by auto
  have wfnode: "wf3 (P a' b' c'')" using P.prems(2) .
  have wfb': "wf3 b'" and wfc'': "wf3 c''" using P.prems(2) by auto
  have sb': "size b' < n" using P.prems(3) by simp
  have szc'': "size c'' < n" using P.prems(3) by simp
  have head: "psi (oV b') a' < psi (oV f) a"
  proof -
    have "a' < a \<or> (a' = a \<and> (olt b' b \<or> b' = b))" using hd by simp
    thus ?thesis
    proof
      assume "a' < a" thus ?thesis by (rule psi_subscript_jump)
    next
      assume "a' = a \<and> (olt b' b \<or> b' = b)"
      hence aa: "a' = a" and bb: "olt b' b \<or> b' = b" by auto
      have "olt b' f" using bb bf by (auto intro: olt_trans)
      have ob: "oV b' < oV f" by (rule mono[OF \<open>olt b' f\<close> wfb' sb'])
      have mem: "oV b' \<in> elts (Cset (\<lambda>\<xi>\<in>elts (oV b'). psi \<xi>) (oV b') a')"
        by (rule ccnd[OF wfnode sb'])
      have "psi (oV b') a' < psi (oV f) a'"
        by (rule psi_strict_mono_arg[OF Ord_oV Ord_oV ob mem])
      thus ?thesis using aa by simp
    qed
  qed
  have "allprinc_lt (psi (oV f) a) c''" using P.IH(2)[OF hall wfc'' szc''] .
  thus ?case using head by simp
qed

text \<open>\<^bold>\<open>Buchholz Lemma 2.2(c)\<close> on \<open>wf3\<close> (= Buchholz \<open>OT\<close>): the value map is strictly
  monotone.  Main induction on the size of the \<^emph>\<open>left\<close> term (Buchholz's induction
  on \<open>|a|\<close>, with the right term arbitrary); the C-membership for 1.3 is supplied
  by \<open>Ccond_of_lt\<close> from the induction hypothesis on the critical subterms (OT3).\<close>

theorem oV_order_pres:
  "wf3 v \<Longrightarrow> wf3 u \<Longrightarrow> olt v u \<Longrightarrow> oV v < oV u"
proof (induction "size v" arbitrary: v u rule: less_induct)
  case less
  have ccnd: "\<And>a' b' c'. wf3 (P a' b' c') \<Longrightarrow> size b' < size v
                \<Longrightarrow> oV b' \<in> elts (Cset (\<lambda>\<xi>\<in>elts (oV b'). psi \<xi>) (oV b') a')"
  proof -
    fix a' b' c' assume wfn: "wf3 (P a' b' c')" and szb': "size b' < size v"
    have wfb': "wf3 b'" using wfn by simp
    have G: "\<forall>x \<in> Gterm a' b'. olt x b'" using wfn by simp
    show "oV b' \<in> elts (Cset (\<lambda>\<xi>\<in>elts (oV b'). psi \<xi>) (oV b') a')"
    proof (rule Ccond_of_lt)
      fix x assume xG: "x \<in> Gterm a' b'"
      have wfx: "wf3 x" by (rule wf3_Gterm[OF wfb' xG])
      have szx: "size x < size b'" by (rule Gterm_size[OF xG])
      have lt: "olt x b'" using G xG by blast
      show "oV x < oV b'"
        by (rule less.hyps[OF _ wfx wfb' lt]) (use szx szb' in simp)
    qed
  qed
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
      have aa: "e = a" using arg by simp
      have wff: "wf3 f" using wfu by simp
      have wfc: "wf3 c" using wfv by simp
      have wfb: "wf3 b" using wfv by simp
      have mono: "\<And>b'. olt b' f \<Longrightarrow> wf3 b' \<Longrightarrow> size b' < size v \<Longrightarrow> oV b' < oV f"
      proof -
        fix b' assume A1: "olt b' f" and A2: "wf3 b'" and A3: "size b' < size v"
        show "oV b' < oV f" by (rule less.hyps[OF A3 A2 wff A1])
      qed
      have hac: "headle_all (P a b Z) c" by (rule wf3_headle[OF wfv])
      have szc: "size c < size v" using P by simp
      have spine: "allprinc_lt (psi (oV f) a) c"
        by (rule allprinc_lt_spine[OF mono ccnd arg(2) hac wfc szc])
      have szb: "size b < size v" using P by simp
      have obf: "oV b < oV f" by (rule mono[OF arg(2) wfb szb])
      have memb: "oV b \<in> elts (Cset (\<lambda>\<xi>\<in>elts (oV b). psi \<xi>) (oV b) a)"
        by (rule ccnd[OF wfv szb])
      have lead: "psi (oV b) a < psi (oV f) a"
        by (rule psi_strict_mono_arg[OF Ord_oV Ord_oV obf memb])
      have "allprinc_lt (psi (oV f) a) (P a b c)" using lead spine by simp
      hence "oV (P a b c) < psi (oV f) a"
        by (rule oV_lt_of_allprinc[OF psi_addprinc])
      also have "psi (oV f) a \<le> oV (P e f g)" using aa psi_le_oV by simp
      finally show ?thesis using P u by simp
    next
      case tail
      have wfc: "wf3 c" using wfv by simp
      have wfg: "wf3 g" using wfu by simp
      have "oV c < oV g"
      proof (rule less.hyps)
        show "size c < size v" using P by simp
        show "wf3 c" by (rule wfc)
        show "wf3 g" by (rule wfg)
        show "olt c g" using tail by simp
      qed
      hence "psi (oV b) a + oV c < psi (oV b) a + oV g" by simp
      thus ?thesis using P u tail by simp
    qed
  qed
qed

subsection \<open>Well-foundedness of \<open>olt\<close> on the Buchholz class \<open>wf3\<close> (Lemma 2.2)\<close>

text \<open>The value map embeds \<open>(wf3, olt)\<close> into the ordinals, so \<open>olt\<close> is well-founded
  on \<open>wf3\<close>.  This is Buchholz's Lemma 2.2 proved (rather than cited): the sole
  ingredient beyond \<section>1 is the strict monotonicity above.\<close>

theorem wf_olt_wf3: "wf {(w,x). olt w x \<and> wf3 w \<and> wf3 x}"
proof (rule wf_subset[OF wf_inv_image[OF wf_VWF, of oV]])
  show "{(w,x). olt w x \<and> wf3 w \<and> wf3 x} \<subseteq> inv_image VWF oV"
  proof (rule subrelI)
    fix w x assume "(w,x) \<in> {(w,x). olt w x \<and> wf3 w \<and> wf3 x}"
    then have "olt w x" "wf3 x" "wf3 w" by auto
    then have "oV w < oV x" using oV_order_pres by blast
    thus "(w,x) \<in> inv_image VWF oV"
      by (simp add: inv_image_def VWF_iff_Ord_less)
  qed
qed

end
