theory embed
  imports wf wo wflevel buchholz
begin

section \<open>Embedding the PSS notation into the well-foundedness core\<close>

text \<open>
  The PSS notation \<^typ>\<open>three\<close> (\<open>p\<^sub>a(b)+c\<close>, with the naive subscript-first order
  \<open>olt\<close> = \<open><o\<close> from \<^theory>\<open>YAPSS.mechanized\<close>) is mapped into Towsner's well-founded
  ordinal terms \<^typ>\<open>ot\<close> (\<^theory>\<open>YAPSS.wo\<close>) by reading each principal \<open>p\<^sub>a(b)\<close> as the
  collapsing term \<open>\<vartheta>\<^sub>a b\<close> (\<^const>\<open>Th\<close>) and the \<open>+\<close>-chain as the natural sum
  (\<^const>\<open>Su\<close>).

  A subtlety: Towsner's sums must have length \<open>\<noteq> 1\<close> (a lone principal is \<^emph>\<open>not\<close>
  written as a sum, and indeed \<open>Su [x] \<noteq> x\<close> under \<open><\<^sub>o\<close>).  So \<open>collapse\<close> turns the
  list of principal summands into \<open>Zero\<close> (empty), the bare principal (singleton),
  or a genuine \<open>Su\<close> (length \<open>\<ge> 2\<close>).  This makes the image well-formed (\<^const>\<open>wfo\<close>).

  The plan: prove this map is order-preserving on \<open>NF\<close> (where the naive order
  coincides with the true collapsing order), so well-foundedness of \<open><\<^sub>o\<close>
  transfers to \<open>NF\<close>, discharging the diagonal accessibility obligation.
\<close>

definition collapse :: "ot list \<Rightarrow> ot" where
  "collapse xs = (case xs of [] \<Rightarrow> Su [] | [x] \<Rightarrow> x | _ \<Rightarrow> Su xs)"

lemma collapse_Nil [simp]: "collapse [] = Su []"
  by (simp add: collapse_def)

lemma collapse_single [simp]: "collapse [x] = x"
  by (simp add: collapse_def)

lemma collapse_cons2 [simp]: "collapse (x # y # ys) = Su (x # y # ys)"
  by (simp add: collapse_def)

text \<open>\<open>eprincs t\<close> is the list of principal summands of \<open>t\<close>; \<open>embed t\<close> collapses it.\<close>

fun eprincs :: "three \<Rightarrow> ot list" where
  "eprincs Z = []"
| "eprincs (P a b c) = Th (int a) (collapse (eprincs b)) # eprincs c"

definition embed :: "three \<Rightarrow> ot" where
  "embed t = collapse (eprincs t)"

lemma embed_Z [simp]: "embed Z = Zero"
  by (simp add: embed_def)

lemma eprincs_P [simp]:
  "eprincs (P a b c) = Th (int a) (embed b) # eprincs c"
  by (simp add: embed_def)

text \<open>\<open>collapse\<close> of a list of well-formed principals is well-formed.\<close>

lemma wfo_collapse:
  assumes "\<forall>x \<in> set xs. isH x \<and> wfo x" shows "wfo (collapse xs)"
proof (cases xs)
  case Nil thus ?thesis by simp
next
  case (Cons x ys)
  show ?thesis
  proof (cases ys)
    case Nil thus ?thesis using Cons assms by simp
  next
    case (Cons y zs) thus ?thesis using \<open>xs = x # ys\<close> assms by auto
  qed
qed

text \<open>Every summand produced by the embedding is a principal \<vartheta>-term whose
  argument is itself a well-formed image; hence the image is well-formed.\<close>

lemma eprincs_props: "x \<in> set (eprincs t) \<Longrightarrow> isH x \<and> wfo x"
proof (induction t arbitrary: x)
  case (P a b c)
  from P.prems consider "x = Th (int a) (embed b)" | "x \<in> set (eprincs c)"
    by (auto simp: embed_def)
  thus ?case
  proof cases
    case 1
    have "\<forall>y \<in> set (eprincs b). isH y \<and> wfo y" using P.IH(1) by blast
    hence "wfo (embed b)" unfolding embed_def by (rule wfo_collapse)
    thus ?thesis using 1 by simp
  next
    case 2
    show ?thesis by (rule P.IH(2)[OF 2])
  qed
qed simp

lemma wfo_embed: "wfo (embed t)"
  unfolding embed_def by (rule wfo_collapse) (use eprincs_props in auto)

text \<open>The embedding never produces an \<open>\<Omega>\<close>: every image term is \<^const>\<open>omfree\<close>.  This is
  why the well-foundedness target may be (and must be) restricted to the \<open>\<Omega>\<close>-free
  terms \<dash> the full \<^typ>\<open>int\<close>-level order is ill-founded via \<open>\<Omega>\<^bsub>-k\<^esub>\<close>.\<close>

lemma omfree_collapse:
  assumes "\<forall>x \<in> set xs. omfree x" shows "omfree (collapse xs)"
proof (cases xs)
  case Nil thus ?thesis by simp
next
  case (Cons x ys)
  show ?thesis
  proof (cases ys)
    case Nil thus ?thesis using Cons assms by simp
  next
    case (Cons y zs) thus ?thesis using \<open>xs = x # ys\<close> assms by auto
  qed
qed

lemma omfree_eprincs: "x \<in> set (eprincs t) \<Longrightarrow> omfree x"
proof (induction t arbitrary: x)
  case (P a b c)
  from P.prems consider "x = Th (int a) (embed b)" | "x \<in> set (eprincs c)"
    by (auto simp: embed_def)
  thus ?case
  proof cases
    case 1
    have "omfree (embed b)" unfolding embed_def
      by (rule omfree_collapse) (use P.IH(1) in auto)
    thus ?thesis using 1 by simp
  next
    case 2 show ?thesis by (rule P.IH(2)[OF 2])
  qed
qed simp

lemma omfree_embed: "omfree (embed t)"
  unfolding embed_def by (rule omfree_collapse) (use omfree_eprincs in auto)

text \<open>The embedding produces only \<^bold>\<open>nonnegative\<close> subscripts: every \<open>\<vartheta>\<close> uses
  \<open>\<vartheta>\<^bsub>int a\<^esub>\<close> with \<open>a : nat\<close>, so the image lands in the \<open>nneg\<close> fragment \<dash> exactly the
  one on which @{thm [source] wf_oltRwF} is well-founded.\<close>

lemma nneg_collapse:
  assumes "\<forall>x \<in> set xs. nneg x" shows "nneg (collapse xs)"
proof (cases xs)
  case Nil thus ?thesis by simp
next
  case (Cons x ys)
  show ?thesis
  proof (cases ys)
    case Nil thus ?thesis using Cons assms by simp
  next
    case (Cons y zs) thus ?thesis using \<open>xs = x # ys\<close> assms by auto
  qed
qed

lemma nneg_eprincs: "x \<in> set (eprincs t) \<Longrightarrow> nneg x"
proof (induction t arbitrary: x)
  case (P a b c)
  from P.prems consider "x = Th (int a) (embed b)" | "x \<in> set (eprincs c)"
    by (auto simp: embed_def)
  thus ?case
  proof cases
    case 1
    have "nneg (embed b)" unfolding embed_def
      by (rule nneg_collapse) (use P.IH(1) in auto)
    thus ?thesis using 1 by simp
  next
    case 2 show ?thesis by (rule P.IH(2)[OF 2])
  qed
qed simp

lemma nneg_embed: "nneg (embed t)"
  unfolding embed_def by (rule nneg_collapse) (use nneg_eprincs in auto)

text \<open>The principal \<^const>\<open>bag\<close> of an embedded term is exactly the (multiset of the)
  list of its principal summands \<^const>\<open>eprincs\<close>.  This lets the order-preservation
  argument reason about \<open><\<^sub>o\<close> on sums via the Dershowitz\<dash>Manna multiset extension
  over the principals.\<close>

lemma bag_collapse:
  assumes "\<forall>x \<in> set xs. isH x" shows "bag (collapse xs) = mset xs"
proof (cases xs)
  case Nil thus ?thesis by simp
next
  case (Cons y ys)
  show ?thesis
  proof (cases ys)
    case Nil thus ?thesis using Cons assms by (cases y) auto
  next
    case (Cons z zs) thus ?thesis using \<open>xs = y # ys\<close> by simp
  qed
qed

lemma bag_embed: "bag (embed t) = mset (eprincs t)"
proof -
  have "\<forall>x \<in> set (eprincs t). isH x" using eprincs_props by blast
  from bag_collapse[OF this] show ?thesis by (simp only: embed_def)
qed

lemma bag_embed_P: "bag (embed (P a b c)) = {# Th (int a) (embed b) #} + bag (embed c)"
  by (simp add: bag_embed del: eprincs.simps)

text \<open>Every principal summand of \<open>embed c\<close> is a collapse \<open>\<vartheta>\<^bsub>int s\<^esub>(\<dots>)\<close> whose
  subscript \<open>s\<close> is one of \<open>c\<close>'s top-level sibling subscripts \<^const>\<open>tops\<close>.\<close>

lemma eprincs_form:
  "x \<in> set (eprincs c) \<Longrightarrow> \<exists>s h. x = Th (int s) (embed h) \<and> s \<in> set (tops c)"
proof (induction c)
  case Z thus ?case by simp
next
  case (P e f g)
  from P.prems consider "x = Th (int e) (embed f)" | "x \<in> set (eprincs g)"
    by (auto simp del: eprincs.simps)
  thus ?case
  proof cases
    case 1 thus ?thesis by auto
  next
    case 2 with P.IH obtain s h where "x = Th (int s) (embed h)" "s \<in> set (tops g)" by blast
    thus ?thesis by auto
  qed
qed

text \<open>Hence if every top-level sibling subscript of \<open>c\<close> is \<open>< n\<close>, all principal
  summands of \<open>embed c\<close> are below \<open>\<vartheta>\<^bsub>n\<^esub> D\<close> (for any \<open>D\<close>) \<dash> the subscript drop
  dominates (@{thm [source] Th_lt_of_sub_lt}).\<close>

lemma eprincs_lt_Th:
  assumes "\<forall>s \<in> set (tops c). int s < n" "x \<in> set (eprincs c)"
  shows "x <\<^sub>o Th n D"
proof -
  from eprincs_form[OF assms(2)] obtain s h
    where x: "x = Th (int s) (embed h)" and s: "s \<in> set (tops c)" by blast
  have "int s < n" using assms(1) s by blast
  thus ?thesis using x Th_lt_of_sub_lt[OF omfree_embed] by simp
qed

lemma embed_P_neq_Zero: "embed (P e f g) \<noteq> Zero"
proof (cases "eprincs g")
  case Nil
  hence "embed (P e f g) = Th (int e) (embed f)" by (simp add: embed_def)
  thus ?thesis by simp
next
  case (Cons y ys)
  hence "embed (P e f g) = Su (Th (int e) (embed f) # y # ys)" by (simp add: embed_def)
  thus ?thesis by simp
qed

text \<open>Dershowitz\<dash>Manna single-dominator step for collapses: if a principal \<open>c\<close>
  strictly dominates every summand of \<open>collapse xs\<close>, occurs in \<open>ys\<close>, and is absent
  from \<open>xs\<close>, then \<open>collapse xs <\<^sub>o collapse ys\<close>.  Covers all the \<open>Zero\<close>/singleton/sum
  shape combinations uniformly.\<close>

lemma collapse_neq_Zero:
  assumes "c \<in> set ys" "isH c" shows "collapse ys \<noteq> Zero"
proof (cases ys)
  case Nil thus ?thesis using assms(1) by simp
next
  case yC: (Cons y1 yr)
  show ?thesis
  proof (cases yr)
    case Nil thus ?thesis using yC assms by (cases c) auto
  next
    case (Cons y2 yr2) thus ?thesis using yC by simp
  qed
qed

lemma collapse_lt_dom:
  assumes hx: "\<forall>\<alpha>\<in>set xs. isH \<alpha>"
    and hc: "isH c"
    and dom: "\<forall>\<alpha>\<in>set xs. \<alpha> <\<^sub>o c"
    and cy: "c \<in> set ys"
    and cnotx: "c \<notin> set xs"
  shows "collapse xs <\<^sub>o collapse ys"
proof (cases xs)
  case Nil
  have "collapse ys \<noteq> Zero" using collapse_neq_Zero[OF cy hc] .
  thus ?thesis using Nil by (simp add: olt_ZeroI)
next
  case xC: (Cons x1 xr)
  show ?thesis
  proof (cases xr)
    case Nil
    have x1: "x1 \<in> set xs" using xC by simp
    have hx1: "isH x1" using hx x1 by simp
    have x1c: "x1 <\<^sub>o c" using dom x1 by simp
    have cxs: "collapse xs = x1" using xC Nil by simp
    show ?thesis
    proof (cases ys)
      case Nil thus ?thesis using cy by simp
    next
      case yC: (Cons y1 yr)
      show ?thesis
      proof (cases yr)
        case Nil
        have "y1 = c" using cy yC Nil by simp
        thus ?thesis using cxs yC Nil x1c by simp
      next
        case (Cons y2 yr2)
        have "x1 <\<^sub>o Su ys" using hx1 x1c cy by (cases x1) auto
        thus ?thesis using cxs yC Cons by simp
      qed
    qed
  next
    case xC2: (Cons x2 xr2)
    have cxs: "collapse xs = Su xs" using xC xC2 by simp
    show ?thesis
    proof (cases ys)
      case Nil thus ?thesis using cy by simp
    next
      case yC: (Cons y1 yr)
      show ?thesis
      proof (cases yr)
        case Nil
        have yc: "y1 = c" using cy yC Nil by simp
        have "Su xs <\<^sub>o c" using hc dom by (cases c) auto
        thus ?thesis using cxs yC Nil yc by simp
      next
        case (Cons y2 yr2)
        have cys: "collapse ys = Su ys" using yC Cons by simp
        have cin: "c \<in># mset ys - mset xs"
        proof -
          have z: "count (mset xs) c = 0" using cnotx by (simp add: count_eq_zero_iff)
          have p: "0 < count (mset ys) c" using cy by (simp add: count_greater_zero_iff)
          have "count (mset xs) c < count (mset ys) c" using z p by linarith
          thus ?thesis by (simp add: in_diff_count)
        qed
        have "\<forall>\<alpha>\<in>#mset xs - mset ys. \<alpha> <\<^sub>o c"
          using dom by (auto dest: in_diffD)
        hence "Su xs <\<^sub>o Su ys" using cin by auto
        thus ?thesis using cxs cys by simp
      qed
    qed
  qed
qed

section \<open>Order-preservation of \<open>embed\<close> on \<open>NF\<close> (the embedding obligation \<open>op\<close>)\<close>

text \<open>\<^bold>\<open>Order-preservation (P/P case sorried):\<close> on \<open>NF\<close>, the naive subscript order \<open><o\<close>
  (\<^theory>\<open>YAPSS.mechanized\<close>) is refined by the collapsing order \<open><\<^sub>o\<close>.  The \<open>Z\<close> cases
  are immediate; the principal (\<open>P\<close>/\<open>P\<close>) case needs the \<open>NF\<close> invariants (the
  built-from-below / spine bounds of \<^theory>\<open>YAPSS.wf\<close>) to discharge the critical-subterm
  (\<open>K\<close>) conditions of \<open><\<^sub>o\<close>.  This is one of the remaining obligations.\<close>

theorem op_NF:
  assumes "w \<in> NF" "x \<in> NF" "w <o x"
  shows "embed w <\<^sub>o embed x"
proof (cases w)
  case Z
  have "x \<noteq> Z" using assms(3) Z olt_Z_iff by blast
  then obtain e f g where x: "x = P e f g" by (cases x) auto
  show ?thesis using Z x embed_P_neq_Zero by (simp add: olt_ZeroI)
next
  case (P a b c)
  have "x \<noteq> Z" using assms(3) olt_Z_iff by blast
  then obtain e f g where x: "x = P e f g" by (cases x) auto
  \<comment> \<open>principal/principal: needs the \<open>NF\<close> K-condition (built-from-below)\<close>
  show ?thesis sorry
qed

section \<open>Wiring: the remaining obligations imply \<open>wf Rnf\<close>\<close>

text \<open>Well-foundedness on the \<open>\<Omega>\<close>-free terms (\<^const>\<open>oltRwF\<close>, @{thm [source] wf_oltRwF},
  reduced to the single core @{thm [source] masterF}) plus order-preservation of
  \<^const>\<open>embed\<close> on \<open>NF\<close> discharge \<^prop>\<open>wf Rnf\<close>, hence PSS termination.  The image
  of \<^const>\<open>embed\<close> is well-formed (@{thm [source] wfo_embed}) and \<open>\<Omega>\<close>-free
  (@{thm [source] omfree_embed}), so it lands inside \<^const>\<open>oltRwF\<close>.\<close>

theorem wf_Rnf_via_embed:
  assumes op: "\<And>w x. w \<in> NF \<Longrightarrow> x \<in> NF \<Longrightarrow> w <o x \<Longrightarrow> embed w <\<^sub>o embed x"
  shows "wf Rnf"
proof -
  have wfT: "wf (inv_image oltRwF embed)"
    by (rule wf_inv_image[OF wf_oltRwF])
  have sub: "Rnf \<subseteq> inv_image oltRwF embed"
  proof (rule subsetI)
    fix p assume "p \<in> Rnf"
    then obtain v u where p: "p = (v, u)" and "v <o u" "u \<in> NF" "v \<in> NF" by auto
    have "embed v <\<^sub>o embed u" using op[OF \<open>v \<in> NF\<close> \<open>u \<in> NF\<close> \<open>v <o u\<close>] .
    thus "p \<in> inv_image oltRwF embed"
      using p wfo_embed omfree_embed nneg_embed by (simp add: inv_image_def)
  qed
  show "wf Rnf" by (rule wf_subset[OF wfT sub])
qed

text \<open>End-to-end: PSS termination follows from the single embedding obligation
  \<open>op\<close> (order-preservation on \<open>NF\<close>), with the well-foundedness core @{thm [source]
  masterF} as the only other (internal) gap.\<close>

theorem step_terminates_via_embed:
  assumes op: "\<And>w x. w \<in> NF \<Longrightarrow> x \<in> NF \<Longrightarrow> w <o x \<Longrightarrow> embed w <\<^sub>o embed x"
  shows "wf {(T, M). M \<in> ST_PS \<and> step M T}"
  by (rule step_terminates[OF wf_Rnf_via_embed[OF op]])

text \<open>Discharging \<open>op\<close> by @{thm [source] op_NF}: PSS termination, modulo the three
  remaining internal cores (@{thm [source] masterF}'s collapse closure \<open>L_ThF\<close> at
  the cross-subscript case, the order-meta lemma \<open>olt_trans\<close> at the sum case, and the
  \<open>P\<close>/\<open>P\<close> case of @{thm [source] op_NF}).\<close>

theorem step_terminates_NF: "wf {(T, M). M \<in> ST_PS \<and> step M T}"
  by (rule step_terminates_via_embed[OF op_NF])

end
