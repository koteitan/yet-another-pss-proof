theory mechanized
  imports def
begin

section \<open>The ordinal notation \<open>p_a(b)+c\<close>\<close>

text \<open>
  \<^term>\<open>P a b c\<close> denotes \<open>p\<^bsub>a\<^esub>(b) + c\<close>: a principal term \<open>p\<^bsub>a\<^esub>(b)\<close> with
  natural-number subscript \<open>a\<close> (the row-1 value of a pair) and argument \<open>b\<close>
  (the sub-forest), followed by the rest of the sum \<open>c\<close>.  \<^term>\<open>Z\<close> denotes \<open>0\<close>.
  This generalises the PrSS notation \<open>E a b = \<omega>\<^bsup>a\<^esup> + b\<close>: the single exponent
  \<open>\<omega>\<^bsup>a\<^esup>\<close> is replaced by the subscripted \<open>p\<^bsub>a\<^esub>(b)\<close>.

  The order \<open><o\<close> is the lexicographic order on principal terms with the
  subscript taken first (subscript-first): this is the unique direction under
  which the expansion step strictly decreases the translate (empirically
  verified, 4002/4002 steps; argument-first fails).  Termination targets the
  Buchholz ordinal \<open>\<psi>\<^sub>0(\<psi>\<^sub>\<omega>(0))\<close>, matching natural-number subscripts.
\<close>

datatype ord = Z | P nat ord ord

subsection \<open>The subscript-first lexicographic order\<close>

fun olt :: "ord \<Rightarrow> ord \<Rightarrow> bool" (infix "<o" 50) where
  "olt Z Z = False"
| "olt Z (P _ _ _) = True"
| "olt (P _ _ _) Z = False"
| "olt (P a b c) (P e f g) =
     (a < e \<or> (a = e \<and> b <o f) \<or> (a = e \<and> b = f \<and> c <o g))"

abbreviation ole :: "ord \<Rightarrow> ord \<Rightarrow> bool" (infix "\<le>o" 50) where
  "x \<le>o y \<equiv> (x <o y \<or> x = y)"

text \<open>Leading subscript of a term (the subscript of its first principal term).\<close>

fun lead :: "ord \<Rightarrow> nat" where
  "lead Z = 0"
| "lead (P a _ _) = a"

text \<open>Subscript-first domination: a term whose leading subscript is below \<open>w\<close>
  (or which is \<open>Z\<close>) is strictly below \<^emph>\<open>any\<close> principal term \<open>p\<^bsub>w\<^esub>(b)+c\<close>.  This
  is the mechanism behind the bad-step decrease: the ascending copies all have
  leading subscript \<open>= row-1 of the bad root\<close>, which is strictly below the
  row-1 of the dropped last pair.\<close>

lemma olt_P_of_lead_lt: "t = Z \<or> lead t < w \<Longrightarrow> t <o P w b c"
  by (cases t) auto

lemma olt_irrefl: "\<not> x <o x"
  by (induction x) auto

lemma not_olt_Z: "\<not> x <o Z"
  by (cases x) auto

lemma olt_Z_iff: "x <o y \<Longrightarrow> y \<noteq> Z"
  using not_olt_Z by blast

lemma olt_trans: "x <o y \<Longrightarrow> y <o z \<Longrightarrow> x <o z"
proof (induction z arbitrary: x y)
  case Z
  then show ?case using not_olt_Z by blast
next
  case (P c1 c2 c3)
  show ?case
  proof (cases x)
    case Z
    then show ?thesis by (cases y) auto
  next
    case (P a1 a2 a3)
    note xP = this
    from xP \<open>x <o y\<close> obtain e1 e2 e3 where yP: "y = P e1 e2 e3" by (cases y) auto
    from \<open>x <o y\<close> xP yP
      have xy: "a1 < e1 \<or> (a1 = e1 \<and> a2 <o e2) \<or> (a1 = e1 \<and> a2 = e2 \<and> a3 <o e3)"
      by simp
    from \<open>y <o P c1 c2 c3\<close> yP
      have yz: "e1 < c1 \<or> (e1 = c1 \<and> e2 <o c2) \<or> (e1 = c1 \<and> e2 = c2 \<and> e3 <o c3)"
      by simp
    have "a1 < c1 \<or> (a1 = c1 \<and> a2 <o c2) \<or> (a1 = c1 \<and> a2 = c2 \<and> a3 <o c3)"
      using xy yz P.IH(1)[of a2 e2] P.IH(2)[of a3 e3] by (elim disjE) auto
    then show ?thesis using xP yP by simp
  qed
qed

lemma olt_total: "x <o y \<or> x = y \<or> y <o x"
proof (induction x arbitrary: y)
  case Z
  then show ?case by (cases y) auto
next
  case (P a1 a2 a3)
  show ?case
  proof (cases y)
    case Z
    then show ?thesis by simp
  next
    case (P e1 e2 e3)
    have "a1 < e1 \<or> a1 = e1 \<or> e1 < a1" by arith
    moreover have "a2 <o e2 \<or> a2 = e2 \<or> e2 <o a2" using P.IH(1) by blast
    moreover have "a3 <o e3 \<or> a3 = e3 \<or> e3 <o a3" using P.IH(2) by blast
    ultimately show ?thesis unfolding \<open>y = P e1 e2 e3\<close> by auto
  qed
qed

lemma ole_olt_trans: "x \<le>o y \<Longrightarrow> y <o z \<Longrightarrow> x <o z"
  using olt_trans by blast

lemma olt_ole_trans: "x <o y \<Longrightarrow> y \<le>o z \<Longrightarrow> x <o z"
  using olt_trans by blast

text \<open>Strict monotonicity of a principal term in its argument / its tail.\<close>

lemma olt_P_b: "b1 <o b2 \<Longrightarrow> P a b1 c1 <o P a b2 c2"
  by simp

lemma olt_P_c: "c1 <o c2 \<Longrightarrow> P a b c1 <o P a b c2"
  by simp


section \<open>The translation \<open>translate : pairseq \<Rightarrow> ord\<close>\<close>

text \<open>
  Read the pair sequence left to right as a forest by row 0 (the first
  component): the head pair \<open>(x,y)\<close> becomes a principal term \<open>p\<^bsub>y\<^esub>(\<dots>)\<close> whose
  argument is the translation of the maximal following block of pairs with
  row-0 value \<open>> x\<close> (its descendants), and whose tail is the translation of the
  remaining suffix (its siblings).  The subscript is the row-1 value \<open>y\<close>.
  This is the PrSS forest map \<open>omap\<close> with \<open>\<omega>\<^bsup>\<bullet>\<^esup>\<close> replaced by \<open>p\<^bsub>y\<^esub>(\<bullet>)\<close>.
\<close>

function translate :: "pairseq \<Rightarrow> ord" where
  "translate [] = Z"
| "translate (p # rest) =
     P (snd p) (translate (takeWhile (\<lambda>q. fst p < fst q) rest))
               (translate (dropWhile (\<lambda>q. fst p < fst q) rest))"
  by pat_completeness auto
termination
  by (relation "measure length")
     (auto simp: le_imp_less_Suc length_takeWhile_le
            intro: le_less_trans[OF length_dropWhile_le])

lemma lead_translate: "lead (translate M) = (case M of [] \<Rightarrow> 0 | p # _ \<Rightarrow> snd p)"
  by (cases M) auto

subsection \<open>Row-0 monotonicity of the parent relation\<close>

text \<open>Along a row-0 ancestry the row-0 value strictly / weakly increases.  This
  underlies the single-tree shape of the bad part (its root has the least
  row-0).\<close>

lemma nextrel0_entry0_less: "nextrel0 M j0 j1 \<Longrightarrow> entry M 0 j0 < entry M 0 j1"
  by (simp add: nextrel0_def)

lemma le0_entry0_mono:
  assumes "le0 M j0 j1" shows "entry M 0 j0 \<le> entry M 0 j1"
proof -
  from assms have "(nextrel0 M)\<^sup>*\<^sup>* j0 j1" by (simp add: le0_def)
  thus ?thesis
  proof (induction rule: rtranclp_induct)
    case base thus ?case by simp
  next
    case (step y z)
    from step.hyps(2) have "entry M 0 y < entry M 0 z" by (rule nextrel0_entry0_less)
    with step.IH show ?case by simp
  qed
qed

text \<open>Indices increase along the row-0 Next relation.\<close>

lemma nextrel0_index_less: "nextrel0 M a b \<Longrightarrow> a < b"
  by (simp add: nextrel0_def)

lemma nextrel0_rtrancl_index_le: "(nextrel0 M)\<^sup>*\<^sup>* a b \<Longrightarrow> a \<le> b"
  by (induction rule: rtranclp_induct) (auto dest: nextrel0_index_less)

text \<open>Key interval lemma: along a row-0 ancestry \<open>j\<^sub>0 \<le>\<^sub>M j\<^sub>1\<close>, \<^emph>\<open>every\<close> index in
  \<open>(j\<^sub>0, j\<^sub>1]\<close> (not only the chain points) has row-0 strictly above \<open>j\<^sub>0\<close>: the
  valleys between chain points are \<open>\<ge>\<close> the next chain point by \<open>nextrel0\<close>.  This
  makes the bad part a single tree rooted at \<open>j\<^sub>0\<close> (its least row-0).\<close>

lemma le0_interval_gt:
  assumes "(nextrel0 M)\<^sup>*\<^sup>* j0 j1"
  shows "\<forall>k. j0 < k \<and> k \<le> j1 \<longrightarrow> entry M 0 j0 < entry M 0 k"
  using assms
proof (induction rule: rtranclp_induct)
  case base
  show ?case by simp
next
  case (step y z)
  have yz: "entry M 0 y < entry M 0 z" using step.hyps(2) by (simp add: nextrel0_def)
  have j0y: "j0 \<le> y" using step.hyps(1) by (rule nextrel0_rtrancl_index_le)
  have j0le: "entry M 0 j0 \<le> entry M 0 y"
  proof (cases "j0 < y")
    case True
    hence "entry M 0 j0 < entry M 0 y" using step.IH by blast
    thus ?thesis by simp
  next
    case False
    with j0y have "j0 = y" by simp
    thus ?thesis by simp
  qed
  show ?case
  proof (intro allI impI, elim conjE)
    fix k assume k1: "j0 < k" and k2: "k \<le> z"
    show "entry M 0 j0 < entry M 0 k"
    proof (cases "k \<le> y")
      case True
      thus ?thesis using k1 step.IH by blast
    next
      case False
      hence yk: "y < k" by simp
      show ?thesis
      proof (cases "k = z")
        case True
        thus ?thesis using j0le yz by simp
      next
        case False
        with k2 yk have mid: "y < k \<and> k < z" by simp
        hence "entry M 0 z \<le> entry M 0 k"
          using step.hyps(2) by (simp add: nextrel0_def)
        thus ?thesis using j0le yz by simp
      qed
    qed
  qed
qed

text \<open>If every pair after the head lies strictly above it in row 0, the whole
  list reads as one tree: a single principal term with empty tail.\<close>

lemma translate_single_tree:
  assumes "\<forall>x\<in>set R. fst p < fst x"
  shows "translate (p # R) = P (snd p) (translate R) Z"
proof -
  have tw: "takeWhile (\<lambda>q. fst p < fst q) R = R"
    using assms by (simp add: takeWhile_eq_all_conv)
  have dw: "dropWhile (\<lambda>q. fst p < fst q) R = []"
    using assms by (simp add: dropWhile_eq_Nil_conv)
  show ?thesis by (simp only: translate.simps(2) tw dw translate.simps(1))
qed

subsection \<open>Context congruence (BADCTX)\<close>

text \<open>If two tails \<open>Z\<^sub>1, Z\<^sub>2\<close> share the same first pair's row-0 value and all
  their other pairs lie strictly above it (so each is a single tree once read),
  then a common good part \<open>G\<close> preserves a strict decrease between them.  This is
  the context-peeling step of the bad-branch decrease: by induction on \<open>G\<close>, each
  good pair either closes the comparison inside its own subtree or passes it on
  one level deeper, until \<open>G\<close> is consumed and the comparison is exactly the one
  on \<open>Z\<^sub>1, Z\<^sub>2\<close>.\<close>

lemma translate_ctx_cong:
  assumes base: "translate Z1 <o translate Z2"
    and ne1: "Z1 \<noteq> []" and ne2: "Z2 \<noteq> []"
    and root: "fst (hd Z1) = fst (hd Z2)"
    and r1: "\<forall>x\<in>set (tl Z1). fst (hd Z1) \<le> fst x"
    and r2: "\<forall>x\<in>set (tl Z2). fst (hd Z2) \<le> fst x"
  shows "translate (G @ Z1) <o translate (G @ Z2)"
proof (induction G rule: length_induct)
  case (1 G)
  show ?case
  proof (cases G)
    case Nil
    then show ?thesis using base by simp
  next
    case (Cons g G')
    let ?Pg = "\<lambda>q. fst g < fst q"
    \<comment> \<open>row-0 of the shared root\<close>
    have hd2: "fst (hd Z2) = fst (hd Z1)" using root by simp
    show ?thesis
    proof (cases "\<forall>x\<in>set G'. ?Pg x")
      case allG: True
      show ?thesis
      proof (cases "?Pg (hd Z1)")
        case True
        \<comment> \<open>case (b): the whole tail nests under \<open>g\<close>; pass to \<open>G'\<close>\<close>
        have aZ1: "\<forall>x\<in>set Z1. ?Pg x" using True r1 ne1 by (cases Z1) auto
        have aZ2: "\<forall>x\<in>set Z2. ?Pg x" using True hd2 r2 ne2 by (cases Z2) auto
        have all1: "\<forall>x\<in>set (G' @ Z1). ?Pg x" using allG aZ1 by auto
        have all2: "\<forall>x\<in>set (G' @ Z2). ?Pg x" using allG aZ2 by auto
        have tw1: "takeWhile ?Pg (G' @ Z1) = G' @ Z1"
          using all1 by (simp add: takeWhile_eq_all_conv)
        have dw1: "dropWhile ?Pg (G' @ Z1) = []"
          using all1 by (simp add: dropWhile_eq_Nil_conv)
        have tw2: "takeWhile ?Pg (G' @ Z2) = G' @ Z2"
          using all2 by (simp add: takeWhile_eq_all_conv)
        have dw2: "dropWhile ?Pg (G' @ Z2) = []"
          using all2 by (simp add: dropWhile_eq_Nil_conv)
        have e1: "translate (G @ Z1) = P (snd g) (translate (G' @ Z1)) Z"
          by (simp only: Cons append_Cons translate.simps(2) tw1 dw1 translate.simps(1))
        have e2: "translate (G @ Z2) = P (snd g) (translate (G' @ Z2)) Z"
          by (simp only: Cons append_Cons translate.simps(2) tw2 dw2 translate.simps(1))
        have "translate (G' @ Z1) <o translate (G' @ Z2)"
          using "1.IH" Cons by simp
        then show ?thesis using e1 e2 by (simp add: olt_P_b)
      next
        case False
        \<comment> \<open>case (c): the tail is a sibling after \<open>g\<close>'s subtree; use the base case\<close>
        have twZ1: "takeWhile ?Pg Z1 = []" using False ne1 by (cases Z1) auto
        have dwZ1: "dropWhile ?Pg Z1 = Z1" using False ne1 by (cases Z1) auto
        have twZ2: "takeWhile ?Pg Z2 = []" using False hd2 ne2 by (cases Z2) auto
        have dwZ2: "dropWhile ?Pg Z2 = Z2" using False hd2 ne2 by (cases Z2) auto
        have tw1: "takeWhile ?Pg (G' @ Z1) = G'"
          using allG twZ1 by (simp add: takeWhile_append2)
        have dw1: "dropWhile ?Pg (G' @ Z1) = Z1"
          using allG dwZ1 by (simp add: dropWhile_append2)
        have tw2: "takeWhile ?Pg (G' @ Z2) = G'"
          using allG twZ2 by (simp add: takeWhile_append2)
        have dw2: "dropWhile ?Pg (G' @ Z2) = Z2"
          using allG dwZ2 by (simp add: dropWhile_append2)
        have e1: "translate (G @ Z1) = P (snd g) (translate G') (translate Z1)"
          by (simp only: Cons append_Cons translate.simps(2) tw1 dw1)
        have e2: "translate (G @ Z2) = P (snd g) (translate G') (translate Z2)"
          by (simp only: Cons append_Cons translate.simps(2) tw2 dw2)
        show ?thesis using e1 e2 base by (simp add: olt_P_c)
      qed
    next
      case False
      \<comment> \<open>case (a): \<open>G'\<close> already drops to/below \<open>g\<close>; recurse on the shorter tail of \<open>G'\<close>\<close>
      then obtain x where x: "x \<in> set G'" and nx: "\<not> ?Pg x" by blast
      have tw1: "takeWhile ?Pg (G' @ Z1) = takeWhile ?Pg G'"
        using x nx by (simp add: takeWhile_append1)
      have dw1: "dropWhile ?Pg (G' @ Z1) = dropWhile ?Pg G' @ Z1"
        using x nx by (simp add: dropWhile_append1)
      have tw2: "takeWhile ?Pg (G' @ Z2) = takeWhile ?Pg G'"
        using x nx by (simp add: takeWhile_append1)
      have dw2: "dropWhile ?Pg (G' @ Z2) = dropWhile ?Pg G' @ Z2"
        using x nx by (simp add: dropWhile_append1)
      have e1: "translate (G @ Z1)
          = P (snd g) (translate (takeWhile ?Pg G')) (translate (dropWhile ?Pg G' @ Z1))"
        by (simp only: Cons append_Cons translate.simps(2) tw1 dw1)
      have e2: "translate (G @ Z2)
          = P (snd g) (translate (takeWhile ?Pg G')) (translate (dropWhile ?Pg G' @ Z2))"
        by (simp only: Cons append_Cons translate.simps(2) tw2 dw2)
      have "length (dropWhile ?Pg G') < length G"
        using Cons by (simp add: le_imp_less_Suc length_dropWhile_le)
      then have "translate (dropWhile ?Pg G' @ Z1) <o translate (dropWhile ?Pg G' @ Z2)"
        using "1.IH" by blast
      then show ?thesis using e1 e2 by (simp add: olt_P_c)
    qed
  qed
qed

subsection \<open>Sanity checks (the examples of the task description)\<close>

lemma "translate [(0,0)] = P 0 Z Z"
  by simp

text \<open>\<open>(0,0)(1,0) = p\<^sub>0(p\<^sub>0(0))\<close>\<close>
lemma "translate [(0,0),(1,0)] = P 0 (P 0 Z Z) Z"
  by simp

text \<open>\<open>(0,0)(1,1) = p\<^sub>0(p\<^sub>1(0))\<close>\<close>
lemma "translate [(0,0),(1,1)] = P 0 (P 1 Z Z) Z"
  by simp

text \<open>\<open>(0,0)(1,0)(1,0) = p\<^sub>0(p\<^sub>0(0)+p\<^sub>0(0))\<close>\<close>
lemma "translate [(0,0),(1,0),(1,0)] = P 0 (P 0 Z (P 0 Z Z)) Z"
  by simp

text \<open>\<open>(0,0)(1,1)(2,2)(3,3) = p\<^sub>0(p\<^sub>1(p\<^sub>2(p\<^sub>3(0))))\<close>\<close>
lemma "translate [(0,0),(1,1),(2,2),(3,3)] = P 0 (P 1 (P 2 (P 3 Z Z) Z) Z) Z"
  by simp


section \<open>Subscripts and their monotonicity under expansion\<close>

text \<open>The set of subscripts occurring in a notation term.\<close>

fun subs :: "ord \<Rightarrow> nat set" where
  "subs Z = {}"
| "subs (P a b c) = insert a (subs b \<union> subs c)"

text \<open>Every subscript of \<open>translate M\<close> is a row-1 value of \<open>M\<close>: the subscripts
  are exactly the \<open>y\<close>-components used, never invented.\<close>

lemma subs_translate: "subs (translate M) \<subseteq> snd ` set M"
proof (induction M rule: translate.induct)
  case 1
  show ?case by simp
next
  case (2 p rest)
  let ?tw = "takeWhile (\<lambda>q. fst p < fst q) rest"
  let ?dw = "dropWhile (\<lambda>q. fst p < fst q) rest"
  have tw: "set ?tw \<subseteq> set rest" by (auto dest: set_takeWhileD)
  have dw: "set ?dw \<subseteq> set rest" by (metis dropWhile_eq_drop set_drop_subset)
  have A: "subs (translate ?tw) \<subseteq> snd ` set rest"
    by (rule subset_trans[OF 2(1) image_mono[OF tw]])
  have B: "subs (translate ?dw) \<subseteq> snd ` set rest"
    by (rule subset_trans[OF 2(2) image_mono[OF dw]])
  from A B show ?case by auto
qed

text \<open>The row index \<open>i\<^sub>1\<close> is at most 1, so the row-1 increment \<open>\<delta>\<^sub>1\<close> is always 0.\<close>

lemma idx1_le1: "idx1 M j \<le> 1"
  by (simp add: idx1_def)

text \<open>One expansion step never introduces a new row-1 value: the bad part is
  copied with row 1 preserved (\<open>\<delta>\<^sub>1 = 0\<close>) and the last pair is dropped.  Hence
  the (finite) set of subscripts is non-increasing under expansion — the
  invariant behind the max-subscript stratification of well-foundedness.\<close>

lemma oper_snd_subset: "snd ` set (M[n]) \<subseteq> snd ` set M"
proof (cases "Lng M - 1 = 0")
  case True
  thus ?thesis by (simp add: oper_def)
next
  case L: False
  show ?thesis
  proof (cases "entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0")
    case True
    thus ?thesis using L by (auto simp: oper_def Let_def Pred_def dest!: in_set_butlastD)
  next
    case nz: False
    show ?thesis
    proof (cases "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)")
      case False
      thus ?thesis using L nz
        by (auto simp: oper_def Let_def Pred_def dest!: in_set_butlastD)
    next
      case hp: True
      let ?i1 = "idx1 M (Lng M - 1)"
      let ?j0 = "parent M ?i1 (Lng M - 1)"
      let ?d0 = "if 0 < ?i1 then entry M 0 (Lng M - 1) - entry M 0 ?j0 else (0::nat)"
      have d1z: "\<not> 1 < ?i1" using idx1_le1 by (simp add: not_less)
      have unfold: "M[n] = take ?j0 M
          @ concat (map (\<lambda>k. map (\<lambda>j. (entry M 0 j + k * ?d0, entry M 1 j))
                              [?j0..<Lng M - 1]) [0..<n])"
        using L nz hp d1z by (auto simp: oper_def Let_def)
      show ?thesis
      proof
        fix s assume "s \<in> snd ` set (M[n])"
        then obtain q where q: "q \<in> set (M[n])" and s: "s = snd q" by auto
        have "q \<in> set (take ?j0 M)
            \<or> q \<in> set (concat (map (\<lambda>k. map (\<lambda>j. (entry M 0 j + k * ?d0, entry M 1 j))
                                       [?j0..<Lng M - 1]) [0..<n]))"
          using q by (simp add: unfold)
        then show "s \<in> snd ` set M"
        proof
          assume "q \<in> set (take ?j0 M)"
          then have "q \<in> set M" using in_set_takeD by fast
          thus ?thesis using s by blast
        next
          assume "q \<in> set (concat (map (\<lambda>k. map (\<lambda>j. (entry M 0 j + k * ?d0, entry M 1 j))
                                       [?j0..<Lng M - 1]) [0..<n]))"
          then obtain j where j: "j \<in> {?j0..<Lng M - 1}" and qeq: "snd q = entry M 1 j"
            by auto
          from j have "j < Lng M" by auto
          then have "M ! j \<in> set M" by simp
          moreover have "snd q = snd (M ! j)" using qeq by (simp add: entry_def)
          ultimately show ?thesis using s by (auto simp: image_iff)
        qed
      qed
    qed
  qed
qed


text \<open>Consequently the subscripts of the translated expansion are bounded by
  the row-1 values already present in \<open>M\<close>: expansion never raises the maximum
  subscript.\<close>

lemma subs_translate_oper: "subs (translate (M[n])) \<subseteq> snd ` set M"
  using subs_translate[of "M[n]"] oper_snd_subset[of M n] by blast


section \<open>Appending a pair strictly increases the measure\<close>

text \<open>The analogue of PrSS \<open>omap_snoc_increase\<close>: extending a pair sequence on
  the right strictly increases its translation.  Hence dropping the last pair
  strictly decreases it, which covers the two \<open>Pred\<close> branches of \<open>M[n]\<close>.\<close>

lemma translate_snoc_increase: "translate C <o translate (C @ [m])"
proof (induction C rule: translate.induct)
  case 1
  show ?case by simp
next
  case (2 p rest)
  let ?P = "\<lambda>q. fst p < fst q"
  show ?case
  proof (cases "\<forall>x\<in>set rest. ?P x")
    case allp: True
    \<comment> \<open>the whole \<open>rest\<close> is below \<open>p\<close>: it is one block; the new pair extends it or starts a sibling\<close>
    have tw: "takeWhile ?P rest = rest" using allp by (simp add: takeWhile_eq_all_conv)
    have dw: "dropWhile ?P rest = []" using allp by (simp add: dropWhile_eq_Nil_conv)
    show ?thesis
    proof (cases "?P m")
      case True
      have tw': "takeWhile ?P (rest @ [m]) = rest @ [m]"
        using allp True by (simp add: takeWhile_eq_all_conv)
      have dw': "dropWhile ?P (rest @ [m]) = []"
        using allp True by (simp add: dropWhile_eq_Nil_conv)
      have key: "translate rest <o translate (rest @ [m])" using 2(1) tw by simp
      show ?thesis using key by (simp add: tw dw tw' dw')
    next
      case False
      have tw': "takeWhile ?P (rest @ [m]) = rest"
        using allp False by (simp add: takeWhile_append2)
      have dw': "dropWhile ?P (rest @ [m]) = [m]"
        using allp False by (simp add: dropWhile_append2)
      show ?thesis by (simp add: tw dw tw' dw')
    qed
  next
    case False
    then obtain x where x: "x \<in> set rest" and nP: "\<not> ?P x" by blast
    have tw': "takeWhile ?P (rest @ [m]) = takeWhile ?P rest"
      using x nP by (simp add: takeWhile_append1)
    have dw': "dropWhile ?P (rest @ [m]) = dropWhile ?P rest @ [m]"
      using x nP by (simp add: dropWhile_append1)
    have key: "translate (dropWhile ?P rest) <o translate (dropWhile ?P rest @ [m])"
      using 2(2) by simp
    show ?thesis using key by (simp add: tw' dw')
  qed
qed

lemma translate_butlast_decrease:
  "C \<noteq> [] \<Longrightarrow> translate (butlast C) <o translate C"
  using translate_snoc_increase[of "butlast C" "last C"]
  by (simp add: snoc_eq_iff_butlast)


subsection \<open>Abstract bad-step cores\<close>

text \<open>Core for \<open>i\<^sub>1 = 0\<close> (exact copies).  A tree rooted at \<open>(v\<^sub>0,w\<^sub>0)\<close> with body
  \<open>R\<close> (all above \<open>v\<^sub>0\<close>), followed by any block \<open>T\<close> that re-opens at or below \<open>v\<^sub>0\<close>
  (the next exact copy's root), is strictly below the same tree with the body
  extended by one more descendant \<open>lp\<close> (the dropped last pair).  The leading
  argument is \<open>R\<close> on the left but grows to \<open>R @ [lp]\<close> on the right; the number of
  trailing copies (in \<open>T\<close>) is irrelevant.\<close>

lemma core_i0:
  assumes R: "\<forall>x\<in>set R. v0 < fst x"
    and vl: "v0 < fst lp"
    and Thd: "T = [] \<or> \<not> v0 < fst (hd T)"
  shows "translate (((v0,w0) # R) @ T) <o translate (((v0,w0) # R) @ [lp])"
proof -
  let ?P = "\<lambda>q. v0 < fst q"
  have twT: "takeWhile ?P (R @ T) = R"
  proof (cases T)
    case Nil thus ?thesis using R by (simp add: takeWhile_eq_all_conv)
  next
    case (Cons t ts)
    with Thd have "\<not> ?P t" by simp
    hence "takeWhile ?P T = []" using Cons by simp
    thus ?thesis using R by (simp add: takeWhile_append2)
  qed
  have dwT: "dropWhile ?P (R @ T) = T"
  proof (cases T)
    case Nil thus ?thesis using R by (simp add: dropWhile_eq_Nil_conv)
  next
    case (Cons t ts)
    with Thd have "\<not> ?P t" by simp
    hence "dropWhile ?P T = T" using Cons by simp
    thus ?thesis using R by (simp add: dropWhile_append2)
  qed
  have lhs: "translate (((v0,w0) # R) @ T) = P w0 (translate R) (translate T)"
    by (simp only: append_Cons fst_conv snd_conv translate.simps(2) twT dwT)
  have rhs: "translate (((v0,w0) # R) @ [lp]) = P w0 (translate (R @ [lp])) Z"
  proof -
    have all: "\<forall>x\<in>set (R @ [lp]). fst (v0,w0) < fst x" using R vl by auto
    have "translate ((v0,w0) # (R @ [lp])) = P (snd (v0,w0)) (translate (R @ [lp])) Z"
      by (rule translate_single_tree[OF all])
    thus ?thesis by simp
  qed
  have "translate R <o translate (R @ [lp])" by (rule translate_snoc_increase)
  thus ?thesis using lhs rhs by (simp add: olt_P_b)
qed

text \<open>Core for \<open>i\<^sub>1 = 1\<close> (ascending copies).  The copy-rest \<open>C\<close> is itself a
  single tree rooted at the same row-0 as the dropped last pair \<open>lp\<close> but with a
  strictly smaller subscript; so \<open>C \<prec> [lp]\<close> by subscript-first domination, and
  the common bodies \<open>(v\<^sub>0,w\<^sub>0) # R\<close> / \<open>R\<close> propagate it via BADCTX.\<close>

lemma core_i1:
  assumes R: "\<forall>x\<in>set R. v0 < fst x"
    and CP: "C \<noteq> []"
    and Cmin: "\<forall>x\<in>set (tl C). fst (hd C) < fst x"
    and Croot: "fst (hd C) = fst lp"
    and lpv: "v0 < fst lp"
    and lead_lt: "snd (hd C) < snd lp"
  shows "translate (((v0,w0) # R) @ C) <o translate (((v0,w0) # R) @ [lp])"
proof -
  \<comment> \<open>\<open>C\<close> is a single tree; its translation is dominated by \<open>p\<^bsub>snd lp\<^esub>(0)\<close>\<close>
  have allC: "\<forall>x\<in>set C. v0 < fst x"
  proof
    fix x assume "x \<in> set C"
    then consider "x = hd C" | "x \<in> set (tl C)" using CP by (cases C) auto
    thus "v0 < fst x"
    proof cases
      case 1 thus ?thesis using Croot lpv by simp
    next
      case 2 thus ?thesis using Cmin Croot lpv by fastforce
    qed
  qed
  have tC: "translate C = P (snd (hd C)) (translate (tl C)) Z"
    using translate_single_tree[OF Cmin] CP by simp
  have "translate C <o translate [lp]"
  proof -
    have "translate C <o P (snd lp) Z Z"
      using tC lead_lt by (simp add: olt_P_of_lead_lt)
    thus ?thesis by simp
  qed
  \<comment> \<open>propagate through the common body \<open>R\<close>, then through the root \<open>(v\<^sub>0,w\<^sub>0)\<close>\<close>
  have inner: "translate (R @ C) <o translate (R @ [lp])"
  proof (rule translate_ctx_cong)
    show "translate C <o translate [lp]" by fact
    show "C \<noteq> []" by fact
    show "[lp] \<noteq> []" by simp
    show "fst (hd C) = fst (hd [lp])" using Croot by simp
    show "\<forall>x\<in>set (tl C). fst (hd C) \<le> fst x" using Cmin by auto
    show "\<forall>x\<in>set (tl [lp]). fst (hd [lp]) \<le> fst x" by simp
  qed
  have allRC: "\<forall>x\<in>set (R @ C). fst (v0,w0) < fst x" using R allC by auto
  have allRlp: "\<forall>x\<in>set (R @ [lp]). fst (v0,w0) < fst x" using R lpv by auto
  have lhs: "translate (((v0,w0) # R) @ C) = P w0 (translate (R @ C)) Z"
    using translate_single_tree[OF allRC] by simp
  have rhs: "translate (((v0,w0) # R) @ [lp]) = P w0 (translate (R @ [lp])) Z"
    using translate_single_tree[OF allRlp] by simp
  show ?thesis using inner lhs rhs by (simp add: olt_P_b)
qed


section \<open>The expansion step strictly decreases the measure: \<open>Pred\<close> branches\<close>

text \<open>In the two degenerate branches of \<open>M[n]\<close> (last pair \<open>(0,0)\<close>, or no unique
  parent in row \<open>i\<^sub>1\<close>) the step drops the last pair, so the measure decreases
  by @{thm translate_butlast_decrease}.  The remaining (bad) branch is the
  genuine core, handled separately.\<close>

lemma translate_oper_pred:
  assumes L: "1 < Lng M"
    and br: "(entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)
             \<or> \<not> hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
  shows "translate (M[n]) <o translate M"
proof -
  from L have j1: "Lng M - 1 \<noteq> 0" by simp
  have "M[n] = Pred M"
    using br
  proof
    assume "entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0"
    thus ?thesis using j1 by (simp add: oper_def Let_def)
  next
    assume "\<not> hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    thus ?thesis using j1 by (auto simp: oper_def Let_def)
  qed
  moreover have "Pred M = butlast M" using L by (simp add: Pred_def)
  moreover have "M \<noteq> []" using L by auto
  ultimately show ?thesis using translate_butlast_decrease by simp
qed

end
