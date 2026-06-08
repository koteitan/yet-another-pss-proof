theory mechanized
  imports def
begin

section \<open>The ternary-tree notation \<open>p_a(b)+c\<close>\<close>

text \<open>
  The type \<open>three\<close> is a tree whose nodes carry one natural number and two
  subtrees; it is named after that structure, not after any order (linearity of
  \<open><o\<close> is proved below, not presupposed).  \<open>P a b c\<close> denotes \<open>p\<^bsub>a\<^esub>(b) + c\<close>:
  a principal term \<open>p\<^bsub>a\<^esub>(b)\<close> with natural-number subscript \<open>a\<close> (the row-1 value of
  a pair) and argument \<open>b\<close> (the sub-forest), followed by the rest of the sum \<open>c\<close>.
  \<^term>\<open>Z\<close> denotes \<open>0\<close>.  This generalises the PrSS notation \<open>E a b = \<omega>\<^bsup>a\<^esup> + b\<close>:
  the single exponent \<open>\<omega>\<^bsup>a\<^esup>\<close> is replaced by the subscripted \<open>p\<^bsub>a\<^esub>(b)\<close>.

  The order \<open><o\<close> is the lexicographic order on principal terms with the
  subscript taken first (subscript-first).  Under this direction the expansion
  step strictly decreases the translate (see \<open>m_step_decreases\<close> below).
\<close>

datatype three = Z | P nat three three

subsection \<open>The subscript-first lexicographic order\<close>

fun olt :: "three \<Rightarrow> three \<Rightarrow> bool" (infix "<o" 50) where
  "olt Z Z = False"
| "olt Z (P _ _ _) = True"
| "olt (P _ _ _) Z = False"
| "olt (P a b c) (P e f g) =
     (a < e \<or> (a = e \<and> b <o f) \<or> (a = e \<and> b = f \<and> c <o g))"

abbreviation ole :: "three \<Rightarrow> three \<Rightarrow> bool" (infix "\<le>o" 50) where
  "x \<le>o y \<equiv> (x <o y \<or> x = y)"

text \<open>Leading subscript of a term (the subscript of its first principal term).\<close>

fun lead :: "three \<Rightarrow> nat" where
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


section \<open>The translation \<open>translate : pairseq \<Rightarrow> three\<close>\<close>

text \<open>
  Read the pair sequence left to right as a forest by row 0 (the first
  component): the head pair \<open>(x,y)\<close> becomes a principal term \<open>p\<^bsub>y\<^esub>(\<dots>)\<close> whose
  argument is the translation of the maximal following block of pairs with
  row-0 value \<open>> x\<close> (its descendants), and whose tail is the translation of the
  remaining suffix (its siblings).  The subscript is the row-1 value \<open>y\<close>.
  This is the PrSS forest map \<open>omap\<close> with \<open>\<omega>\<^bsup>\<bullet>\<^esup>\<close> replaced by \<open>p\<^bsub>y\<^esub>(\<bullet>)\<close>.
\<close>

function translate :: "pairseq \<Rightarrow> three" where
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

text \<open>A block \<open>(v\<^sub>0,w\<^sub>0) # R\<close> (root \<open>v\<^sub>0\<close>, body \<open>R\<close> all above \<open>v\<^sub>0\<close>) followed by a tail
  \<open>T\<close> that re-opens at or below \<open>v\<^sub>0\<close> translates to a single principal whose argument
  is \<open>R\<close> and whose siblings are \<open>T\<close>.  (This is the block shape used by the bad-step
  cores; exposed here for the CNF preservation proof.)\<close>

lemma translate_block_append:
  assumes R: "\<forall>x\<in>set R. v0 < fst x" and T: "T = [] \<or> \<not> v0 < fst (hd T)"
  shows "translate (((v0,w0) # R) @ T) = P w0 (translate R) (translate T)"
proof -
  let ?P = "\<lambda>q. v0 < fst q"
  have twT: "takeWhile ?P (R @ T) = R"
  proof (cases T)
    case Nil thus ?thesis using R by (simp add: takeWhile_eq_all_conv)
  next
    case (Cons t ts)
    with T have "\<not> ?P t" by simp
    hence "takeWhile ?P T = []" using Cons by simp
    thus ?thesis using R by (simp add: takeWhile_append2)
  qed
  have dwT: "dropWhile ?P (R @ T) = T"
  proof (cases T)
    case Nil thus ?thesis using R by (simp add: dropWhile_eq_Nil_conv)
  next
    case (Cons t ts)
    with T have "\<not> ?P t" by simp
    hence "dropWhile ?P T = T" using Cons by simp
    thus ?thesis using R by (simp add: dropWhile_append2)
  qed
  show ?thesis by (simp only: append_Cons fst_conv snd_conv translate.simps(2) twT dwT)
qed

text \<open>Shifting every row-0 value by a constant preserves the translation: \<open>translate\<close>
  only reads row-0 through the strict comparisons \<open>fst p < fst q\<close> (shift-invariant)
  and reads row-1 (\<open>snd\<close>) unchanged.  This is why the ascending copies of the
  bad-step tiling (which differ from the base block only by a uniform row-0 shift)
  all translate to the same tree.\<close>

lemma translate_shift: "translate (map (\<lambda>p. (fst p + d, snd p)) M) = translate M"
proof (induction M rule: translate.induct)
  case 1 thus ?case by simp
next
  case (2 p rest)
  let ?f = "\<lambda>p. (fst p + d, snd p)"
  let ?P = "\<lambda>q. fst p < fst q"
  have tw: "takeWhile (\<lambda>q. fst (?f p) < fst q) (map ?f rest) = map ?f (takeWhile ?P rest)"
    by (simp add: takeWhile_map o_def)
  have dw: "dropWhile (\<lambda>q. fst (?f p) < fst q) (map ?f rest) = map ?f (dropWhile ?P rest)"
    by (simp add: dropWhile_map o_def)
  have "translate (map ?f (p # rest))
        = P (snd p) (translate (map ?f (takeWhile ?P rest))) (translate (map ?f (dropWhile ?P rest)))"
    using tw dw by (simp only: list.map translate.simps(2) fst_conv snd_conv)
  also have "\<dots> = P (snd p) (translate (takeWhile ?P rest)) (translate (dropWhile ?P rest))"
    using "2.IH"(1) "2.IH"(2) by simp
  also have "\<dots> = translate (p # rest)" by simp
  finally show ?case .
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

text \<open>A suffix as an index map (helper for the bad-step list bookkeeping).\<close>

lemma drop_eq_map_nth: "drop a xs = map (\<lambda>i. xs ! i) [a..<length xs]"
proof (rule nth_equalityI)
  show "length (drop a xs) = length (map (\<lambda>i. xs ! i) [a..<length xs])" by simp
next
  fix i assume "i < length (drop a xs)"
  thus "drop a xs ! i = map (\<lambda>i. xs ! i) [a..<length xs] ! i"
    by (auto simp: nth_drop)
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

fun subs :: "three \<Rightarrow> nat set" where
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

text \<open>The bad branch of \<open>M[n]\<close>, unfolded (\<open>\<delta>\<^sub>1 = 0\<close> since \<open>idx1 \<le> 1\<close>).\<close>

lemma oper_bad_unfold:
  assumes "Lng M - 1 \<noteq> 0"
    and "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
  shows "M[n] =
    take (parent M (idx1 M (Lng M - 1)) (Lng M - 1)) M
    @ concat (map (\<lambda>k. map (\<lambda>j.
          (entry M 0 j + k * (if 0 < idx1 M (Lng M - 1)
              then entry M 0 (Lng M - 1)
                   - entry M 0 (parent M (idx1 M (Lng M - 1)) (Lng M - 1))
              else 0),
           entry M 1 j))
        [parent M (idx1 M (Lng M - 1)) (Lng M - 1)..<Lng M - 1]) [0..<n])"
proof -
  have d1z: "\<not> 1 < idx1 M (Lng M - 1)" using idx1_le1 by (simp add: not_less)
  show ?thesis using assms d1z by (auto simp: oper_def Let_def)
qed

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

text \<open>Appending a pair can only \<^emph>\<open>increase\<close> (weakly) the translation of a leading
  same-level block \<open>takeWhile (\<lambda>x. a < fst x)\<close>: either the block is unchanged (some
  earlier pair already stopped it) or it is extended by the new pair (then
  @{thm [source] translate_snoc_increase} applies).  Used for the sibling-condition
  transfer in \<open>cnf_snoc\<close>.\<close>

lemma translate_takeWhile_snoc_le:
  "translate (takeWhile (\<lambda>x. a < fst x) C) \<le>o translate (takeWhile (\<lambda>x. a < fst x) (C @ [m]))"
proof (cases "\<forall>x\<in>set C. a < fst x")
  case True
  hence twC: "takeWhile (\<lambda>x. a < fst x) C = C" by (simp add: takeWhile_eq_all_conv)
  show ?thesis
  proof (cases "a < fst m")
    case mt: True
    have e: "takeWhile (\<lambda>x. a < fst x) (C @ [m]) = C @ [m]"
      using True mt by (simp add: takeWhile_eq_all_conv)
    have "translate (takeWhile (\<lambda>x. a < fst x) C) <o translate (C @ [m])"
      unfolding twC by (rule translate_snoc_increase)
    thus ?thesis using e by auto
  next
    case nm: False
    have eq: "takeWhile (\<lambda>x. a < fst x) (C @ [m]) = C"
      using True nm by (simp add: takeWhile_append2)
    show ?thesis by (simp add: eq twC)
  qed
next
  case False
  then obtain x where "x \<in> set C" "\<not> a < fst x" by blast
  hence "takeWhile (\<lambda>x. a < fst x) (C @ [m]) = takeWhile (\<lambda>x. a < fst x) C"
    by (simp add: takeWhile_append1)
  thus ?thesis by simp
qed


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
    and Cge: "\<forall>x\<in>set (tl C). fst (hd C) \<le> fst x"
    and Croot: "fst (hd C) = fst lp"
    and lpv: "v0 < fst lp"
    and lead_lt: "snd (hd C) < snd lp"
  shows "translate (((v0,w0) # R) @ C) <o translate (((v0,w0) # R) @ [lp])"
proof -
  have allC: "\<forall>x\<in>set C. v0 < fst x"
  proof
    fix x assume "x \<in> set C"
    then consider "x = hd C" | "x \<in> set (tl C)" using CP by (cases C) auto
    thus "v0 < fst x"
    proof cases
      case 1 thus ?thesis using Croot lpv by simp
    next
      case 2 thus ?thesis using Cge Croot lpv by fastforce
    qed
  qed
  \<comment> \<open>subscript-first domination: \<open>C\<close> leads with subscript \<open>snd (hd C) < snd lp\<close>\<close>
  have leadC: "lead (translate C) = snd (hd C)"
    using CP by (cases C) (auto simp: lead_translate)
  have "translate C <o translate [lp]"
  proof -
    have "translate C = Z \<or> lead (translate C) < snd lp" using leadC lead_lt by simp
    hence "translate C <o P (snd lp) Z Z" by (rule olt_P_of_lead_lt)
    thus ?thesis by simp
  qed
  \<comment> \<open>propagate through the common body \<open>R\<close>, then through the root \<open>(v\<^sub>0,w\<^sub>0)\<close>\<close>
  have inner: "translate (R @ C) <o translate (R @ [lp])"
  proof (rule translate_ctx_cong)
    show "translate C <o translate [lp]" by fact
    show "C \<noteq> []" by fact
    show "[lp] \<noteq> []" by simp
    show "fst (hd C) = fst (hd [lp])" using Croot by simp
    show "\<forall>x\<in>set (tl C). fst (hd C) \<le> fst x" by fact
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


subsection \<open>The expansion step strictly decreases the measure: bad branch\<close>

text \<open>The genuine case: the bad part \<open>B\<close> is copied (with row-0 ascension when
  \<open>i\<^sub>1 = 1\<close>) and the last pair dropped.  Decompose \<open>M = G \<oplus> B \<oplus> [lp]\<close> and
  \<open>M[n] = G \<oplus> (B \<oplus> C)\<close>; the abstract cores give \<open>B \<oplus> C \<prec> B \<oplus> [lp]\<close> and BADCTX
  lifts it through \<open>G\<close>.\<close>

lemma translate_oper_bad:
  assumes L: "1 < Lng M"
    and nz: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and n: "1 \<le> n"
  shows "translate (M[n]) <o translate M"
proof -
  let ?j1 = "Lng M - 1"
  let ?i1 = "idx1 M ?j1"
  let ?j0 = "parent M ?i1 ?j1"
  let ?d0 = "if 0 < ?i1 then entry M 0 ?j1 - entry M 0 ?j0 else (0::nat)"
  let ?sh = "\<lambda>k j. (entry M 0 j + k * ?d0, entry M 1 j)"
  let ?B = "map (?sh 0) [?j0..<?j1]"
  let ?R = "map (?sh 0) [Suc ?j0..<?j1]"
  let ?C = "concat (map (\<lambda>k. map (?sh k) [?j0..<?j1]) [1..<n])"
  let ?cps = "concat (map (\<lambda>k. map (?sh k) [?j0..<?j1]) [0..<n])"
  let ?lp = "M ! ?j1"
  let ?v0 = "entry M 0 ?j0"
  let ?w0 = "entry M 1 ?j0"
  \<comment> \<open>parent facts\<close>
  have ex1: "\<exists>!j0. nextR M ?i1 j0 ?j1" using hp by (simp add: hasParent_def)
  have np: "nextR M ?i1 ?j0 ?j1" using theI'[OF ex1] by (simp add: parent_def)
  have j0lt: "?j0 < ?j1"
    using np by (auto simp: nextR_def nextrel0_def nextrel1_def split: if_splits)
  have chain: "(nextrel0 M)\<^sup>*\<^sup>* ?j0 ?j1"
  proof (cases "?i1 = 0")
    case True with np have "nextrel0 M ?j0 ?j1" by (simp add: nextR_def)
    thus ?thesis by (rule r_into_rtranclp)
  next
    case False with np have "nextrel1 M ?j0 ?j1" by (simp add: nextR_def)
    thus ?thesis by (simp add: nextrel1_def le0_def)
  qed
  have iv: "\<And>k. ?j0 < k \<Longrightarrow> k \<le> ?j1 \<Longrightarrow> ?v0 < entry M 0 k"
    using le0_interval_gt[OF chain] by blast
  have LngM: "Lng M = Suc ?j1" using L by simp
  \<comment> \<open>structure\<close>
  have B_eq: "?B = (?v0, ?w0) # ?R"
  proof -
    have "[?j0..<?j1] = ?j0 # [Suc ?j0..<?j1]" using j0lt by (simp add: upt_conv_Cons)
    thus ?thesis by simp
  qed
  have R_gt: "\<forall>x\<in>set ?R. ?v0 < fst x"
  proof
    fix x assume "x \<in> set ?R"
    then obtain j where j: "j \<in> set [Suc ?j0..<?j1]" and xeq: "x = ?sh 0 j" by auto
    from j have "?j0 < j" "j \<le> ?j1" by auto
    hence "?v0 < entry M 0 j" by (rule iv)
    thus "?v0 < fst x" using xeq by simp
  qed
  have lp_gt: "?v0 < fst ?lp"
  proof -
    have "?v0 < entry M 0 ?j1" using iv j0lt by simp
    thus ?thesis by (simp add: entry_def)
  qed
  have cps_eq: "?cps = ?B @ ?C"
  proof -
    have "[0..<n] = 0 # [1..<n]" using n by (simp add: upt_conv_Cons)
    thus ?thesis by simp
  qed
  have dropM: "drop ?j0 M = ?B @ [?lp]"
  proof -
    have "drop ?j0 M = map (\<lambda>i. M ! i) [?j0..<Lng M]" by (rule drop_eq_map_nth)
    also have "[?j0..<Lng M] = [?j0..<?j1] @ [?j1]"
    proof -
      have le: "?j0 \<le> ?j1" using j0lt by simp
      show ?thesis by (metis le upt_Suc_append LngM)
    qed
    also have "map (\<lambda>i. M ! i) ([?j0..<?j1] @ [?j1])
                 = map (\<lambda>i. M ! i) [?j0..<?j1] @ [?lp]" by simp
    also have "map (\<lambda>i. M ! i) [?j0..<?j1] = ?B"
      by (simp add: entry_def cong: map_cong)
    finally show ?thesis .
  qed
  have Mn: "M[n] = take ?j0 M @ ?cps"
    by (rule oper_bad_unfold) (use L nz hp in auto)
  \<comment> \<open>shape of the bad part and copies\<close>
  have Bne: "?B \<noteq> []" using j0lt by simp
  have hdB: "hd ?B = (?v0, ?w0)" by (simp only: B_eq list.sel(1))
  have tlB: "tl ?B = ?R" by (simp only: B_eq list.sel(3))
  have R_ge: "\<forall>x\<in>set ?R. ?v0 \<le> fst x" using R_gt by (auto intro: order_less_imp_le)
  have allC_v0: "\<forall>x\<in>set ?C. ?v0 \<le> fst x"
  proof
    fix x assume "x \<in> set ?C"
    then obtain k j where k: "k \<in> set [1..<n]" and j: "j \<in> set [?j0..<?j1]"
      and xeq: "x = ?sh k j" by (auto simp: set_concat)
    from j have "?j0 \<le> j" "j < ?j1" by auto
    hence "?v0 \<le> entry M 0 j" using iv[of j] by (cases "?j0 < j") auto
    also have "entry M 0 j \<le> fst x" using xeq by simp
    finally show "?v0 \<le> fst x" .
  qed
  \<comment> \<open>core: \<open>B \<oplus> C \<prec> B \<oplus> [lp]\<close>\<close>
  have core: "translate (?B @ ?C) <o translate (?B @ [?lp])"
  proof (cases "?i1 = 1 \<and> 2 \<le> n")
    case True
    hence i1: "?i1 = 1" and n2: "2 \<le> n" by auto
    have nl1: "nextrel1 M ?j0 ?j1" using np i1 by (simp add: nextR_def)
    have d0pos: "?d0 = entry M 0 ?j1 - ?v0" using i1 by simp
    have hdC: "hd ?C = ?sh 1 ?j0"
    proof -
      have u: "[1..<n] = 1 # [Suc 1..<n]" using n2 by (simp add: upt_conv_Cons)
      have ne: "map (?sh 1) [?j0..<?j1] \<noteq> []" using j0lt by simp
      have "?C = map (?sh 1) [?j0..<?j1] @ concat (map (\<lambda>k. map (?sh k) [?j0..<?j1]) [Suc 1..<n])"
        by (subst u) simp
      hence "hd ?C = hd (map (?sh 1) [?j0..<?j1])" using ne by (simp add: hd_append)
      also have "\<dots> = ?sh 1 ?j0" using j0lt by (simp add: upt_conv_Cons)
      finally show ?thesis .
    qed
    have CP: "?C \<noteq> []"
    proof -
      have "1 \<in> set [1..<n]" using n2 by simp
      moreover have "map (?sh 1) [?j0..<?j1] \<noteq> []" using j0lt by simp
      ultimately show ?thesis by (auto simp: set_concat)
    qed
    have fstv: "entry M 0 ?j1 = ?v0 + ?d0"
    proof -
      have "?v0 \<le> entry M 0 ?j1" using lp_gt by (simp add: entry_def)
      thus ?thesis using d0pos by simp
    qed
    have hdfst: "fst (hd ?C) = fst ?lp"
      using hdC fstv by (simp add: entry_def)
    have hdsnd: "snd (hd ?C) < snd ?lp"
    proof -
      have "entry M 1 ?j0 < entry M 1 ?j1" using nl1 by (simp add: nextrel1_def)
      thus ?thesis using hdC by (simp add: entry_def)
    qed
    have allC_ge: "\<forall>x\<in>set ?C. fst (hd ?C) \<le> fst x"
    proof
      fix x assume "x \<in> set ?C"
      then obtain k j where k: "k \<in> set [1..<n]" and j: "j \<in> set [?j0..<?j1]"
        and xeq: "x = ?sh k j" by (auto simp: set_concat)
      from k have k1: "1 \<le> k" by auto
      from j have "?j0 \<le> j" "j < ?j1" by auto
      hence vj: "?v0 \<le> entry M 0 j" using iv[of j] by (cases "?j0 < j") auto
      have dk: "?d0 \<le> k * ?d0" using mult_le_mono1[OF k1, of ?d0] by simp
      have "fst (hd ?C) = ?v0 + ?d0" using hdC by simp
      also have "\<dots> \<le> entry M 0 j + k * ?d0" using vj dk by (simp add: add_mono)
      also have "\<dots> = fst x" using xeq by simp
      finally show "fst (hd ?C) \<le> fst x" .
    qed
    have Cge: "\<forall>x\<in>set (tl ?C). fst (hd ?C) \<le> fst x"
    proof
      fix x assume "x \<in> set (tl ?C)"
      hence "x \<in> set ?C" using CP by (cases ?C) auto
      thus "fst (hd ?C) \<le> fst x" using allC_ge by blast
    qed
    show ?thesis
      unfolding B_eq
      by (rule core_i1[OF R_gt CP Cge hdfst lp_gt hdsnd])
  next
    case False
    have Thd: "?C = [] \<or> \<not> ?v0 < fst (hd ?C)"
    proof (cases "n = 1")
      case True
      hence "?C = []" by simp
      thus ?thesis ..
    next
      case False
      with n have n2: "2 \<le> n" by simp
      from \<open>\<not> (?i1 = 1 \<and> 2 \<le> n)\<close> n2 have "?i1 \<noteq> 1" by simp
      with idx1_le1[of M ?j1] have i0: "?i1 = 0" by simp
      hence d00: "?d0 = 0" by simp
      have u: "[1..<n] = 1 # [Suc 1..<n]" using n2 by (simp add: upt_conv_Cons)
      have ne: "map (?sh 1) [?j0..<?j1] \<noteq> []" using j0lt by simp
      have "?C = map (?sh 1) [?j0..<?j1] @ concat (map (\<lambda>k. map (?sh k) [?j0..<?j1]) [Suc 1..<n])"
        by (subst u) simp
      hence "hd ?C = ?sh 1 ?j0" using ne j0lt by (simp add: hd_append upt_conv_Cons)
      hence "fst (hd ?C) = ?v0" using d00 by simp
      thus ?thesis by simp
    qed
    show ?thesis
      unfolding B_eq
      by (rule core_i0[OF R_gt lp_gt Thd])
  qed
  \<comment> \<open>lift through the good part \<open>G = take ?j0 M\<close> by BADCTX\<close>
  have bc: "translate (take ?j0 M @ (?B @ ?C)) <o translate (take ?j0 M @ (?B @ [?lp]))"
  proof (rule translate_ctx_cong)
    show "translate (?B @ ?C) <o translate (?B @ [?lp])" by (rule core)
    show "?B @ ?C \<noteq> []" using Bne by simp
    show "?B @ [?lp] \<noteq> []" by simp
    show "fst (hd (?B @ ?C)) = fst (hd (?B @ [?lp]))"
      using Bne hdB by (simp add: hd_append)
    show "\<forall>x\<in>set (tl (?B @ ?C)). fst (hd (?B @ ?C)) \<le> fst x"
    proof -
      have e: "fst (hd (?B @ ?C)) = ?v0" using Bne hdB by (simp add: hd_append)
      have t: "tl (?B @ ?C) = ?R @ ?C" using Bne tlB by (simp add: tl_append2)
      have "\<forall>x\<in>set (?R @ ?C). ?v0 \<le> fst x"
      proof
        fix x assume "x \<in> set (?R @ ?C)"
        then consider "x \<in> set ?R" | "x \<in> set ?C" by auto
        thus "?v0 \<le> fst x"
          by cases (use R_ge allC_v0 in blast)+
      qed
      thus ?thesis using e t by simp
    qed
    show "\<forall>x\<in>set (tl (?B @ [?lp])). fst (hd (?B @ [?lp])) \<le> fst x"
    proof -
      have e: "fst (hd (?B @ [?lp])) = ?v0" using Bne hdB by (simp add: hd_append)
      have t: "tl (?B @ [?lp]) = ?R @ [?lp]" using Bne tlB by (simp add: tl_append2)
      have "?v0 \<le> fst ?lp" using lp_gt by simp
      hence "\<forall>x\<in>set (?R @ [?lp]). ?v0 \<le> fst x" using R_ge by auto
      thus ?thesis using e t by simp
    qed
  qed
  have listeq: "take ?j0 M @ (?B @ [?lp]) = M"
    using dropM by (metis append_take_drop_id)
  have e1: "translate (M[n]) = translate (take ?j0 M @ (?B @ ?C))"
    using Mn cps_eq by simp
  have e2: "translate (take ?j0 M @ (?B @ [?lp])) = translate M"
    using listeq by simp
  from bc e1 e2 show ?thesis by simp
qed


subsection \<open>The decrease lemma\<close>

text \<open>Every expansion step on a sequence of length \<open>> 1\<close> strictly decreases the
  measure, regardless of the copy count \<open>n \<ge> 1\<close> (and regardless of standardness).\<close>

theorem m_step_decreases:
  assumes "1 < Lng M" and "1 \<le> n"
  shows "translate (M[n]) <o translate M"
proof (cases "entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0")
  case True
  thus ?thesis using assms(1) translate_oper_pred by blast
next
  case nz: False
  show ?thesis
  proof (cases "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)")
    case False
    thus ?thesis using assms(1) translate_oper_pred by blast
  next
    case True
    thus ?thesis using assms nz translate_oper_bad by blast
  qed
qed

end
