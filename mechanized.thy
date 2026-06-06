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

end
