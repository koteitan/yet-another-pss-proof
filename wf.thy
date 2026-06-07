theory wf
  imports proofs
begin

text \<open>
  Towards \<open>diagacc\<close> (well-foundedness of \<open><o\<close> on \<open>NF\<close>).  This file develops the
  \<^emph>\<open>syntactic\<close> core of the subscript-monotonicity of descent: along the leftmost
  argument spine of a term, the subscript-first order \<open><o\<close> refines the
  lexicographic order on the spine; together with the normal-form invariants of
  \<open>NF\<close> (the spine begins \<open>0,1,\<dots>,maxsub\<close>; every subscript is \<le> the spine
  maximum) this yields \<open>w <o x \<Longrightarrow> maxsub w \<le> maxsub x\<close>.

  Here we prove the order-theoretic part unconditionally (\<open>olt_imp_slex\<close>,
  \<open>climb_mono\<close>, \<open>maxsub_mono_cond\<close>), taking the two NF-invariants as hypotheses.
  Establishing those invariants for \<open>NF = translate ` ST_PS\<close> (by induction on the
  generation of \<open>ST_PS\<close>) is the next stage; see \<open>memo.md\<close>.
\<close>

subsection \<open>Leftmost spine, its maximum, and the maximal subscript\<close>

fun spine :: "three \<Rightarrow> nat list" where
  "spine Z = []"
| "spine (P a b c) = a # spine b"

definition cmax :: "nat list \<Rightarrow> nat" where
  "cmax xs = foldr max xs 0"

abbreviation climb :: "three \<Rightarrow> nat" where
  "climb t \<equiv> cmax (spine t)"

fun maxsub :: "three \<Rightarrow> nat" where
  "maxsub Z = 0"
| "maxsub (P a b c) = max a (max (maxsub b) (maxsub c))"

lemma cmax_Nil [simp]: "cmax [] = 0" by (simp add: cmax_def)
lemma cmax_Cons [simp]: "cmax (x # xs) = max x (cmax xs)" by (simp add: cmax_def)

lemma cmax_ge: "z \<in> set xs \<Longrightarrow> z \<le> cmax xs"
  by (induction xs) auto

subsection \<open>The order \<open><o\<close> refines the spine lexicographic order\<close>

text \<open>\<open>slex xs ys\<close>: lexicographic \<open>\<le>\<close> on subscript lists, with the empty list (a
  spine that has ended) counted as smallest, i.e. a proper prefix is smaller.\<close>

fun slex :: "nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "slex [] ys = True"
| "slex (x # xs) [] = False"
| "slex (x # xs) (y # ys) = (x < y \<or> (x = y \<and> slex xs ys))"

lemma slex_refl: "slex xs xs"
  by (induction xs) auto

lemma olt_imp_slex: "w <o x \<Longrightarrow> slex (spine w) (spine x)"
proof (induction x arbitrary: w)
  case Z
  then show ?case using not_olt_Z by blast
next
  case (P e f g)
  show ?case
  proof (cases w)
    case Z
    then show ?thesis by simp
  next
    case (P a b c)
    have "(a < e) \<or> (a = e \<and> b <o f) \<or> (a = e \<and> b = f \<and> c <o g)"
      using P.prems by (simp add: \<open>w = P a b c\<close>)
    then show ?thesis
    proof (elim disjE)
      assume "a < e"
      then show ?thesis by (simp add: \<open>w = P a b c\<close>)
    next
      assume "a = e \<and> b <o f"
      then have "slex (spine b) (spine f)" using P.IH(1) by blast
      then show ?thesis using \<open>a = e \<and> b <o f\<close> by (simp add: \<open>w = P a b c\<close>)
    next
      assume "a = e \<and> b = f \<and> c <o g"
      then show ?thesis using slex_refl by (simp add: \<open>w = P a b c\<close>)
    qed
  qed
qed

subsection \<open>From \<open>slex\<close> and the NF invariants to subscript monotonicity\<close>

text \<open>If two lists agree on a prefix of length \<open>k\<close> and at position \<open>k\<close> the first
  list is strictly larger (or the second has ended), they are not \<open>slex\<close>-below.\<close>

lemma not_slex_of_gt:
  "\<lbrakk> take k xs = take k ys; k < length xs;
     (length ys \<le> k \<or> ys ! k < xs ! k) \<rbrakk> \<Longrightarrow> \<not> slex xs ys"
proof (induction k arbitrary: xs ys)
  case 0
  then obtain x xs' where xs: "xs = x # xs'" by (cases xs) auto
  show ?case
  proof (cases ys)
    case Nil
    then show ?thesis using xs by simp
  next
    case (Cons y ys')
    with 0 xs have "y < x" by simp
    then show ?thesis using xs Cons by simp
  qed
next
  case (Suc k)
  from \<open>Suc k < length xs\<close> obtain x xs' where xs: "xs = x # xs'" by (cases xs) auto
  from \<open>take (Suc k) xs = take (Suc k) ys\<close> xs obtain y ys' where ys: "ys = y # ys'"
    by (cases ys) auto
  from \<open>take (Suc k) xs = take (Suc k) ys\<close> xs ys
  have xy: "x = y" and tk: "take k xs' = take k ys'" by auto
  from \<open>Suc k < length xs\<close> xs have klen: "k < length xs'" by simp
  from \<open>length ys \<le> Suc k \<or> ys ! Suc k < xs ! Suc k\<close> xs ys
  have "length ys' \<le> k \<or> ys' ! k < xs' ! k" by auto
  with tk klen have "\<not> slex xs' ys'" using Suc.IH by blast
  then show ?case using xs ys xy by simp
qed

text \<open>The NF invariant on a spine \<open>s\<close>: it begins \<open>0,1,\<dots>,cmax s\<close>.\<close>

definition inv2 :: "nat list \<Rightarrow> bool" where
  "inv2 s \<longleftrightarrow> (\<forall>i\<le>cmax s. i < length s \<and> s ! i = i)"

lemma take_eq_of_inv2:
  assumes "inv2 sw" and "inv2 sx" and "k \<le> Suc (cmax sw)" and "k \<le> Suc (cmax sx)"
  shows "take k sw = take k sx"
proof (rule nth_equalityI)
  have "cmax sw < length sw" using assms(1) unfolding inv2_def by blast
  hence lw: "k \<le> length sw" using assms(3) by simp
  have "cmax sx < length sx" using assms(2) unfolding inv2_def by blast
  hence lx: "k \<le> length sx" using assms(4) by simp
  show "length (take k sw) = length (take k sx)" using lw lx by simp
  fix i assume "i < length (take k sw)"
  then have ik: "i < k" using lw by simp
  then have "i \<le> cmax sw" "i \<le> cmax sx" using assms(3,4) by auto
  then have "sw ! i = i" "sx ! i = i" using assms(1,2) unfolding inv2_def by auto
  then show "take k sw ! i = take k sx ! i" using ik lw lx by simp
qed

lemma cmax_le_of_slex:
  assumes sl: "slex sw sx" and iw: "inv2 sw" and ix: "inv2 sx"
  shows "cmax sw \<le> cmax sx"
proof (rule ccontr)
  assume "\<not> cmax sw \<le> cmax sx"
  then have gt: "cmax sx < cmax sw" by simp
  let ?k = "Suc (cmax sx)"
  have kw': "?k \<le> cmax sw" using gt by simp
  \<comment> \<open>agreement on the common prefix of length \<open>cmax sx + 1\<close>\<close>
  have take_eq: "take ?k sw = take ?k sx"
  proof (rule take_eq_of_inv2[OF iw ix])
    show "?k \<le> Suc (cmax sw)" using kw' by simp
    show "?k \<le> Suc (cmax sx)" by simp
  qed
  \<comment> \<open>position \<open>?k\<close> exists in \<open>sw\<close> and carries value \<open>?k\<close>\<close>
  have inw: "?k < length sw \<and> sw ! ?k = ?k" using iw kw' unfolding inv2_def by blast
  \<comment> \<open>in \<open>sx\<close> everything is \<le> \<open>cmax sx < ?k\<close>\<close>
  have hi: "length sx \<le> ?k \<or> sx ! ?k < sw ! ?k"
  proof (cases "?k < length sx")
    case True
    then have "sx ! ?k \<in> set sx" by simp
    then have "sx ! ?k \<le> cmax sx" by (rule cmax_ge)
    also have "cmax sx < ?k" by simp
    also have "?k = sw ! ?k" using inw by simp
    finally show ?thesis by simp
  next
    case False
    then show ?thesis by simp
  qed
  have "\<not> slex sw sx"
    using not_slex_of_gt[OF take_eq] inw hi by simp
  with sl show False by simp
qed

lemma climb_mono:
  assumes "w <o x" and "inv2 (spine w)" and "inv2 (spine x)"
  shows "climb w \<le> climb x"
  using cmax_le_of_slex[OF olt_imp_slex[OF assms(1)] assms(2,3)] .

text \<open>Subscript monotonicity of descent, modulo the NF invariants
  \<open>maxsub = climb\<close> (every subscript is \<le> the spine maximum) and \<open>inv2\<close> (the spine
  begins \<open>0,1,\<dots>,maxsub\<close>).\<close>

theorem maxsub_mono_cond:
  assumes "w <o x"
    and "maxsub w = climb w" and "maxsub x = climb x"
    and "inv2 (spine w)" and "inv2 (spine x)"
  shows "maxsub w \<le> maxsub x"
  using climb_mono[OF assms(1) assms(4,5)] assms(2,3) by simp


subsection \<open>The spine as the strictly-increasing-row-0 prefix\<close>

text \<open>The leftmost argument spine of \<open>translate M\<close> reads off the row-1 values of
  the maximal prefix of \<open>M\<close> along which row 0 (\<open>fst\<close>) strictly increases.\<close>

fun incpref :: "pairseq \<Rightarrow> pairseq" where
  "incpref [] = []"
| "incpref [p] = [p]"
| "incpref (p # q # rest) = (if fst p < fst q then p # incpref (q # rest) else [p])"

lemma takeWhile_fst_nest:
  fixes a b :: nat and xs :: pairseq
  assumes "a < b"
  shows "takeWhile (\<lambda>x. b < fst x) (takeWhile (\<lambda>x. a < fst x) xs)
         = takeWhile (\<lambda>x. b < fst x) xs"
proof -
  have "(\<lambda>x::nat\<times>nat. (a < fst x) \<and> (b < fst x)) = (\<lambda>x. b < fst x)"
    using assms by (auto simp: fun_eq_iff intro: less_trans)
  thus ?thesis by (simp add: takeWhile_takeWhile)
qed

lemma spine_translate_eq: "spine (translate M) = map snd (incpref M)"
proof (induction M rule: incpref.induct)
  case 1
  show ?case by simp
next
  case (2 p)
  show ?case by simp
next
  case (3 p q rest)
  show ?case
  proof (cases "fst p < fst q")
    case False
    then have "takeWhile (\<lambda>x. fst p < fst x) (q # rest) = []" by simp
    then show ?thesis using False by simp
  next
    case True
    have tw: "takeWhile (\<lambda>x. fst p < fst x) (q # rest) = q # takeWhile (\<lambda>x. fst p < fst x) rest"
      using True by simp
    have nest: "takeWhile (\<lambda>x. fst q < fst x) (takeWhile (\<lambda>x. fst p < fst x) rest)
          = takeWhile (\<lambda>x. fst q < fst x) rest"
      using takeWhile_fst_nest[OF True] .
    have "spine (translate (p # q # rest))
          = snd p # spine (translate (q # takeWhile (\<lambda>x. fst p < fst x) rest))"
      using tw by simp
    also have "\<dots> = snd p # snd q # spine (translate (takeWhile (\<lambda>x. fst q < fst x) rest))"
      using nest by simp
    also have "\<dots> = snd p # spine (translate (q # rest))" by simp
    also have "\<dots> = snd p # map snd (incpref (q # rest))" using "3.IH" True by simp
    also have "\<dots> = map snd (incpref (p # q # rest))" using True by simp
    finally show ?thesis .
  qed
qed


subsection \<open>The NF invariants for the diagonal towers (base case)\<close>

lemma diagSeq_Cons:
  assumes "u \<le> v"
  shows "diagSeq u v = (u, u) # diagSeq (Suc u) v"
proof -
  have "[u..<Suc v] = u # [Suc u..<Suc v]" using assms by (simp add: upt_conv_Cons)
  thus ?thesis by (simp add: diagSeq_def)
qed

lemma fst_in_diagSeq:
  assumes "q \<in> set (diagSeq a b)"
  shows "fst q \<ge> a"
  using assms by (auto simp: diagSeq_def)

lemma translate_diagSeq:
  "u \<le> v \<Longrightarrow> translate (diagSeq u v) = P u (translate (diagSeq (Suc u) v)) Z"
proof -
  assume uv: "u \<le> v"
  have rest: "diagSeq u v = (u, u) # diagSeq (Suc u) v" using uv by (rule diagSeq_Cons)
  have allgt: "\<forall>q \<in> set (diagSeq (Suc u) v). u < fst q"
    using fst_in_diagSeq[of _ "Suc u" v] by fastforce
  have tw: "takeWhile (\<lambda>q. u < fst q) (diagSeq (Suc u) v) = diagSeq (Suc u) v"
    using allgt by (simp add: takeWhile_eq_all_conv)
  have dw: "dropWhile (\<lambda>q. u < fst q) (diagSeq (Suc u) v) = []"
    using allgt by (simp add: dropWhile_eq_Nil_conv)
  show ?thesis by (simp add: rest tw dw)
qed

lemma cmax_le: "(\<forall>x \<in> set xs. x \<le> b) \<Longrightarrow> cmax xs \<le> b"
  by (induction xs) auto

lemma spine_translate_diagSeq_aux:
  "spine (translate (diagSeq u (u + n))) = [u..<Suc (u + n)]"
proof (induction n arbitrary: u)
  case 0
  have e: "diagSeq (Suc u) u = []" by (simp add: diagSeq_def)
  have "spine (translate (diagSeq u u)) = [u]"
    using translate_diagSeq[of u u] e by simp
  thus ?case by simp
next
  case (Suc n)
  have le: "u \<le> u + Suc n" by simp
  have step1: "spine (translate (diagSeq u (u + Suc n)))
        = u # spine (translate (diagSeq (Suc u) (u + Suc n)))"
    using translate_diagSeq[OF le] by simp
  have shift: "diagSeq (Suc u) (u + Suc n) = diagSeq (Suc u) (Suc u + n)" by simp
  have ih: "spine (translate (diagSeq (Suc u) (Suc u + n))) = [Suc u..<Suc (Suc u + n)]"
    using Suc.IH[of "Suc u"] by simp
  have cons: "[u..<Suc (u + Suc n)] = u # [Suc u..<Suc (u + Suc n)]"
    by (simp add: upt_conv_Cons)
  have arith: "Suc (u + Suc n) = Suc (Suc u + n)" by simp
  show ?case
    using step1 shift ih cons arith by simp
qed

lemma spine_translate_diagSeq:
  assumes "u \<le> v" shows "spine (translate (diagSeq u v)) = [u..<Suc v]"
proof -
  have "v = u + (v - u)" using assms by simp
  thus ?thesis using spine_translate_diagSeq_aux[of u "v - u"] by simp
qed

lemma cmax_upt:
  assumes "u \<le> v" shows "cmax [u..<Suc v] = v"
proof -
  have "v \<in> set [u..<Suc v]" using assms by simp
  hence ge: "v \<le> cmax [u..<Suc v]" by (rule cmax_ge)
  have "\<forall>x \<in> set [u..<Suc v]. x \<le> v" by auto
  hence "cmax [u..<Suc v] \<le> v" by (rule cmax_le)
  with ge show ?thesis by simp
qed

text \<open>For the diagonal towers \<open>D(v) = translate (diagSeq 0 v)\<close> the two NF
  invariants hold: the spine is exactly \<open>[0,1,\<dots>,v]\<close>, so \<open>inv2\<close> holds and
  \<open>maxsub = climb = v\<close>.\<close>

lemma spine_diagSeq0: "spine (translate (diagSeq 0 v)) = [0..<Suc v]"
  using spine_translate_diagSeq[of 0 v] by simp

lemma climb_diagSeq0: "climb (translate (diagSeq 0 v)) = v"
  using spine_diagSeq0 cmax_upt[of 0 v] by simp

lemma inv2_spine_diagSeq0: "inv2 (spine (translate (diagSeq 0 v)))"
proof (unfold inv2_def, intro allI impI conjI)
  fix i assume "i \<le> cmax (spine (translate (diagSeq 0 v)))"
  then have iv: "i \<le> v" using climb_diagSeq0 by simp
  show "i < length (spine (translate (diagSeq 0 v)))"
    using spine_diagSeq0 iv by simp
  have "spine (translate (diagSeq 0 v)) ! i = [0..<Suc v] ! i"
    using spine_diagSeq0 by simp
  also have "\<dots> = i" using iv by (simp del: upt_Suc add: nth_upt)
  finally show "spine (translate (diagSeq 0 v)) ! i = i" .
qed

end
