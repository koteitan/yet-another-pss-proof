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

lemma cmax_le: "(\<forall>x \<in> set xs. x \<le> b) \<Longrightarrow> cmax xs \<le> b"
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

lemma incpref_append: "\<exists>ys. incpref M @ ys = M"
proof (induction M rule: incpref.induct)
  case 1 show ?case by simp
next
  case (2 p) show ?case by simp
next
  case (3 p q rest)
  show ?case
  proof (cases "fst p < fst q")
    case True
    from "3.IH"[OF True] obtain ys where "incpref (q # rest) @ ys = q # rest" by blast
    hence "(p # incpref (q # rest)) @ ys = p # q # rest" by simp
    thus ?thesis using True by auto
  next
    case False
    thus ?thesis by auto
  qed
qed

lemma incpref_fst_sorted: "sorted_wrt (\<lambda>x y. fst x < fst y) (incpref M)"
proof (induction M rule: incpref.induct)
  case 1 show ?case by simp
next
  case (2 p) show ?case by simp
next
  case (3 p q rest)
  show ?case
  proof (cases "fst p < fst q")
    case True
    have IHsorted: "sorted_wrt (\<lambda>x y. fst x < fst y) (incpref (q # rest))"
      using "3.IH"[OF True] .
    have hd: "incpref (q # rest) = q # tl (incpref (q # rest))"
      by (cases rest) auto
    \<comment> \<open>every element of \<open>incpref (q # rest)\<close> has row 0 \<ge> fst q\<close>
    have ge: "\<forall>z \<in> set (incpref (q # rest)). fst q \<le> fst z"
    proof
      fix z assume "z \<in> set (incpref (q # rest))"
      then consider "z = q" | "z \<in> set (tl (incpref (q # rest)))"
        using hd by (metis set_ConsD)
      thus "fst q \<le> fst z"
      proof cases
        case 1 thus ?thesis by simp
      next
        case 2
        from IHsorted hd have "\<forall>z \<in> set (tl (incpref (q # rest))). fst q < fst z"
          by (metis sorted_wrt.simps(2))
        with 2 show ?thesis by auto
      qed
    qed
    have "\<forall>z \<in> set (incpref (q # rest)). fst p < fst z" using ge True by fastforce
    thus ?thesis using True IHsorted by simp
  next
    case False
    thus ?thesis by simp
  qed
qed

lemma incpref_snoc:
  "incpref (ys @ [x]) =
     (if incpref ys = ys \<and> (ys = [] \<or> fst (last ys) < fst x) then ys @ [x] else incpref ys)"
proof (induction ys rule: incpref.induct)
  case 1 thus ?case by simp
next
  case (2 p) thus ?case by auto
next
  case (3 p q rest)
  show ?case
  proof (cases "fst p < fst q")
    case False thus ?thesis by simp
  next
    case True
    have e: "incpref ((p # q # rest) @ [x]) = p # incpref ((q # rest) @ [x])"
      using True by simp
    have ih: "incpref ((q # rest) @ [x])
              = (if incpref (q # rest) = q # rest \<and> fst (last (q # rest)) < fst x
                 then (q # rest) @ [x] else incpref (q # rest))"
      using "3.IH"[OF True] by simp
    show ?thesis
    proof (cases "incpref (q # rest) = q # rest \<and> fst (last (q # rest)) < fst x")
      case True
      then have "incpref ((p # q # rest) @ [x]) = p # (q # rest) @ [x]"
        using e ih by simp
      moreover have "incpref (p # q # rest) = p # q # rest"
        using \<open>fst p < fst q\<close> True by simp
      ultimately show ?thesis using \<open>fst p < fst q\<close> True by simp
    next
      case False
      then have "incpref ((p # q # rest) @ [x]) = p # incpref (q # rest)"
        using e ih by simp
      moreover have "\<not> (incpref (p # q # rest) = p # q # rest \<and> fst (last (p # q # rest)) < fst x)"
        using \<open>fst p < fst q\<close> False by auto
      ultimately show ?thesis using \<open>fst p < fst q\<close> by simp
    qed
  qed
qed

lemma incpref_append_stop:
  "incpref ys \<noteq> ys \<Longrightarrow> incpref (ys @ zs) = incpref ys"
proof (induction ys rule: incpref.induct)
  case 1 thus ?case by simp
next
  case (2 p) thus ?case by simp
next
  case (3 p q rest)
  show ?case
  proof (cases "fst p < fst q")
    case False thus ?thesis by simp
  next
    case True
    then have ne: "incpref (q # rest) \<noteq> q # rest" using "3.prems" by simp
    have "incpref ((p # q # rest) @ zs) = p # incpref ((q # rest) @ zs)"
      using True by simp
    also have "\<dots> = p # incpref (q # rest)" using "3.IH"[OF True ne] by simp
    also have "\<dots> = incpref (p # q # rest)" using True by simp
    finally show ?thesis .
  qed
qed

lemma incpref_append_full:
  "incpref ys = ys \<Longrightarrow> \<exists>ws. incpref (ys @ zs) = ys @ ws"
proof (induction ys rule: incpref.induct)
  case 1
  show ?case by simp
next
  case (2 p)
  have "\<exists>ws. incpref (p # zs) = p # ws"
    by (cases zs) auto
  thus ?case by simp
next
  case (3 p q rest)
  have pq: "fst p < fst q" using "3.prems" by (cases "fst p < fst q") auto
  have ihcond: "incpref (q # rest) = q # rest" using "3.prems" pq by simp
  from "3.IH"[OF pq ihcond] obtain ws where
    ws: "incpref ((q # rest) @ zs) = (q # rest) @ ws" by blast
  have "incpref ((p # q # rest) @ zs) = p # incpref ((q # rest) @ zs)" using pq by simp
  also have "\<dots> = (p # q # rest) @ ws" using ws by simp
  finally show ?case by blast
qed

lemma incpref_butlast:
  "incpref (butlast M) = (if incpref M = M then butlast M else incpref M)"
proof (cases "M = []")
  case True thus ?thesis by simp
next
  case False
  then have M: "M = butlast M @ [last M]" by simp
  let ?ys = "butlast M"
  let ?c = "incpref ?ys = ?ys \<and> (?ys = [] \<or> fst (last ?ys) < fst (last M))"
  have eqM: "incpref M = incpref (?ys @ [last M])" by (metis M)
  have snoc: "incpref (?ys @ [last M]) = (if ?c then ?ys @ [last M] else incpref ?ys)"
    by (rule incpref_snoc)
  show ?thesis
  proof (cases ?c)
    case True
    have "incpref M = ?ys @ [last M]" using eqM snoc True by simp
    hence "incpref M = M" using M by simp
    moreover have "incpref ?ys = ?ys" using True by simp
    ultimately show ?thesis by simp
  next
    case False
    have eq: "incpref M = incpref ?ys" using eqM snoc False by simp
    have "incpref M \<noteq> M"
    proof
      assume "incpref M = M"
      with eq have "incpref ?ys = M" by simp
      hence "length M = length (incpref ?ys)" by simp
      also have "\<dots> \<le> length ?ys"
        using incpref_append[of ?ys] by (metis le_add1 length_append)
      also have "\<dots> < length M" using M by (metis length_append_singleton lessI)
      finally show False by simp
    qed
    with eq show ?thesis by simp
  qed
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


subsection \<open>The maximal subscript is the maximal row-1 value\<close>

lemma cmax_append: "cmax (xs @ ys) = max (cmax xs) (cmax ys)"
  by (induction xs) auto

lemma maxsub_translate: "maxsub (translate M) = cmax (map snd M)"
proof (induction M rule: translate.induct)
  case 1
  show ?case by simp
next
  case (2 p rest)
  have key: "cmax (map snd rest)
        = max (cmax (map snd (takeWhile (\<lambda>q. fst p < fst q) rest)))
              (cmax (map snd (dropWhile (\<lambda>q. fst p < fst q) rest)))"
    by (metis cmax_append map_append takeWhile_dropWhile_id)
  show ?case using 2 key by simp
qed

text \<open>So the maximal-subscript invariant \<open>maxsub = climb\<close> is the pair-sequence
  statement \<open>cmax (map snd M) = cmax (map snd (incpref M))\<close>: the maximal row-1
  value of \<open>M\<close> is attained already within its strictly-increasing-row-0 prefix.\<close>

lemma maxsub_eq_climb_iff:
  "maxsub (translate M) = climb (translate M)
     \<longleftrightarrow> cmax (map snd M) = cmax (map snd (incpref M))"
  by (simp add: maxsub_translate spine_translate_eq)


subsection \<open>The pair-sequence normal-form invariant and its closure\<close>

definition nfinv :: "pairseq \<Rightarrow> bool" where
  "nfinv M \<longleftrightarrow> cmax (map snd M) = cmax (map snd (incpref M))
                \<and> inv2 (map snd (incpref M))"

lemma cmax_mem: "xs \<noteq> [] \<Longrightarrow> cmax xs \<in> set xs"
proof (induction xs)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "cmax xs \<le> x")
    case True hence "cmax (x # xs) = x" by simp
    thus ?thesis by simp
  next
    case False
    hence "cmax (x # xs) = cmax xs" by simp
    moreover have "xs \<noteq> []" using False by auto
    ultimately show ?thesis using Cons.IH by simp
  qed
qed

lemma cmax_butlast_le: "cmax (butlast xs) \<le> cmax xs"
proof (rule cmax_le)
  show "\<forall>x\<in>set (butlast xs). x \<le> cmax xs"
    using cmax_ge in_set_butlastD by fast
qed

lemma inv2_butlast:
  assumes inv: "inv2 xs" and ne: "butlast xs \<noteq> []"
  shows "inv2 (butlast xs)"
proof -
  let ?r = "cmax (butlast xs)"
  have rR: "?r \<le> cmax xs" by (rule cmax_butlast_le)
  have key: "?r < length (butlast xs)"
  proof (rule ccontr)
    assume "\<not> ?r < length (butlast xs)"
    then have le: "length (butlast xs) \<le> ?r" by simp
    have "?r \<in> set (butlast xs)" using ne by (rule cmax_mem)
    then obtain j where j: "j < length (butlast xs)" and xj: "butlast xs ! j = ?r"
      by (metis in_set_conv_nth)
    have "j < ?r" using j le by simp
    hence "j \<le> cmax xs" using rR by simp
    hence "xs ! j = j" using inv unfolding inv2_def by auto
    moreover have "xs ! j = ?r" using xj j by (simp add: nth_butlast)
    ultimately show False using \<open>j < ?r\<close> by simp
  qed
  show ?thesis
  proof (unfold inv2_def, intro allI impI conjI)
    fix i assume "i \<le> ?r"
    then have ir: "i \<le> cmax xs" using rR by simp
    show "i < length (butlast xs)" using \<open>i \<le> ?r\<close> key by simp
    have "xs ! i = i" using ir inv unfolding inv2_def by auto
    moreover have "butlast xs ! i = xs ! i"
      using \<open>i \<le> ?r\<close> key by (simp add: nth_butlast)
    ultimately show "butlast xs ! i = i" by simp
  qed
qed

text \<open>The key closure: appending a block whose row-1 values already occur in
  \<open>ys\<close> preserves \<open>nfinv\<close>.\<close>

lemma nfinv_append:
  assumes inv: "nfinv ys" and sub: "snd ` set R \<subseteq> snd ` set ys"
  shows "nfinv (ys @ R)"
proof -
  have cmaxR: "cmax (map snd R) \<le> cmax (map snd ys)"
  proof (rule cmax_le, rule ballI)
    fix x assume "x \<in> set (map snd R)"
    then have "x \<in> snd ` set R" by simp
    then have "x \<in> snd ` set ys" using sub by blast
    then have "x \<in> set (map snd ys)" by simp
    thus "x \<le> cmax (map snd ys)" by (rule cmax_ge)
  qed
  have cmax_all: "cmax (map snd (ys @ R)) = cmax (map snd ys)"
    using cmaxR by (simp add: cmax_append)
  from inv have A: "cmax (map snd ys) = cmax (map snd (incpref ys))"
    and B: "inv2 (map snd (incpref ys))" by (auto simp: nfinv_def)
  show ?thesis
  proof (cases "incpref ys = ys")
    case False
    have ip: "incpref (ys @ R) = incpref ys" by (rule incpref_append_stop[OF False])
    show ?thesis using A B cmax_all ip by (simp add: nfinv_def)
  next
    case True
    obtain ws where ws: "incpref (ys @ R) = ys @ ws"
      using incpref_append_full[OF True] by blast
    \<comment> \<open>\<open>ws\<close> is a prefix of \<open>R\<close>, so its row-1 values are bounded\<close>
    have wsR: "snd ` set ws \<subseteq> snd ` set ys"
    proof -
      have "ys @ ws = incpref (ys @ R)" using ws by simp
      then obtain zs where "ys @ ws @ zs = ys @ R"
        using incpref_append by (metis append.assoc)
      hence "ws @ zs = R" by simp
      hence "set ws \<subseteq> set R" by (metis Un_iff set_append subsetI)
      thus ?thesis using sub by auto
    qed
    have cmws: "cmax (map snd ws) \<le> cmax (map snd ys)"
    proof (rule cmax_le, rule ballI)
      fix x assume "x \<in> set (map snd ws)"
      then have "x \<in> snd ` set ws" by simp
      then have "x \<in> snd ` set ys" using wsR by blast
      then have "x \<in> set (map snd ys)" by simp
      thus "x \<le> cmax (map snd ys)" by (rule cmax_ge)
    qed
    have climb_all: "cmax (map snd (incpref (ys @ R))) = cmax (map snd ys)"
      using ws cmws by (simp add: cmax_append)
    \<comment> \<open>invariant on \<open>map snd ys @ map snd ws\<close>\<close>
    have invys: "inv2 (map snd ys)" using B True by simp
    have Bys: "inv2 (map snd ys)" using B True by simp
    have "inv2 (map snd (ys @ ws))"
    proof (unfold inv2_def, intro allI impI conjI)
      fix i assume "i \<le> cmax (map snd (ys @ ws))"
      then have ic: "i \<le> cmax (map snd ys)" using cmws by (simp add: cmax_append)
      have ilen: "i < length ys" using Bys ic unfolding inv2_def by auto
      show "i < length (map snd (ys @ ws))" using ilen by simp
      have b: "snd (ys ! i) = i"
      proof -
        from Bys ic have "map snd ys ! i = i" unfolding inv2_def by blast
        with ilen show ?thesis by (metis nth_map)
      qed
      have "map snd (ys @ ws) ! i = snd (ys ! i)"
        using ilen by (simp add: nth_append)
      thus "map snd (ys @ ws) ! i = i" using b by simp
    qed
    thus ?thesis using ws cmax_all climb_all by (simp add: nfinv_def)
  qed
qed


lemma nfinv_butlast:
  assumes inv: "nfinv M" and ne: "butlast M \<noteq> []"
  shows "nfinv (butlast M)"
proof -
  from inv have A: "cmax (map snd M) = cmax (map snd (incpref M))"
    and B: "inv2 (map snd (incpref M))" by (auto simp: nfinv_def)
  show ?thesis
  proof (cases "incpref M = M")
    case True
    have ip: "incpref (butlast M) = butlast M" using incpref_butlast True by simp
    have "inv2 (map snd (butlast M))"
    proof -
      have "inv2 (map snd M)" using B True by simp
      moreover have "butlast (map snd M) \<noteq> []" using ne by (simp add: map_butlast[symmetric])
      ultimately have "inv2 (butlast (map snd M))" by (rule inv2_butlast)
      thus ?thesis by (simp add: map_butlast)
    qed
    thus ?thesis using ip by (simp add: nfinv_def)
  next
    case False
    have ip: "incpref (butlast M) = incpref M" using incpref_butlast False by simp
    obtain ys where ysM: "incpref M @ ys = M" using incpref_append by blast
    have ysne: "ys \<noteq> []" using ysM False by auto
    have preb: "butlast M = incpref M @ butlast ys"
      using ysM ysne by (metis butlast_append)
    have subset: "set (map snd (incpref M)) \<subseteq> set (map snd (butlast M))"
      using preb by auto
    \<comment> \<open>\<open>(A)\<close> for \<open>butlast M\<close>\<close>
    have le1: "cmax (map snd (incpref M)) \<le> cmax (map snd (butlast M))"
      using subset cmax_ge by (intro cmax_le) blast
    have le2: "cmax (map snd (butlast M)) \<le> cmax (map snd M)"
      by (simp add: map_butlast cmax_butlast_le)
    have "cmax (map snd (butlast M)) = cmax (map snd (incpref M))"
      using le1 le2 A by simp
    thus ?thesis using ip B by (simp add: nfinv_def)
  qed
qed

subsection \<open>The bad-case expansion as \<open>butlast M\<close> followed by ascending copies\<close>

lemma take_split_map_nth:
  assumes "j0 \<le> m" and "m \<le> length xs"
  shows "take j0 xs @ map (\<lambda>j. xs ! j) [j0..<m] = take m xs"
proof -
  have "take (m - j0) (drop j0 xs) = map (\<lambda>i. xs ! i) [j0..<m]"
  proof -
    have "drop j0 xs = map (\<lambda>i. xs ! i) [j0..<length xs]" by (rule drop_eq_map_nth)
    hence "take (m - j0) (drop j0 xs) = map (\<lambda>i. xs ! i) (take (m - j0) [j0..<length xs])"
      by (simp add: take_map)
    also have "take (m - j0) [j0..<length xs] = [j0..<m]"
      using assms by (simp add: take_upt)
    finally show ?thesis .
  qed
  moreover have "take m xs = take j0 xs @ take (m - j0) (drop j0 xs)"
    using assms by (metis le_add_diff_inverse take_add)
  ultimately show ?thesis by simp
qed

lemma nextR_less: "nextR M i j0 j1 \<Longrightarrow> j0 < j1"
  by (auto simp: nextR_def nextrel0_def nextrel1_def split: if_splits)

lemma parent_less:
  assumes "hasParent M i j1" shows "parent M i j1 < j1"
proof -
  from assms have "nextR M i (parent M i j1) j1"
    by (metis hasParent_def parent_def theI')
  thus ?thesis by (rule nextR_less)
qed

text \<open>In the bad case the \<open>k = 0\<close> copy reproduces the dropped suffix, so the
  expansion is \<open>butlast M\<close> followed by the (\<open>k \<ge> 1\<close>) ascending copies; the copies
  only repeat row-1 values already present in \<open>butlast M\<close>.\<close>

lemma oper_bad_eq_butlast_append:
  assumes L: "Lng M - 1 \<noteq> 0"
    and nz: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and n1: "1 \<le> n"
  shows "\<exists>R. M[n] = butlast M @ R \<and> snd ` set R \<subseteq> snd ` set (butlast M)"
proof -
  let ?i1 = "idx1 M (Lng M - 1)"
  let ?j0 = "parent M ?i1 (Lng M - 1)"
  let ?d0 = "if 0 < ?i1 then entry M 0 (Lng M - 1) - entry M 0 ?j0 else (0::nat)"
  let ?cp = "\<lambda>k. map (\<lambda>j. (entry M 0 j + k * ?d0, entry M 1 j)) [?j0..<Lng M - 1]"
  have unfold: "M[n] = take ?j0 M @ concat (map ?cp [0..<n])"
    using oper_bad_unfold[OF L nz hp] by simp
  have j0lt: "?j0 < Lng M - 1" using parent_less[OF hp] .
  have blt: "butlast M = take (Lng M - 1) M" by (simp add: butlast_conv_take)
  \<comment> \<open>the \<open>k = 0\<close> copy is the dropped suffix \<open>M\<^bsub>?j0\<^esub> \<dots> M\<^bsub>Lng M - 2\<^esub>\<close>\<close>
  have cp0: "?cp 0 = map (\<lambda>j. M ! j) [?j0..<Lng M - 1]"
    by (simp add: entry_def)
  have but: "take ?j0 M @ ?cp 0 = butlast M"
  proof -
    have "take ?j0 M @ ?cp 0 = take ?j0 M @ map (\<lambda>j. M ! j) [?j0..<Lng M - 1]"
      using cp0 by simp
    also have "\<dots> = take (Lng M - 1) M"
      using take_split_map_nth[of ?j0 "Lng M - 1" M] j0lt by simp
    finally show ?thesis using blt by simp
  qed
  have nsplit: "M[n] = butlast M @ concat (map ?cp [Suc 0..<n])"
  proof -
    have "[0..<n] = 0 # [Suc 0..<n]" using n1 by (simp add: upt_conv_Cons)
    hence "concat (map ?cp [0..<n]) = ?cp 0 @ concat (map ?cp [Suc 0..<n])" by simp
    thus ?thesis using unfold but by simp
  qed
  let ?R = "concat (map ?cp [Suc 0..<n])"
  have "snd ` set ?R \<subseteq> snd ` set (butlast M)"
  proof
    fix s assume "s \<in> snd ` set ?R"
    then obtain j where j: "j \<in> {?j0..<Lng M - 1}" and sj: "s = entry M 1 j" by auto
    from j have jlt: "j < Lng M - 1" by simp
    have "j < length (take (Lng M - 1) M)" using jlt by simp
    then have "take (Lng M - 1) M ! j \<in> set (take (Lng M - 1) M)" by (rule nth_mem)
    moreover have "take (Lng M - 1) M ! j = M ! j" using jlt by simp
    ultimately have "M ! j \<in> set (butlast M)" using blt by simp
    moreover have "s = snd (M ! j)" using sj by (simp add: entry_def)
    ultimately show "s \<in> snd ` set (butlast M)" by (auto simp: image_iff)
  qed
  with nsplit show ?thesis by blast
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


subsection \<open>The NF invariant holds on all standard forms\<close>

text \<open>Unifying the three \<open>oper\<close> branches (for \<open>Lng M > 1\<close>): the expansion is
  always \<open>butlast M\<close> followed by a block whose row-1 values already occur in
  \<open>butlast M\<close>.\<close>

lemma oper_eq_butlast_append:
  assumes L: "1 < Lng M" and n1: "1 \<le> n"
  shows "\<exists>R. M[n] = butlast M @ R \<and> snd ` set R \<subseteq> snd ` set (butlast M)"
proof (cases "entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0")
  case True
  have "M[n] = butlast M" using True L by (simp add: oper_def Let_def Pred_def)
  thus ?thesis by auto
next
  case nz: False
  show ?thesis
  proof (cases "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)")
    case False
    have "M[n] = butlast M" using L nz False by (simp add: oper_def Let_def Pred_def)
    thus ?thesis by auto
  next
    case hp: True
    have "Lng M - 1 \<noteq> 0" using L by simp
    thus ?thesis using oper_bad_eq_butlast_append[OF _ nz hp n1] by blast
  qed
qed

lemma nfinv_diag: "nfinv (diagSeq 0 v)"
proof -
  have e1: "map snd (incpref (diagSeq 0 v)) = [0..<Suc v]"
    using spine_translate_eq[of "diagSeq 0 v"] spine_diagSeq0[of v] by simp
  have e2: "map snd (diagSeq 0 v) = [0..<Suc v]"
    by (simp add: diagSeq_def comp_def)
  have "inv2 (map snd (incpref (diagSeq 0 v)))"
    using inv2_spine_diagSeq0[of v] spine_translate_eq[of "diagSeq 0 v"] by simp
  moreover have "cmax (map snd (diagSeq 0 v)) = cmax (map snd (incpref (diagSeq 0 v)))"
    using e1 e2 by simp
  ultimately show ?thesis by (simp add: nfinv_def)
qed

lemma nfinv_ST_PS: "M \<in> ST_PS \<Longrightarrow> nfinv M"
proof (induction M rule: ST_PS.induct)
  case (diag v)
  show ?case by (rule nfinv_diag)
next
  case (oper M n)
  show ?case
  proof (cases "1 < Lng M")
    case False
    hence "M[n] = M" by (simp add: oper_eq_self_short)
    thus ?thesis using oper.IH by simp
  next
    case True
    obtain R where R: "M[n] = butlast M @ R"
      and Rsub: "snd ` set R \<subseteq> snd ` set (butlast M)"
      using oper_eq_butlast_append[OF True oper.hyps(2)] by blast
    have bne: "butlast M \<noteq> []"
      using True by (metis length_butlast length_greater_0_conv zero_less_diff)
    have "nfinv (butlast M)" using nfinv_butlast[OF oper.IH bne] .
    hence "nfinv (butlast M @ R)" using Rsub by (rule nfinv_append)
    thus ?thesis using R by simp
  qed
qed


subsection \<open>Subscript-monotonicity of descent on \<open>NF = translate ` ST_PS\<close>\<close>

theorem maxsub_mono_NF:
  assumes "Mw \<in> ST_PS" and "Mx \<in> ST_PS" and "translate Mw <o translate Mx"
  shows "maxsub (translate Mw) \<le> maxsub (translate Mx)"
proof (rule maxsub_mono_cond[OF assms(3)])
  show "maxsub (translate Mw) = climb (translate Mw)"
    using nfinv_ST_PS[OF assms(1)] by (simp add: maxsub_eq_climb_iff nfinv_def)
  show "maxsub (translate Mx) = climb (translate Mx)"
    using nfinv_ST_PS[OF assms(2)] by (simp add: maxsub_eq_climb_iff nfinv_def)
  show "inv2 (spine (translate Mw))"
    using nfinv_ST_PS[OF assms(1)] by (simp add: nfinv_def spine_translate_eq)
  show "inv2 (spine (translate Mx))"
    using nfinv_ST_PS[OF assms(2)] by (simp add: nfinv_def spine_translate_eq)
qed

lemma maxsub_mono_NF':
  assumes "v \<in> NF" and "u \<in> NF" and "v <o u"
  shows "maxsub v \<le> maxsub u"
proof -
  from assms(1) obtain Mv where Mv: "Mv \<in> ST_PS" "v = translate Mv" by auto
  from assms(2) obtain Mu where Mu: "Mu \<in> ST_PS" "u = translate Mu" by auto
  show ?thesis using maxsub_mono_NF[OF Mv(1) Mu(1)] assms(3) Mv(2) Mu(2) by simp
qed


subsection \<open>Cantor normal form: siblings are non-increasing\<close>

text \<open>The within-level order is not well-founded on \<open>nfinv\<close> terms alone (e.g.
  \<open>p\<^bsub>0\<^esub>(0) + p\<^bsub>0\<^esub>(p\<^bsub>0\<^esub>(0))\<close> has increasing siblings yet satisfies \<open>nfinv\<close>); the
  genuine standard forms additionally have \<^emph>\<open>non-increasing\<close> sibling sums (CNF).\<close>

fun cnf :: "three \<Rightarrow> bool" where
  "cnf Z = True"
| "cnf (P a b Z) = cnf b"
| "cnf (P a b (P e f g)) = (cnf b \<and> \<not> (P a b Z <o P e f Z) \<and> cnf (P e f g))"

lemma cnf_translate_diagSeq_aux: "cnf (translate (diagSeq u (u + n)))"
proof (induction n arbitrary: u)
  case 0
  have e: "diagSeq (Suc u) u = []" by (simp add: diagSeq_def)
  show ?case using translate_diagSeq[of u u] e by simp
next
  case (Suc n)
  have e: "translate (diagSeq u (u + Suc n))
           = P u (translate (diagSeq (Suc u) (u + Suc n))) Z"
    using translate_diagSeq[of u "u + Suc n"] by simp
  have shift: "diagSeq (Suc u) (u + Suc n) = diagSeq (Suc u) (Suc u + n)" by simp
  show ?case using e shift Suc.IH[of "Suc u"] by simp
qed

lemma cnf_diag: "cnf (translate (diagSeq 0 v))"
  using cnf_translate_diagSeq_aux[of 0 v] by simp

text \<open>\<open>cnf\<close> is preserved by dropping the last pair: if \<open>translate (D @ [m])\<close> is in CNF
  then so is \<open>translate D\<close>.  The interesting case appends \<open>m\<close> deep inside the last
  sibling block; the leading two-principal comparison is preserved because the
  earlier sibling's argument only grows (@{thm [source] translate_takeWhile_snoc_le})
  and @{thm [source] olt_ole_trans}.  This discharges the \<open>Pred\<close> case of \<open>cnf\<close>
  preservation under \<open>oper\<close>.\<close>

lemma cnf_snoc: "cnf (translate (D @ [m])) \<Longrightarrow> cnf (translate D)"
proof (induction D rule: translate.induct)
  case 1
  show ?case by simp
next
  case (2 p rest)
  let ?P = "\<lambda>q. fst p < fst q"
  let ?tw = "takeWhile ?P rest"
  let ?dw = "dropWhile ?P rest"
  show ?case
  proof (cases "\<forall>x\<in>set rest. ?P x")
    case allp: True
    have tw: "?tw = rest" using allp by (simp add: takeWhile_eq_all_conv)
    have dw: "?dw = []" using allp by (simp add: dropWhile_eq_Nil_conv)
    have eq0: "translate (p # rest) = P (snd p) (translate rest) Z"
    proof -
      have a: "translate ?tw = translate rest" by (simp only: tw)
      have b: "translate ?dw = Z" by (simp only: dw translate.simps(1))
      show ?thesis using a b by simp
    qed
    show ?thesis
    proof (cases "?P m")
      case True
      have "cnf (translate (rest @ [m]))"
        using "2.prems" allp True by (simp add: takeWhile_eq_all_conv dropWhile_eq_Nil_conv)
      hence "cnf (translate rest)" using "2.IH"(1) tw by simp
      thus ?thesis using eq0 by simp
    next
      case False
      have "translate ((p # rest) @ [m]) = P (snd p) (translate rest) (P (snd m) Z Z)"
        using allp False by (simp add: takeWhile_append2 dropWhile_append2)
      hence "cnf (translate rest)" using "2.prems" by simp
      thus ?thesis using eq0 by simp
    qed
  next
    case notall: False
    then obtain x where x: "x \<in> set rest" "\<not> ?P x" by blast
    have tw': "takeWhile ?P (rest @ [m]) = ?tw" using x by (simp add: takeWhile_append1)
    have dw': "dropWhile ?P (rest @ [m]) = ?dw @ [m]" using x by (simp add: dropWhile_append1)
    have dwne: "?dw \<noteq> []" using x by (auto simp: dropWhile_eq_Nil_conv)
    have hyp: "cnf (P (snd p) (translate ?tw) (translate (?dw @ [m])))"
      using "2.prems" tw' dw' by simp
    from dwne obtain q rest2 where dwq: "?dw = q # rest2" by (cases ?dw) auto
    let ?Q = "\<lambda>y. fst q < fst y"
    let ?f  = "translate (takeWhile ?Q rest2)"
    let ?f' = "translate (takeWhile ?Q (rest2 @ [m]))"
    let ?g  = "translate (dropWhile ?Q rest2)"
    let ?g' = "translate (dropWhile ?Q (rest2 @ [m]))"
    have td:  "translate ?dw = P (snd q) ?f ?g" using dwq by simp
    have td': "translate (?dw @ [m]) = P (snd q) ?f' ?g'" using dwq by simp
    have fle: "?f \<le>o ?f'" using translate_takeWhile_snoc_le[of "fst q" rest2 m] by simp
    \<comment> \<open>unfold the CNF of the snoc'd term\<close>
    have H: "cnf (translate ?tw)
             \<and> \<not> (P (snd p) (translate ?tw) Z <o P (snd q) ?f' Z)
             \<and> cnf (P (snd q) ?f' ?g')"
      using hyp td' by simp
    have cb: "cnf (translate ?tw)" using H by simp
    have sib': "\<not> (P (snd p) (translate ?tw) Z <o P (snd q) ?f' Z)" using H by simp
    have cdw: "cnf (translate ?dw)" using "2.IH"(2) H td' by simp
    \<comment> \<open>transfer the sibling non-increase from \<open>?f'\<close> back to \<open>?f\<close>\<close>
    have leP: "P (snd q) ?f Z \<le>o P (snd q) ?f' Z" using fle olt_P_b by blast
    have sib: "\<not> (P (snd p) (translate ?tw) Z <o P (snd q) ?f Z)"
    proof
      assume "P (snd p) (translate ?tw) Z <o P (snd q) ?f Z"
      from olt_ole_trans[OF this leP] show False using sib' by simp
    qed
    show ?thesis using td cb cdw sib by simp
  qed
qed

lemma cnf_butlast: "C \<noteq> [] \<Longrightarrow> cnf (translate C) \<Longrightarrow> cnf (translate (butlast C))"
  using cnf_snoc[of "butlast C" "last C"] by (simp add: snoc_eq_iff_butlast)

text \<open>The top-level sibling subscripts of a term (its \<open>+\<close>-chain of principals).\<close>

fun tops :: "three \<Rightarrow> nat list" where
  "tops Z = []"
| "tops (P a b c) = a # tops c"

text \<open>In a CNF term the leading subscript caps every sibling subscript: the \<open>+\<close>-chain
  is non-increasing in the subscripts.  This is what lets the leading principal of
  the embedding dominate the whole tail in the order-preservation argument.\<close>

lemma cnf_tops_le: "cnf (P a b c) \<Longrightarrow> \<forall>s \<in> set (tops c). s \<le> a"
proof (induction c arbitrary: a b)
  case Z thus ?case by simp
next
  case (P e f g)
  from P.prems have nlt: "\<not> (P a b Z <o P e f Z)" and cg: "cnf (P e f g)" by auto
  have ea: "e \<le> a" using nlt by auto
  have "\<forall>s \<in> set (tops g). s \<le> e" using P.IH(2)[OF cg] .
  hence "\<forall>s \<in> set (tops g). s \<le> a" using ea by auto
  thus ?case using ea by simp
qed


subsection \<open>Reduction of well-foundedness to within-maxsub-level\<close>

text \<open>Since \<open><o\<close>-descent on \<open>NF\<close> is subscript-monotone (@{thm [source] maxsub_mono_NF'}),
  the maximal-subscript-decreasing part of \<open>Rnf\<close> is well-founded outright; by
  \<open>wf_union_compatible\<close> the whole \<open>Rnf\<close> is well-founded as soon as its
  \<^emph>\<open>equal-maximal-subscript\<close> part is.  This isolates the remaining obligation to a
  single maximal-subscript level (the Buchholz collapsing core).\<close>

theorem wf_Rnf_from_within_level:
  assumes wfE: "wf {(w,x). w <o x \<and> x \<in> NF \<and> w \<in> NF \<and> maxsub w = maxsub x}"
  shows "wf Rnf"
proof -
  let ?D = "{(w,x). w <o x \<and> x \<in> NF \<and> w \<in> NF \<and> maxsub w < maxsub x}"
  let ?E = "{(w,x). w <o x \<and> x \<in> NF \<and> w \<in> NF \<and> maxsub w = maxsub x}"
  have wfD: "wf ?D"
  proof (rule wf_subset)
    show "wf (inv_image less_than maxsub)" by (rule wf_inv_image[OF wf_less_than])
    show "?D \<subseteq> inv_image less_than maxsub" by (auto simp: inv_image_def)
  qed
  have split: "Rnf = ?D \<union> ?E"
    using maxsub_mono_NF' by fastforce
  have comp: "?D O ?E \<subseteq> ?D"
    using olt_trans by auto
  have "wf (?D \<union> ?E)" by (rule wf_union_compatible[OF wfD wfE comp])
  thus ?thesis using split by simp
qed

end
