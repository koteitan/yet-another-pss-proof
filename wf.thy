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

text \<open>\<open>cnf\<close> is preserved by any prefix \<open>take k\<close> (iterated @{thm [source] cnf_butlast}).\<close>

lemma cnf_take:
  assumes "cnf (translate M)" shows "cnf (translate (take k M))"
proof (induction "length M - k" arbitrary: k)
  case 0
  hence "take k M = M" by simp
  thus ?case using assms by simp
next
  case (Suc d)
  have klt: "k < length M" using Suc.hyps(2) by (cases "k < length M") auto
  have d: "d = length M - Suc k" using Suc.hyps(2) by simp
  have ihk: "cnf (translate (take (Suc k) M))" using Suc.hyps(1)[OF d] .
  have ne: "take (Suc k) M \<noteq> []" using klt by (auto simp: take_eq_Nil)
  have e: "butlast (take (Suc k) M) = take k M"
  proof -
    have "length (take (Suc k) M) = Suc k" using klt by simp
    thus ?thesis by (simp add: butlast_conv_take take_take)
  qed
  show ?case using cnf_butlast[OF ne ihk] e by simp
qed

text \<open>CNF core, the exact-copy (i1 = 0) case: \<open>n\<close> identical copies of a block
  \<open>(v0,w0) # R\<close> translate to a CNF term \<dash> the equal sibling blocks are
  non-increasing by (three-level, proven) irreflexivity of \<open><o\<close>.\<close>

lemma cnf_replicate_block:
  assumes R: "\<forall>x\<in>set R. v0 < fst x" and cR: "cnf (translate R)"
  shows "cnf (translate (concat (replicate n ((v0,w0) # R))))"
proof (induction n)
  case 0 thus ?case by simp
next
  case (Suc m)
  let ?blk = "(v0,w0) # R"
  let ?T = "concat (replicate m ?blk)"
  have hd: "concat (replicate (Suc m) ?blk) = ?blk @ ?T" by simp
  have Tcond: "?T = [] \<or> \<not> v0 < fst (hd ?T)"
    by (cases m) auto
  have tb: "translate (?blk @ ?T) = P w0 (translate R) (translate ?T)"
    by (rule translate_block_append[OF R Tcond])
  show ?case
  proof (cases m)
    case 0
    thus ?thesis using hd tb cR by simp
  next
    case (Suc m')
    have tT: "translate ?T = P w0 (translate R) (translate (concat (replicate m' ?blk)))"
    proof -
      have e: "?T = ?blk @ concat (replicate m' ?blk)" using Suc by simp
      have c: "concat (replicate m' ?blk) = [] \<or> \<not> v0 < fst (hd (concat (replicate m' ?blk)))"
        by (cases m') auto
      show ?thesis using e translate_block_append[OF R c] by simp
    qed
    have cT: "cnf (translate ?T)" using Suc.IH .
    have irr: "\<not> (P w0 (translate R) Z <o P w0 (translate R) Z)" using olt_irrefl by blast
    have "cnf (P w0 (translate R) (translate ?T))" using cR cT tT irr by simp
    thus ?thesis using hd tb by simp
  qed
qed

text \<open>\<^bold>\<open>CNF context congruence.\<close>  If \<open>Z1, Z2\<close> share their leading principal's
  (subscript, argument), \<open>translate Z1 <o translate Z2\<close>, and \<open>translate Z1\<close> is CNF,
  then a common good part \<open>G\<close> preserves CNF: \<open>cnf (translate (G @ Z2))\<close> implies
  \<open>cnf (translate (G @ Z1))\<close>.  The sibling-boundary that \<open>G\<close> creates is preserved
  because the leading argument only shrinks (\<open>arg\<^sub>1 \<le>o arg\<^sub>2\<close>, extracted from the
  decrease lifted by @{thm [source] translate_ctx_cong}) and \<open><o\<close> is transitive
  (three-level, proven).\<close>

lemma cnf_ctx_cong:
  assumes cZ1: "cnf (translate Z1)"
    and decr: "translate Z1 <o translate Z2"
    and ne1: "Z1 \<noteq> []" and ne2: "Z2 \<noteq> []"
    and root: "fst (hd Z1) = fst (hd Z2)"
    and lead: "\<exists>a1 b1 c1 a2 b2 c2. translate Z1 = P a1 b1 c1 \<and> translate Z2 = P a2 b2 c2
                  \<and> P a1 b1 Z \<le>o P a2 b2 Z"
    and r1: "\<forall>x\<in>set (tl Z1). fst (hd Z1) \<le> fst x"
    and r2: "\<forall>x\<in>set (tl Z2). fst (hd Z2) \<le> fst x"
  shows "cnf (translate (G @ Z2)) \<Longrightarrow> cnf (translate (G @ Z1))"
proof (induction G rule: length_induct)
  case (1 G)
  from lead obtain a1 b1 c1 a2 b2 c2
    where lZ1: "translate Z1 = P a1 b1 c1" and lZ2: "translate Z2 = P a2 b2 c2"
      and leadle: "P a1 b1 Z \<le>o P a2 b2 Z"
    by blast
  show ?case
  proof (cases G)
    case Nil thus ?thesis using "1.prems" cZ1 by simp
  next
    case (Cons g G')
    let ?Pg = "\<lambda>q. fst g < fst q"
    have hd2: "fst (hd Z2) = fst (hd Z1)" using root by simp
    show ?thesis
    proof (cases "\<forall>x\<in>set G'. ?Pg x")
      case allG: True
      show ?thesis
      proof (cases "?Pg (hd Z1)")
        case True
        have aZ1: "\<forall>x\<in>set Z1. ?Pg x" using True r1 ne1 by (cases Z1) auto
        have aZ2: "\<forall>x\<in>set Z2. ?Pg x" using True hd2 r2 ne2 by (cases Z2) auto
        have all1: "\<forall>x\<in>set (G' @ Z1). ?Pg x" using allG aZ1 by auto
        have all2: "\<forall>x\<in>set (G' @ Z2). ?Pg x" using allG aZ2 by auto
        have tw1: "takeWhile ?Pg (G' @ Z1) = G' @ Z1" using all1 by (simp add: takeWhile_eq_all_conv)
        have dw1: "dropWhile ?Pg (G' @ Z1) = []" using all1 by (simp add: dropWhile_eq_Nil_conv)
        have tw2: "takeWhile ?Pg (G' @ Z2) = G' @ Z2" using all2 by (simp add: takeWhile_eq_all_conv)
        have dw2: "dropWhile ?Pg (G' @ Z2) = []" using all2 by (simp add: dropWhile_eq_Nil_conv)
        have e1: "translate (G @ Z1) = P (snd g) (translate (G' @ Z1)) Z"
          by (simp only: Cons append_Cons translate.simps(2) tw1 dw1 translate.simps(1))
        have e2: "translate (G @ Z2) = P (snd g) (translate (G' @ Z2)) Z"
          by (simp only: Cons append_Cons translate.simps(2) tw2 dw2 translate.simps(1))
        have "cnf (translate (G' @ Z2))" using "1.prems" e2 by simp
        hence "cnf (translate (G' @ Z1))" using "1.IH" Cons by simp
        thus ?thesis using e1 by simp
      next
        case False
        have twZ1: "takeWhile ?Pg Z1 = []" using False ne1 by (cases Z1) auto
        have dwZ1: "dropWhile ?Pg Z1 = Z1" using False ne1 by (cases Z1) auto
        have twZ2: "takeWhile ?Pg Z2 = []" using False hd2 ne2 by (cases Z2) auto
        have dwZ2: "dropWhile ?Pg Z2 = Z2" using False hd2 ne2 by (cases Z2) auto
        have tw1: "takeWhile ?Pg (G' @ Z1) = G'" using allG twZ1 by (simp add: takeWhile_append2)
        have dw1: "dropWhile ?Pg (G' @ Z1) = Z1" using allG dwZ1 by (simp add: dropWhile_append2)
        have tw2: "takeWhile ?Pg (G' @ Z2) = G'" using allG twZ2 by (simp add: takeWhile_append2)
        have dw2: "dropWhile ?Pg (G' @ Z2) = Z2" using allG dwZ2 by (simp add: dropWhile_append2)
        have e1: "translate (G @ Z1) = P (snd g) (translate G') (P a1 b1 c1)"
          using lZ1 by (simp only: Cons append_Cons translate.simps(2) tw1 dw1)
        have e2: "translate (G @ Z2) = P (snd g) (translate G') (P a2 b2 c2)"
          using lZ2 by (simp only: Cons append_Cons translate.simps(2) tw2 dw2)
        have ctg: "cnf (translate G')" and bnd2: "\<not> (P (snd g) (translate G') Z <o P a2 b2 Z)"
          using "1.prems" e2 by auto
        have bnd1: "\<not> (P (snd g) (translate G') Z <o P a1 b1 Z)"
        proof
          assume "P (snd g) (translate G') Z <o P a1 b1 Z"
          from olt_ole_trans[OF this leadle] show False using bnd2 by simp
        qed
        have "cnf (P a1 b1 c1)" using cZ1 lZ1 by simp
        thus ?thesis using e1 ctg bnd1 by simp
      qed
    next
      case notallG: False
      then obtain x where x: "x \<in> set G'" and nx: "\<not> ?Pg x" by blast
      have tw1: "takeWhile ?Pg (G' @ Z1) = takeWhile ?Pg G'" using x nx by (simp add: takeWhile_append1)
      have dw1: "dropWhile ?Pg (G' @ Z1) = dropWhile ?Pg G' @ Z1" using x nx by (simp add: dropWhile_append1)
      have tw2: "takeWhile ?Pg (G' @ Z2) = takeWhile ?Pg G'" using x nx by (simp add: takeWhile_append1)
      have dw2: "dropWhile ?Pg (G' @ Z2) = dropWhile ?Pg G' @ Z2" using x nx by (simp add: dropWhile_append1)
      let ?D = "dropWhile ?Pg G'"
      have e1: "translate (G @ Z1) = P (snd g) (translate (takeWhile ?Pg G')) (translate (?D @ Z1))"
        by (simp only: Cons append_Cons translate.simps(2) tw1 dw1)
      have e2: "translate (G @ Z2) = P (snd g) (translate (takeWhile ?Pg G')) (translate (?D @ Z2))"
        by (simp only: Cons append_Cons translate.simps(2) tw2 dw2)
      have Dne: "?D \<noteq> []" using x nx by (auto simp: dropWhile_eq_Nil_conv)
      \<comment> \<open>both tails are principals with the same leading subscript\<close>
      obtain e arg1 t1 where p1: "translate (?D @ Z1) = P e arg1 t1"
        using Dne ne1 by (cases "?D @ Z1") auto
      obtain e' arg2 t2 where p2: "translate (?D @ Z2) = P e' arg2 t2"
        using Dne ne2 by (cases "?D @ Z2") auto
      have lenD: "length ?D < length G" using Cons by (simp add: le_imp_less_Suc length_dropWhile_le)
      have decrD: "translate (?D @ Z1) <o translate (?D @ Z2)"
        by (rule translate_ctx_cong[OF decr ne1 ne2 root r1 r2])
      have ee: "e = e'"
        using p1 p2 lead_translate[of "?D @ Z1"] lead_translate[of "?D @ Z2"] Dne
        by (cases ?D) auto
      have argle: "arg1 <o arg2 \<or> arg1 = arg2" using p1 p2 decrD ee by (auto split: if_splits)
      \<comment> \<open>recurse for CNF of the new tail\<close>
      have ctw: "cnf (translate (takeWhile ?Pg G'))" using "1.prems" e2 p2 by simp
      have "cnf (translate (?D @ Z2))" using "1.prems" e2 p2 by simp
      hence cD1: "cnf (translate (?D @ Z1))" using "1.IH" lenD by blast
      \<comment> \<open>the boundary \<open>\<not> (... <o P e arg\<^sub>1 Z)\<close> transfers from \<open>arg\<^sub>2\<close>\<close>
      have bnd2: "\<not> (P (snd g) (translate (takeWhile ?Pg G')) Z <o P e' arg2 Z)"
        using "1.prems" e2 p2 by simp
      have bnd1: "\<not> (P (snd g) (translate (takeWhile ?Pg G')) Z <o P e arg1 Z)"
      proof
        assume "P (snd g) (translate (takeWhile ?Pg G')) Z <o P e arg1 Z"
        hence "snd g < e \<or> (snd g = e \<and> translate (takeWhile ?Pg G') <o arg1)" by auto
        thus False
        proof
          assume "snd g < e"
          hence "P (snd g) (translate (takeWhile ?Pg G')) Z <o P e' arg2 Z" using ee by simp
          thus False using bnd2 by simp
        next
          assume A: "snd g = e \<and> translate (takeWhile ?Pg G') <o arg1"
          hence "translate (takeWhile ?Pg G') <o arg2" using argle olt_ole_trans by blast
          hence "P (snd g) (translate (takeWhile ?Pg G')) Z <o P e' arg2 Z" using A ee by simp
          thus False using bnd2 by simp
        qed
      qed
      show ?thesis using e1 p1 cD1 ctw bnd1 by simp
    qed
  qed
qed

text \<open>CNF is inherited by a re-opening tail: if \<open>translate (G @ Z)\<close> is CNF and \<open>Z\<close>
  is a single well-formed block (its non-leading pairs all lie above its root),
  then \<open>translate Z\<close> is CNF.\<close>

lemma cnf_tail:
  assumes "T \<noteq> []" and rT: "\<forall>x\<in>set (tl T). fst (hd T) \<le> fst x"
  shows "cnf (translate (G @ T)) \<Longrightarrow> cnf (translate T)"
proof (induction G rule: length_induct)
  case (1 G)
  show ?case
  proof (cases G)
    case Nil thus ?thesis using "1.prems" by simp
  next
    case (Cons g G')
    let ?Pg = "\<lambda>q. fst g < fst q"
    show ?thesis
    proof (cases "\<forall>x\<in>set G'. ?Pg x")
      case allG: True
      show ?thesis
      proof (cases "?Pg (hd T)")
        case True
        have aT: "\<forall>x\<in>set T. ?Pg x" using True rT \<open>T \<noteq> []\<close> by (cases T) auto
        have all: "\<forall>x\<in>set (G' @ T). ?Pg x" using allG aT by auto
        have tw: "takeWhile ?Pg (G' @ T) = G' @ T" using all by (simp add: takeWhile_eq_all_conv)
        have dw: "dropWhile ?Pg (G' @ T) = []" using all by (simp add: dropWhile_eq_Nil_conv)
        have e: "translate (G @ T) = P (snd g) (translate (G' @ T)) Z"
          by (simp only: Cons append_Cons translate.simps(2) tw dw translate.simps(1))
        have cgt: "cnf (translate (G' @ T))" using "1.prems" e by simp
        have "length G' < length G" using Cons by simp
        thus ?thesis using "1.IH" cgt by blast
      next
        case False
        have twT: "takeWhile ?Pg T = []" using False \<open>T \<noteq> []\<close> by (cases T) auto
        have dwT: "dropWhile ?Pg T = T" using False \<open>T \<noteq> []\<close> by (cases T) auto
        have tw: "takeWhile ?Pg (G' @ T) = G'" using allG twT by (simp add: takeWhile_append2)
        have dw: "dropWhile ?Pg (G' @ T) = T" using allG dwT by (simp add: dropWhile_append2)
        have e: "translate (G @ T) = P (snd g) (translate G') (translate T)"
          by (simp only: Cons append_Cons translate.simps(2) tw dw)
        have nz: "translate T \<noteq> Z" using \<open>T \<noteq> []\<close> by (cases T) auto
        thus ?thesis using "1.prems" e by (cases "translate T") auto
      qed
    next
      case notallG: False
      then obtain x where x: "x \<in> set G'" and nx: "\<not> ?Pg x" by blast
      have tw: "takeWhile ?Pg (G' @ T) = takeWhile ?Pg G'" using x nx by (simp add: takeWhile_append1)
      have dw: "dropWhile ?Pg (G' @ T) = dropWhile ?Pg G' @ T" using x nx by (simp add: dropWhile_append1)
      let ?D = "dropWhile ?Pg G'"
      have e: "translate (G @ T) = P (snd g) (translate (takeWhile ?Pg G')) (translate (?D @ T))"
        by (simp only: Cons append_Cons translate.simps(2) tw dw)
      have Dne: "?D \<noteq> []" using x nx by (auto simp: dropWhile_eq_Nil_conv)
      have nz: "translate (?D @ T) \<noteq> Z" using Dne by (cases "?D @ T") auto
      hence "cnf (translate (?D @ T))" using "1.prems" e by (cases "translate (?D @ T)") auto
      moreover have "length ?D < length G" using Cons by (simp add: le_imp_less_Suc length_dropWhile_le)
      ultimately show ?thesis using "1.IH" by blast
    qed
  qed
qed

text \<open>\<^bold>\<open>CNF preservation, the exact-copy (i1 = 0) oper case (abstract).\<close>  Replacing a
  block \<open>(v0,w0)#R\<close> followed by the dropped descendant \<open>lp\<close> (which nests, \<open>v0 < fst lp\<close>)
  by \<open>n\<close> exact copies of the block preserves CNF.  Assembled from @{thm [source]
  cnf_tail} (extract the block's CNF), @{thm [source] cnf_butlast}, @{thm [source]
  cnf_replicate_block} (the copies are CNF), and @{thm [source] cnf_ctx_cong} (the
  good part \<open>G\<close> preserves it; the leading argument shrinks since \<open>lp\<close> is dropped).\<close>

lemma cnf_oper_i1eq0:
  assumes R: "\<forall>x\<in>set R. v0 < fst x"
    and lpv: "v0 < fst lp"
    and n1: "1 \<le> n"
    and cM: "cnf (translate (G @ ((v0,w0) # R) @ [lp]))"
  shows "cnf (translate (G @ concat (replicate n ((v0,w0) # R))))"
proof -
  let ?blk = "(v0,w0) # R"
  obtain m where m: "n = Suc m" using n1 by (cases n) auto
  \<comment> \<open>structures of the two tails\<close>
  have RlpV: "\<forall>x\<in>set (R @ [lp]). fst (v0,w0) < fst x" using R lpv by auto
  have tZ2: "translate (?blk @ [lp]) = P w0 (translate (R @ [lp])) Z"
    using translate_single_tree[OF RlpV] by simp
  have Tcond: "concat (replicate m ?blk) = [] \<or> \<not> v0 < fst (hd (concat (replicate m ?blk)))"
    by (cases m) auto
  have tZ1: "translate (concat (replicate n ?blk))
             = P w0 (translate R) (translate (concat (replicate m ?blk)))"
    using m translate_block_append[OF R Tcond] by simp
  \<comment> \<open>extract CNF of the block body from CNF of \<open>M\<close>\<close>
  have rT: "\<forall>x\<in>set (tl (?blk @ [lp])). fst (hd (?blk @ [lp])) \<le> fst x" using R lpv by auto
  have "cnf (translate (G @ (?blk @ [lp])))" using cM by simp
  hence "cnf (translate (?blk @ [lp]))" using cnf_tail[OF _ rT] by blast
  hence "cnf (translate (R @ [lp]))" using tZ2 by simp
  hence cR: "cnf (translate R)" using cnf_butlast[of "R @ [lp]"] by simp
  have cZ1: "cnf (translate (concat (replicate n ?blk)))" using cnf_replicate_block[OF R cR] .
  \<comment> \<open>lead (\<open>b1 \<le>o b2\<close>) and the strict decrease\<close>
  have RltRlp: "translate R <o translate (R @ [lp])" by (rule translate_snoc_increase)
  have ple: "P w0 (translate R) Z \<le>o P w0 (translate (R @ [lp])) Z"
    using olt_P_b[OF RltRlp, of w0 Z Z] by simp
  have lead: "\<exists>a1 b1 c1 a2 b2 c2. translate (concat (replicate n ?blk)) = P a1 b1 c1
                 \<and> translate (?blk @ [lp]) = P a2 b2 c2 \<and> P a1 b1 Z \<le>o P a2 b2 Z"
    using tZ1 tZ2 ple by blast
  have decr: "translate (concat (replicate n ?blk)) <o translate (?blk @ [lp])"
    using tZ1 tZ2 RltRlp by (simp add: olt_P_b)
  \<comment> \<open>side conditions for the context congruence\<close>
  have blkge: "\<forall>x\<in>set ?blk. v0 \<le> fst x" using R by auto
  have sub: "set (concat (replicate n ?blk)) \<subseteq> set ?blk" using m by (auto simp: set_concat)
  have allge: "\<forall>x\<in>set (concat (replicate n ?blk)). v0 \<le> fst x" using blkge sub by blast
  have ne1: "concat (replicate n ?blk) \<noteq> []" using m by simp
  have ne2: "?blk @ [lp] \<noteq> []" by simp
  have root: "fst (hd (concat (replicate n ?blk))) = fst (hd (?blk @ [lp]))" using m by simp
  have hdv: "fst (hd (concat (replicate n ?blk))) = v0" using m by simp
  have r1: "\<forall>x\<in>set (tl (concat (replicate n ?blk))). fst (hd (concat (replicate n ?blk))) \<le> fst x"
    using allge hdv ne1 by (metis list.set_sel(2))
  have r2: "\<forall>x\<in>set (tl (?blk @ [lp])). fst (hd (?blk @ [lp])) \<le> fst x" using rT by simp
  have imp: "cnf (translate (G @ (?blk @ [lp]))) \<Longrightarrow> cnf (translate (G @ concat (replicate n ?blk)))"
    by (rule cnf_ctx_cong[OF cZ1 decr ne1 ne2 root lead r1 r2])
  have "cnf (translate (G @ (?blk @ [lp])))" using cM by simp
  thus ?thesis using imp by simp
qed

subsection \<open>CNF preservation, the ascending-copies (\<open>i\<^sub>1 = 1\<close>) oper case\<close>

text \<open>The \<open>i\<^sub>1 = 1\<close> bad step replaces the block \<open>blk = (v\<^sub>0,w\<^sub>0)#R\<close> followed by the
  dropped descendant \<open>lp\<close> by \<open>n\<close> \<^emph>\<open>ascending\<close> copies of \<open>blk\<close>: the \<open>k\<close>-th copy is
  \<open>blk\<close> with every row-0 entry shifted up by \<open>k * d\<^sub>0\<close> (\<open>d\<^sub>0 > 0\<close>).  We package the
  copy list as \<open>copies d\<^sub>0 blk n\<close>.\<close>

definition shiftr0 :: "nat \<Rightarrow> (nat \<times> nat) list \<Rightarrow> (nat \<times> nat) list" where
  "shiftr0 d = map (\<lambda>p. (fst p + d, snd p))"

definition copies :: "nat \<Rightarrow> (nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "copies d blk n = concat (map (\<lambda>k. shiftr0 (k * d) blk) [0..<n])"

lemma shiftr0_0 [simp]: "shiftr0 0 M = M"
  by (simp add: shiftr0_def)

lemma shiftr0_Nil [simp]: "shiftr0 d [] = []"
  by (simp add: shiftr0_def)

lemma shiftr0_eq_Nil [simp]: "shiftr0 d M = [] \<longleftrightarrow> M = []"
  by (simp add: shiftr0_def)

lemma shiftr0_shiftr0: "shiftr0 d (shiftr0 e M) = shiftr0 (d + e) M"
  by (simp add: shiftr0_def comp_def add.commute add.left_commute)

lemma shiftr0_concat: "shiftr0 d (concat L) = concat (map (shiftr0 d) L)"
  by (simp add: shiftr0_def map_concat)

lemma translate_shiftr0 [simp]: "translate (shiftr0 d M) = translate M"
  by (simp add: shiftr0_def translate_shift)

lemma hd_shiftr0: "M \<noteq> [] \<Longrightarrow> hd (shiftr0 d M) = (fst (hd M) + d, snd (hd M))"
  by (cases M) (auto simp: shiftr0_def)

lemma copies_0 [simp]: "copies d blk 0 = []"
  by (simp add: copies_def)

lemma copies_1 [simp]: "copies d blk 1 = blk"
  by (simp add: copies_def)

lemma copies_Suc_front: "copies d blk (Suc n) = blk @ shiftr0 d (copies d blk n)"
proof -
  have tail: "shiftr0 d (copies d blk n) = concat (map (\<lambda>k. shiftr0 (k * d) blk) [1..<Suc n])"
  proof -
    have "shiftr0 d (copies d blk n) = concat (map (\<lambda>k. shiftr0 (d + k * d) blk) [0..<n])"
      by (simp add: copies_def shiftr0_concat o_def shiftr0_shiftr0)
    also have "\<dots> = concat (map (\<lambda>k. shiftr0 (k * d) blk) (map Suc [0..<n]))"
      by (simp add: o_def mult_Suc)
    also have "\<dots> = concat (map (\<lambda>k. shiftr0 (k * d) blk) [1..<Suc n])"
      by (simp add: map_Suc_upt)
    finally show ?thesis .
  qed
  have e0: "[0..<Suc n] = 0 # [1..<Suc n]" by (simp add: upt_conv_Cons)
  have A: "copies d blk (Suc n) = blk @ concat (map (\<lambda>k. shiftr0 (k * d) blk) [1..<Suc n])"
    by (simp only: copies_def e0 list.map concat.simps mult_zero_left shiftr0_0)
  thus ?thesis by (simp only: tail)
qed

lemma copies_nonempty: "blk \<noteq> [] \<Longrightarrow> 1 \<le> n \<Longrightarrow> copies d blk n \<noteq> []"
  by (cases n) (auto simp: copies_Suc_front)

lemma hd_copies: "blk \<noteq> [] \<Longrightarrow> 1 \<le> n \<Longrightarrow> hd (copies d blk n) = hd blk"
  by (cases n) (auto simp: copies_Suc_front)

lemma copies_v0_le:
  assumes blk: "blk = (v0, w0) # R" and Rle: "\<forall>x\<in>set R. v0 \<le> fst x"
  shows "\<forall>x\<in>set (copies d blk n). v0 \<le> fst x"
proof
  fix x assume "x \<in> set (copies d blk n)"
  then obtain k where "x \<in> set (shiftr0 (k * d) blk)"
    by (auto simp: copies_def)
  then obtain p where p: "p \<in> set blk" and xe: "x = (fst p + k * d, snd p)"
    by (auto simp: shiftr0_def)
  have "v0 \<le> fst p" using p blk Rle by auto
  thus "v0 \<le> fst x" using xe by simp
qed

lemma copies_tl_gt:
  assumes R: "\<forall>x\<in>set R. v0 < fst x" and d: "0 < d" and n1: "1 \<le> n"
  shows "\<forall>x\<in>set (tl (copies d ((v0, w0) # R) n)). v0 < fst x"
proof -
  obtain m where m: "n = Suc m" using n1 by (cases n) auto
  have e: "copies d ((v0, w0) # R) n = (v0, w0) # (R @ shiftr0 d (copies d ((v0, w0) # R) m))"
    using m copies_Suc_front[of d "(v0, w0) # R" m] by simp
  have "\<forall>x\<in>set (R @ shiftr0 d (copies d ((v0, w0) # R) m)). v0 < fst x"
  proof
    fix x assume "x \<in> set (R @ shiftr0 d (copies d ((v0, w0) # R) m))"
    then consider "x \<in> set R" | "x \<in> set (shiftr0 d (copies d ((v0, w0) # R) m))" by auto
    thus "v0 < fst x"
    proof cases
      case 1 thus ?thesis using R by blast
    next
      case 2
      then obtain p where p: "p \<in> set (copies d ((v0, w0) # R) m)" and xe: "x = (fst p + d, snd p)"
        by (auto simp: shiftr0_def)
      have Rle: "\<forall>x\<in>set R. v0 \<le> fst x" using R by (auto intro: less_imp_le)
      have "v0 \<le> fst p" using copies_v0_le[OF refl Rle] p by blast
      thus ?thesis using xe d by simp
    qed
  qed
  thus ?thesis using e by simp
qed

text \<open>The core induction: \<open>n\<close> ascending copies of a CNF block translate to a CNF
  term.  Each new copy is grafted by @{thm [source] cnf_ctx_cong} against the
  dropped tail \<open>[lp]\<close>; its leading subscript \<open>w\<^sub>0\<close> is strictly below \<open>snd lp\<close>
  (the row-1 increase of the \<open>i\<^sub>1 = 1\<close> parent), so the leading principal does not
  increase and the boundary is preserved.  The recursion uses the self-similarity
  \<open>copies (Suc n) = blk @ shiftr0 d\<^sub>0 (copies n)\<close> and shift-invariance of
  @{const translate}.\<close>

lemma cnf_copies:
  assumes R: "\<forall>x\<in>set R. v0 < fst x"
    and d0pos: "0 < d0"
    and w0lt: "w0 < snd lp"
    and lphd: "fst lp = v0 + d0"
    and cBlp: "cnf (translate (((v0, w0) # R) @ [lp]))"
  shows "cnf (translate (copies d0 ((v0, w0) # R) n))"
proof (induction n)
  case 0 show ?case by simp
next
  case (Suc n)
  let ?blk = "(v0, w0) # R"
  have blkne: "?blk \<noteq> []" by simp
  show ?case
  proof (cases n)
    case 0
    have "cnf (translate ?blk)" using cnf_butlast[of "?blk @ [lp]"] cBlp by simp
    thus ?thesis using 0 by (simp add: copies_Suc_front)
  next
    case (Suc m)
    have n1: "1 \<le> n" using Suc by simp
    have cpne: "copies d0 ?blk n \<noteq> []" using blkne n1 by (rule copies_nonempty)
    have hdcp: "hd (copies d0 ?blk n) = (v0, w0)" using blkne n1 hd_copies[of ?blk n d0] by simp
    have cpcons: "copies d0 ?blk n = (v0, w0) # tl (copies d0 ?blk n)"
      using cpne hdcp by (cases "copies d0 ?blk n") auto
    have tlgt: "\<forall>x\<in>set (tl (copies d0 ?blk n)). v0 < fst x"
      using copies_tl_gt[OF R d0pos n1] by simp
    let ?Z1 = "shiftr0 d0 (copies d0 ?blk n)"
    have Z1ne: "?Z1 \<noteq> []" using cpne by simp
    \<comment> \<open>\<open>translate ?Z1 = translate (copies n)\<close>, of shape \<open>P w\<^sub>0 _ _\<close>\<close>
    have tZ1eq: "translate ?Z1 = translate (copies d0 ?blk n)" by simp
    have st1: "translate (copies d0 ?blk n) = P w0 (translate (tl (copies d0 ?blk n))) Z"
    proof -
      have "translate ((v0, w0) # tl (copies d0 ?blk n))
            = P w0 (translate (tl (copies d0 ?blk n))) Z"
        using translate_single_tree[of "tl (copies d0 ?blk n)" "(v0, w0)"] tlgt by simp
      thus ?thesis using cpcons by simp
    qed
    have cZ1: "cnf (translate ?Z1)" using Suc.IH tZ1eq by simp
    have st1Z1: "translate ?Z1 = P w0 (translate (tl (copies d0 ?blk n))) Z"
      using tZ1eq st1 by simp
    have tlp: "translate [lp] = P (snd lp) Z Z" by simp
    have decr: "translate ?Z1 <o translate [lp]"
    proof -
      have "P w0 (translate (tl (copies d0 ?blk n))) Z <o P (snd lp) Z Z" using w0lt by simp
      thus ?thesis using st1Z1 tlp by simp
    qed
    have leadle: "\<exists>a1 b1 c1 a2 b2 c2. translate ?Z1 = P a1 b1 c1
                    \<and> translate [lp] = P a2 b2 c2 \<and> P a1 b1 Z \<le>o P a2 b2 Z"
    proof -
      have "P w0 (translate (tl (copies d0 ?blk n))) Z \<le>o P (snd lp) Z Z"
        using w0lt by simp
      thus ?thesis using st1Z1 tlp by blast
    qed
    have lpne: "[lp] \<noteq> []" by simp
    have root: "fst (hd ?Z1) = fst (hd [lp])"
    proof -
      have "hd ?Z1 = (v0 + d0, w0)" using cpne hdcp hd_shiftr0[of "copies d0 ?blk n" d0] by simp
      thus ?thesis using lphd by simp
    qed
    have r1: "\<forall>x\<in>set (tl ?Z1). fst (hd ?Z1) \<le> fst x"
    proof -
      have hdf: "fst (hd ?Z1) = v0 + d0"
        using cpne hdcp hd_shiftr0[of "copies d0 ?blk n" d0] by simp
      have Rle: "\<forall>x\<in>set R. v0 \<le> fst x" using R by (auto intro: less_imp_le)
      have allge: "\<forall>x\<in>set (copies d0 ?blk n). v0 \<le> fst x"
        using copies_v0_le[OF refl Rle] by simp
      have "\<forall>x\<in>set ?Z1. v0 + d0 \<le> fst x"
      proof
        fix x assume "x \<in> set ?Z1"
        then obtain p where p: "p \<in> set (copies d0 ?blk n)" and xe: "x = (fst p + d0, snd p)"
          by (auto simp: shiftr0_def)
        have "v0 \<le> fst p" using allge p by blast
        thus "v0 + d0 \<le> fst x" using xe by simp
      qed
      hence "\<forall>x\<in>set (tl ?Z1). v0 + d0 \<le> fst x" using Z1ne by (metis list.set_sel(2))
      thus ?thesis using hdf by simp
    qed
    have r2: "\<forall>x\<in>set (tl [lp]). fst (hd [lp]) \<le> fst x" by simp
    have imp: "cnf (translate (?blk @ [lp])) \<Longrightarrow> cnf (translate (?blk @ ?Z1))"
      by (rule cnf_ctx_cong[OF cZ1 decr Z1ne lpne root leadle r1 r2])
    have eq: "copies d0 ?blk (Suc n) = ?blk @ ?Z1"
      using copies_Suc_front[of d0 ?blk n] by simp
    show ?thesis unfolding eq by (rule imp[OF cBlp])
  qed
qed

text \<open>\<^bold>\<open>CNF preservation, the ascending-copies (\<open>i\<^sub>1 = 1\<close>) oper case.\<close>  Like
  @{thm [source] cnf_oper_i1eq0} but for the genuinely ascending copies; the
  strict decrease \<open>translate (copies d\<^sub>0 blk n) <o translate (blk @ [lp])\<close>
  (the bad-step core, derived internally from @{thm [source] core_i1}) lifts the
  block's CNF through the good part \<open>G\<close> via @{thm [source] cnf_ctx_cong}, while
  @{thm [source] cnf_copies} furnishes CNF of the copies themselves.\<close>

lemma cnf_oper_i1eq1:
  assumes R: "\<forall>x\<in>set R. v0 < fst x"
    and d0pos: "0 < d0"
    and w0lt: "w0 < snd lp"
    and lphd: "fst lp = v0 + d0"
    and n1: "1 \<le> n"
    and cM: "cnf (translate (G @ ((v0, w0) # R) @ [lp]))"
  shows "cnf (translate (G @ copies d0 ((v0, w0) # R) n))"
proof -
  let ?blk = "(v0, w0) # R"
  have blkne: "?blk \<noteq> []" by simp
  \<comment> \<open>the bad-step core decrease, derived from @{thm [source] core_i1}\<close>
  have decr: "translate (copies d0 ?blk n) <o translate (?blk @ [lp])"
  proof (cases "n = 1")
    case True
    hence e: "copies d0 ?blk n = ?blk" by (simp add: copies_Suc_front)
    show ?thesis unfolding e by (rule translate_snoc_increase)
  next
    case False
    obtain m where m: "n = Suc m" using n1 by (cases n) auto
    have m1: "1 \<le> m" using False m by (cases m) auto
    let ?C = "shiftr0 d0 (copies d0 ?blk m)"
    have cpm_ne: "copies d0 ?blk m \<noteq> []" using blkne m1 by (rule copies_nonempty)
    have CP: "?C \<noteq> []" using cpm_ne by simp
    have hdcpm: "hd (copies d0 ?blk m) = (v0, w0)" using blkne m1 hd_copies[of ?blk m d0] by simp
    have hdC: "hd ?C = (v0 + d0, w0)"
      using cpm_ne hdcpm hd_shiftr0[of "copies d0 ?blk m" d0] by simp
    have Cge: "\<forall>x\<in>set (tl ?C). fst (hd ?C) \<le> fst x"
    proof -
      have Rle: "\<forall>x\<in>set R. v0 \<le> fst x" using R by (auto intro: less_imp_le)
      have allge: "\<forall>x\<in>set (copies d0 ?blk m). v0 \<le> fst x" using copies_v0_le[OF refl Rle] by simp
      have "\<forall>x\<in>set ?C. v0 + d0 \<le> fst x"
      proof
        fix x assume "x \<in> set ?C"
        then obtain p where p: "p \<in> set (copies d0 ?blk m)" and xe: "x = (fst p + d0, snd p)"
          by (auto simp: shiftr0_def)
        have "v0 \<le> fst p" using allge p by blast
        thus "v0 + d0 \<le> fst x" using xe by simp
      qed
      hence "\<forall>x\<in>set (tl ?C). v0 + d0 \<le> fst x" using CP by (metis list.set_sel(2))
      thus ?thesis using hdC by simp
    qed
    have Croot: "fst (hd ?C) = fst lp" using hdC lphd by simp
    have lpv: "v0 < fst lp" using lphd d0pos by simp
    have lead_lt: "snd (hd ?C) < snd lp" using hdC w0lt by simp
    have "translate (?blk @ ?C) <o translate (?blk @ [lp])"
      by (rule core_i1[OF R CP Cge Croot lpv lead_lt])
    moreover have "copies d0 ?blk n = ?blk @ ?C"
      using m copies_Suc_front[of d0 ?blk m] by simp
    ultimately show ?thesis by simp
  qed
  have cpne: "copies d0 ?blk n \<noteq> []" using blkne n1 by (rule copies_nonempty)
  have hdcp: "hd (copies d0 ?blk n) = (v0, w0)" using blkne n1 hd_copies[of ?blk n d0] by simp
  have cpcons: "copies d0 ?blk n = (v0, w0) # tl (copies d0 ?blk n)"
    using cpne hdcp by (cases "copies d0 ?blk n") auto
  have tlgt: "\<forall>x\<in>set (tl (copies d0 ?blk n)). v0 < fst x"
    using copies_tl_gt[OF R d0pos n1] by simp
  have Rlp_gt: "\<forall>x\<in>set (R @ [lp]). v0 < fst x" using R lphd d0pos by auto
  \<comment> \<open>both sides are single trees with leading subscript \<open>w\<^sub>0\<close>\<close>
  have st1: "translate (copies d0 ?blk n) = P w0 (translate (tl (copies d0 ?blk n))) Z"
  proof -
    have "translate ((v0, w0) # tl (copies d0 ?blk n))
          = P w0 (translate (tl (copies d0 ?blk n))) Z"
      using translate_single_tree[of "tl (copies d0 ?blk n)" "(v0, w0)"] tlgt by simp
    thus ?thesis using cpcons by simp
  qed
  have st2: "translate (?blk @ [lp]) = P w0 (translate (R @ [lp])) Z"
    using translate_single_tree[of "R @ [lp]" "(v0, w0)"] Rlp_gt by simp
  \<comment> \<open>side conditions for the outer context congruence\<close>
  have ne2: "?blk @ [lp] \<noteq> []" by simp
  have r2: "\<forall>x\<in>set (tl (?blk @ [lp])). fst (hd (?blk @ [lp])) \<le> fst x"
    using Rlp_gt by (auto intro: less_imp_le)
  have cBlp: "cnf (translate (?blk @ [lp]))"
    using cnf_tail[OF ne2 r2] cM by simp
  have cCopies: "cnf (translate (copies d0 ?blk n))"
    by (rule cnf_copies[OF R d0pos w0lt lphd cBlp])
  have leadle: "\<exists>a1 b1 c1 a2 b2 c2. translate (copies d0 ?blk n) = P a1 b1 c1
                  \<and> translate (?blk @ [lp]) = P a2 b2 c2 \<and> P a1 b1 Z \<le>o P a2 b2 Z"
  proof -
    have "P w0 (translate (tl (copies d0 ?blk n))) Z \<le>o P w0 (translate (R @ [lp])) Z"
      using decr st1 st2 by simp
    thus ?thesis using st1 st2 by blast
  qed
  have root: "fst (hd (copies d0 ?blk n)) = fst (hd (?blk @ [lp]))" using hdcp by simp
  have r1: "\<forall>x\<in>set (tl (copies d0 ?blk n)). fst (hd (copies d0 ?blk n)) \<le> fst x"
    using tlgt hdcp by (auto intro: less_imp_le)
  have imp: "cnf (translate (G @ (?blk @ [lp]))) \<Longrightarrow> cnf (translate (G @ copies d0 ?blk n))"
    by (rule cnf_ctx_cong[OF cCopies decr cpne ne2 root leadle r1 r2])
  have "cnf (translate (G @ (?blk @ [lp])))" using cM by simp
  thus ?thesis using imp by simp
qed

lemma copies_replicate: "copies 0 blk n = concat (replicate n blk)"
proof -
  have "copies 0 blk n = concat (map (\<lambda>k. blk) [0..<n])" by (simp add: copies_def)
  also have "map (\<lambda>k. blk) [0..<n] = replicate n blk" by (simp add: map_replicate_const)
  finally show ?thesis .
qed

text \<open>\<^bold>\<open>CNF is preserved by one expansion step.\<close>  The degenerate (\<open>Pred\<close>) branches
  drop the last pair (@{thm [source] cnf_butlast}) or leave \<open>M\<close> unchanged; the
  genuine (bad) branch is discharged by @{thm [source] cnf_oper_i1eq0} (exact
  copies, \<open>d\<^sub>0 = 0\<close>) or @{thm [source] cnf_oper_i1eq1} (ascending copies, \<open>d\<^sub>0 > 0\<close>),
  fed by the decomposition @{thm [source] oper_bad_blocks}.\<close>

lemma cnf_oper:
  assumes n: "1 \<le> n" and cM: "cnf (translate M)"
  shows "cnf (translate (oper M n))"
proof (cases "Lng M - 1 = 0")
  case True
  hence leq: "oper M n = M" by (simp add: oper_def Let_def)
  show ?thesis using cM by (simp only: leq)
next
  case L: False
  hence L1: "1 < Lng M" by simp
  have Mne: "M \<noteq> []" using L1 by (cases M) auto
  show ?thesis
  proof (cases "entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0")
    case z: True
    have leq: "oper M n = butlast M" using z L1 by (simp add: oper_def Let_def Pred_def)
    show ?thesis using cnf_butlast[OF Mne cM] by (simp only: leq)
  next
    case nz: False
    show ?thesis
    proof (cases "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)")
      case False
      hence leq: "oper M n = butlast M" using L1 nz by (simp add: oper_def Let_def Pred_def)
      show ?thesis using cnf_butlast[OF Mne cM] by (simp only: leq)
    next
      case hp: True
      obtain G v0 w0 R d0 lp where
        Meq: "M = G @ ((v0, w0) # R) @ [lp]"
        and Mneq: "oper M n
              = G @ concat (map (\<lambda>k. map (\<lambda>p. (fst p + k * d0, snd p)) ((v0, w0) # R)) [0..<n])"
        and R: "\<forall>x\<in>set R. v0 < fst x" and lpv: "v0 < fst lp"
        and disj: "d0 = 0 \<or> (0 < d0 \<and> w0 < snd lp \<and> fst lp = v0 + d0)"
        by (rule oper_bad_blocks[OF L1 nz hp n])
      have raweq: "concat (map (\<lambda>k. map (\<lambda>p. (fst p + k * d0, snd p)) ((v0, w0) # R)) [0..<n])
                   = copies d0 ((v0, w0) # R) n"
        by (simp add: copies_def shiftr0_def)
      have cM': "cnf (translate (G @ ((v0, w0) # R) @ [lp]))" using cM by (simp only: Meq)
      show ?thesis
      proof (cases "d0 = 0")
        case d0z: True
        have leq: "oper M n = G @ copies 0 ((v0, w0) # R) n"
          using Mneq raweq d0z by simp
        have "cnf (translate (G @ concat (replicate n ((v0, w0) # R))))"
          by (rule cnf_oper_i1eq0[OF R lpv n cM'])
        hence "cnf (translate (G @ copies 0 ((v0, w0) # R) n))" by (simp only: copies_replicate)
        thus ?thesis by (simp only: leq)
      next
        case d0nz: False
        from disj d0nz have d0pos: "0 < d0" and w0lt: "w0 < snd lp" and lphd: "fst lp = v0 + d0"
          by simp_all
        have leq: "oper M n = G @ copies d0 ((v0, w0) # R) n"
          using Mneq raweq by simp
        have "cnf (translate (G @ copies d0 ((v0, w0) # R) n))"
          by (rule cnf_oper_i1eq1[OF R d0pos w0lt lphd n cM'])
        thus ?thesis by (simp only: leq)
      qed
    qed
  qed
qed

text \<open>\<^bold>\<open>Every standard-form sequence translates to a CNF term.\<close>  Induction over the
  generation of @{const ST_PS}: the diagonal seeds are CNF (@{thm [source] cnf_diag})
  and each expansion step preserves CNF (@{thm [source] cnf_oper}).\<close>

lemma cnf_ST_PS: "M \<in> ST_PS \<Longrightarrow> cnf (translate M)"
proof (induction rule: ST_PS.induct)
  case (diag v) show ?case by (simp add: cnf_diag)
next
  case (oper M n) show ?case using cnf_oper[OF oper.hyps(2) oper.IH] .
qed

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
