theory Seqlex
  imports Cnf
begin

definition pairlt :: "nat \<times> nat \<Rightarrow> nat \<times> nat \<Rightarrow> bool" where
  "pairlt p q \<longleftrightarrow>
    fst p < fst q \<or>
      (fst p = fst q \<and> snd p < snd q)"

fun seqlex :: "pairseq \<Rightarrow> pairseq \<Rightarrow> bool" where
  "seqlex [] N = (N \<noteq> [])"
| "seqlex (p # M) [] = False"
| "seqlex (p # M) (q # N) =
    (pairlt p q \<or> (p = q \<and> seqlex M N))"

lemma seqlex_nil_iff [simp]:
  "seqlex [] N \<longleftrightarrow> N \<noteq> []"
  by simp

lemma not_seqlex_nil [simp]:
  "\<not> seqlex (p # M) []"
  by simp

lemma seqlex_cons_cons [simp]:
  "seqlex (p # M) (q # N) \<longleftrightarrow>
    pairlt p q \<or> (p = q \<and> seqlex M N)"
  by simp

lemma seqlex_append_cancel:
  "seqlex (A @ u) (A @ v) \<longleftrightarrow> seqlex u v"
  by (induction A) (auto simp: pairlt_def)

lemma seqlex_prefix:
  assumes "v \<noteq> []"
  shows "seqlex u (u @ v)"
  using assms by (induction u) (auto simp: pairlt_def)

fun steps1 :: "pairseq \<Rightarrow> bool" where
  "steps1 [] = True"
| "steps1 [p] = True"
| "steps1 (p # q # r) =
    (fst q \<le> fst p + 1 \<and> steps1 (q # r))"

lemma steps1_nil [simp]: "steps1 []"
  by simp

lemma steps1_single [simp]: "steps1 [p]"
  by simp

lemma steps1_cons_cons [simp]:
  "steps1 (p # q # r) \<longleftrightarrow>
    fst q \<le> fst p + 1 \<and> steps1 (q # r)"
  by simp

definition getLastD :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a" where
  "getLastD B d = (if B = [] then d else last B)"

definition blockok :: "nat \<Rightarrow> pairseq \<Rightarrow> bool" where
  "blockok d B \<longleftrightarrow>
    (B \<noteq> [] \<longrightarrow> fst (hd B) = d) \<and>
    (\<forall>p\<in>set B. d \<le> fst p) \<and>
    steps1 B"

lemma steps1_iff:
  "steps1 B \<longleftrightarrow>
    (\<forall>j. j + 1 < length B \<longrightarrow>
      fst (nth_default (0, 0) B (j + 1))
        \<le> fst (nth_default (0, 0) B j) + 1)"
proof (induction B rule: steps1.induct)
  case 1
  then show ?case by simp
next
  case (2 p)
  then show ?case by simp
next
  case (3 p q r)
  show ?case
  proof
    assume s: "steps1 (p # q # r)"
    from s have pq: "fst q \<le> fst p + 1"
      and sr: "steps1 (q # r)" by auto
    show "\<forall>j. j + 1 < length (p # q # r) \<longrightarrow>
        fst (nth_default (0, 0) (p # q # r) (j + 1))
          \<le> fst (nth_default (0, 0) (p # q # r) j) + 1"
    proof (intro allI impI)
      fix j
      assume jl: "j + 1 < length (p # q # r)"
      show "fst (nth_default (0, 0) (p # q # r) (j + 1))
          \<le> fst (nth_default (0, 0) (p # q # r) j) + 1"
      proof (cases j)
        case 0
        then show ?thesis using pq by simp
      next
        case (Suc k)
        have "k + 1 < length (q # r)" using jl Suc by simp
        then have "fst
              (nth_default (0, 0) (q # r) (k + 1))
            \<le> fst (nth_default (0, 0) (q # r) k) + 1"
          using "3.IH" sr by blast
        then show ?thesis using Suc by simp
      qed
    qed
  next
    assume h:
      "\<forall>j. j + 1 < length (p # q # r) \<longrightarrow>
        fst (nth_default (0, 0) (p # q # r) (j + 1))
          \<le> fst (nth_default (0, 0) (p # q # r) j) + 1"
    have pq: "fst q \<le> fst p + 1"
      using h[rule_format, of 0] by simp
    have tail:
      "\<forall>j. j + 1 < length (q # r) \<longrightarrow>
        fst (nth_default (0, 0) (q # r) (j + 1))
          \<le> fst (nth_default (0, 0) (q # r) j) + 1"
    proof (intro allI impI)
      fix j
      assume jl: "j + 1 < length (q # r)"
      have "Suc j + 1 < length (p # q # r)"
        using jl by simp
      then have "fst
            (nth_default (0, 0) (p # q # r) (Suc j + 1))
          \<le> fst
              (nth_default (0, 0) (p # q # r) (Suc j)) + 1"
        by (rule h[rule_format])
      then show "fst
            (nth_default (0, 0) (q # r) (j + 1))
          \<le> fst (nth_default (0, 0) (q # r) j) + 1"
        by simp
    qed
    have "steps1 (q # r)" using "3.IH" tail by blast
    then show "steps1 (p # q # r)" using pq by simp
  qed
qed

lemma steps1_tail:
  "steps1 (p # r) \<Longrightarrow> steps1 r"
  by (cases r) auto

lemma steps1_append:
  "steps1 (A @ B) \<longleftrightarrow>
    steps1 A \<and> steps1 B \<and>
      (A = [] \<or> B = [] \<or>
        fst (hd B) \<le> fst (getLastD A (0, 0)) + 1)"
proof (induction A rule: steps1.induct)
  case 1
  then show ?case by simp
next
  case (2 p)
  then show ?case
    by (cases B) (auto simp: getLastD_def)
next
  case (3 p q r)
  then show ?case
    by (auto simp: getLastD_def)
qed

lemma steps1_dropLast:
  assumes "steps1 B"
  shows "steps1 (butlast B)"
proof (cases "B = []")
  case True
  then show ?thesis by simp
next
  case False
  have "butlast B @ [last B] = B"
    using False by simp
  then have "steps1 (butlast B @ [last B])"
    using assms by simp
  then show ?thesis using steps1_append by blast
qed

lemma blockok_dropLast:
  assumes hb: "blockok d B"
  shows "blockok d (butlast B)"
proof -
  from hb have hd:
      "B \<noteq> [] \<longrightarrow> fst (hd B) = d"
    and elems: "\<forall>p\<in>set B. d \<le> fst p"
    and st: "steps1 B"
    unfolding blockok_def by blast+
  have hd':
    "butlast B \<noteq> [] \<longrightarrow>
      fst (hd (butlast B)) = d"
  proof
    assume ne: "butlast B \<noteq> []"
    then obtain x xs where B: "B = x # xs"
      by (cases B) auto
    have xs: "xs \<noteq> []" using ne B by auto
    have "hd (butlast B) = x" using B xs by simp
    moreover have "fst x = d" using hd B by simp
    ultimately show "fst (hd (butlast B)) = d"
      by simp
  qed
  have elems':
    "\<forall>p\<in>set (butlast B). d \<le> fst p"
    using elems by (meson in_set_butlastD)
  have "steps1 (butlast B)"
    by (rule steps1_dropLast[OF st])
  then show ?thesis
    unfolding blockok_def using hd' elems' by blast
qed

lemma blockok_arg:
  assumes hb: "blockok d ((d, y) # r)"
  shows
    "blockok (d + 1)
      (takeWhile (\<lambda>q. d < fst q) r)"
proof -
  from hb have elems:
      "\<forall>p\<in>set ((d, y) # r). d \<le> fst p"
    and st: "steps1 ((d, y) # r)"
    unfolding blockok_def by blast+
  let ?A = "takeWhile (\<lambda>q. d < fst q) r"
  have hdA:
    "?A \<noteq> [] \<longrightarrow> fst (hd ?A) = d + 1"
  proof
    assume ne: "?A \<noteq> []"
    obtain a as where A: "?A = a # as"
      using ne by (cases ?A) auto
    obtain p rs where r: "r = p # rs"
      using ne by (cases r) auto
    have dp: "d < fst p"
    proof (rule ccontr)
      assume "\<not> d < fst p"
      then have "?A = []" using r by simp
      then show False using ne by simp
    qed
    have ap: "a = p"
      using A r dp by simp
    have ub: "fst p \<le> d + 1"
      using st r by simp
    have "fst p = d + 1" using dp ub by simp
    then show "fst (hd ?A) = d + 1"
      using A ap by simp
  qed
  have setA:
    "\<forall>q\<in>set ?A. d + 1 \<le> fst q"
  proof
    fix q
    assume q: "q \<in> set ?A"
    have "d < fst q"
      using set_takeWhileD[OF q] by simp
    then show "d + 1 \<le> fst q" by simp
  qed
  have tail: "steps1 r"
    by (rule steps1_tail[OF st])
  have split:
    "steps1
      (?A @ dropWhile (\<lambda>q. d < fst q) r)"
    using tail by simp
  have stA: "steps1 ?A"
    using steps1_append split by blast
  show ?thesis
    unfolding blockok_def using hdA setA stA by blast
qed

lemma blockok_tail:
  assumes hb: "blockok d ((d, y) # r)"
  shows
    "blockok d
      (dropWhile (\<lambda>q. d < fst q) r)"
proof -
  from hb have elems:
      "\<forall>p\<in>set ((d, y) # r). d \<le> fst p"
    and st: "steps1 ((d, y) # r)"
    unfolding blockok_def by blast+
  let ?T = "dropWhile (\<lambda>q. d < fst q) r"
  have setT: "\<forall>q\<in>set ?T. d \<le> fst q"
    using elems set_dropWhileD by fastforce
  have hdT:
    "?T \<noteq> [] \<longrightarrow> fst (hd ?T) = d"
  proof
    assume ne: "?T \<noteq> []"
    have nlt: "\<not> d < fst (hd ?T)"
      by (rule hd_dropWhile[OF ne])
    have ge: "d \<le> fst (hd ?T)"
      using setT ne hd_in_set by blast
    show "fst (hd ?T) = d" using nlt ge by simp
  qed
  have tail: "steps1 r"
    by (rule steps1_tail[OF st])
  have split:
    "steps1
      (takeWhile (\<lambda>q. d < fst q) r @ ?T)"
    using tail by simp
  have stT: "steps1 ?T"
    using steps1_append split by blast
  show ?thesis
    unfolding blockok_def using hdT setT stT by blast
qed

lemma seqlex_arg_or_tail:
  assumes sl: "seqlex r r'"
  shows
    "(takeWhile (\<lambda>q. d < fst q) r =
        takeWhile (\<lambda>q. d < fst q) r' \<and>
      seqlex
        (dropWhile (\<lambda>q. d < fst q) r)
        (dropWhile (\<lambda>q. d < fst q) r')) \<or>
     (takeWhile (\<lambda>q. d < fst q) r \<noteq>
        takeWhile (\<lambda>q. d < fst q) r' \<and>
      seqlex
        (takeWhile (\<lambda>q. d < fst q) r)
        (takeWhile (\<lambda>q. d < fst q) r'))"
  using sl
proof (induction r arbitrary: r')
  case Nil
  have rne: "r' \<noteq> []" using Nil.prems by simp
  show ?case
  proof (cases
      "takeWhile (\<lambda>q. d < fst q) r' = []")
    case True
    have dw:
      "dropWhile (\<lambda>q. d < fst q) r' = r'"
    proof (cases r')
      case Nil
      then show ?thesis using rne by simp
    next
      case (Cons q t)
      have "\<not> d < fst q"
      proof
        assume "d < fst q"
        then show False using True Cons by simp
      qed
      then show ?thesis using Cons by simp
    qed
    show ?thesis using True dw rne by simp
  next
    case False
    then show ?thesis by simp
  qed
next
  case (Cons p rr)
  show ?case
  proof (cases r')
    case Nil
    then show ?thesis using Cons.prems by simp
  next
    case r'c: (Cons q rr')
    show ?thesis
    proof (cases "p = q")
      case peq: True
      have slr: "seqlex rr rr'"
        using Cons.prems r'c peq
        by (auto simp: pairlt_def)
      show ?thesis
      proof (cases "d < fst p")
        case pos: True
        from Cons.IH[OF slr]
        consider
          (tail)
            "takeWhile (\<lambda>q. d < fst q) rr =
              takeWhile (\<lambda>q. d < fst q) rr'"
            "seqlex
              (dropWhile (\<lambda>q. d < fst q) rr)
              (dropWhile (\<lambda>q. d < fst q) rr')"
        | (arg)
            "takeWhile (\<lambda>q. d < fst q) rr \<noteq>
              takeWhile (\<lambda>q. d < fst q) rr'"
            "seqlex
              (takeWhile (\<lambda>q. d < fst q) rr)
              (takeWhile (\<lambda>q. d < fst q) rr')"
          by blast
        then show ?thesis
        proof cases
          case tail
          then show ?thesis using r'c peq pos by simp
        next
          case arg
          then show ?thesis using r'c peq pos
            by (auto simp: pairlt_def)
        qed
      next
        case neg: False
        then show ?thesis using Cons.prems r'c peq
          by simp
      qed
    next
      case pne: False
      have plt: "pairlt p q"
        using Cons.prems r'c pne by auto
      show ?thesis
      proof (cases "d < fst p")
        case ppos: True
        have qpos: "d < fst q"
          using plt ppos unfolding pairlt_def by auto
        show ?thesis using r'c pne plt ppos qpos
          by auto
      next
        case pnpos: False
        show ?thesis
        proof (cases "d < fst q")
          case qpos: True
          show ?thesis using r'c pnpos qpos by simp
        next
          case qnpos: False
          show ?thesis
            using Cons.prems r'c pnpos qnpos by simp
        qed
      qed
    qed
  qed
qed

lemma seqlex_imp_olt:
  assumes bM: "blockok d M"
    and bN: "blockok d N"
    and sl: "seqlex M N"
  shows "translate M <o translate N"
  using assms
proof (induction "length M + length N"
    arbitrary: d M N rule: less_induct)
  case less
  show ?case
  proof (cases M)
    case Nil
    have "N \<noteq> []" using less.prems(3) Nil by simp
    then obtain q N' where N: "N = q # N'"
      by (cases N) auto
    show ?thesis using Nil N by simp
  next
    case Mc: (Cons p r)
    obtain q r' where N: "N = q # r'"
      using less.prems(3) Mc by (cases N) auto
    have pd: "fst p = d"
      using less.prems(1) Mc
      by (simp add: blockok_def)
    have qd: "fst q = d"
      using less.prems(2) N
      by (simp add: blockok_def)
    obtain y where p: "p = (d, y)"
      using pd by (cases p) auto
    obtain y' where q: "q = (d, y')"
      using qd by (cases q) auto
    show ?thesis
    proof (cases "y = y'")
      case False
      have plt: "pairlt p q"
        using less.prems(3) Mc N p q False
        by (auto simp: pairlt_def)
      have "y < y'" using plt p q
        by (simp add: pairlt_def)
      then show ?thesis using Mc N p q
        by simp
    next
      case True
      have slr: "seqlex r r'"
        using less.prems(3) Mc N p q True
        by (auto simp: pairlt_def)
      have bMr: "blockok d ((d, y) # r)"
        using less.prems(1) Mc p by simp
      have bNr: "blockok d ((d, y) # r')"
        using less.prems(2) N q True by simp
      let ?aM = "takeWhile (\<lambda>x. d < fst x) r"
      let ?tM = "dropWhile (\<lambda>x. d < fst x) r"
      let ?aN = "takeWhile (\<lambda>x. d < fst x) r'"
      let ?tN = "dropWhile (\<lambda>x. d < fst x) r'"
      from seqlex_arg_or_tail[OF slr]
      consider
        (tails) "?aM = ?aN" "seqlex ?tM ?tN"
      | (args) "?aM \<noteq> ?aN" "seqlex ?aM ?aN"
        by blast
      then show ?thesis
      proof cases
        case tails
        have bT: "blockok d ?tM"
          by (rule blockok_tail[OF bMr])
        have bT': "blockok d ?tN"
          by (rule blockok_tail[OF bNr])
        have szM: "length ?tM \<le> length r"
          by (rule length_dropWhile_le)
        have szN: "length ?tN \<le> length r'"
          by (rule length_dropWhile_le)
        have ord: "translate ?tM <o translate ?tN"
        proof (rule less.hyps[
            OF _ bT bT' tails(2)])
          show "length ?tM + length ?tN <
              length M + length N"
            using szM szN Mc N by simp
        qed
        have ae: "translate ?aM = translate ?aN"
          using tails(1) by simp
        show ?thesis using Mc N p q True ord ae
          by simp
      next
        case args
        have bA: "blockok (d + 1) ?aM"
          by (rule blockok_arg[OF bMr])
        have bA': "blockok (d + 1) ?aN"
          by (rule blockok_arg[OF bNr])
        have szM: "length ?aM \<le> length r"
          by (rule length_takeWhile_le)
        have szN: "length ?aN \<le> length r'"
          by (rule length_takeWhile_le)
        have ord: "translate ?aM <o translate ?aN"
        proof (rule less.hyps[
            OF _ bA bA' args(2)])
          show "length ?aM + length ?aN <
              length M + length N"
            using szM szN Mc N by simp
        qed
        show ?thesis using Mc N p q True ord
          by simp
      qed
    qed
  qed
qed

lemma seqlex_total:
  "M = N \<or> seqlex M N \<or> seqlex N M"
proof (induction M arbitrary: N)
  case Nil
  then show ?case by (cases N) auto
next
  case (Cons p M)
  show ?case
  proof (cases N)
    case Nil
    then show ?thesis by simp
  next
    case Nc: (Cons q N')
    show ?thesis
    proof (cases "p = q")
      case True
      then show ?thesis using Cons.IH Nc by auto
    next
      case False
      have "pairlt p q \<or> pairlt q p"
        using False unfolding pairlt_def
        by (cases p; cases q; auto)
      then show ?thesis using Nc by auto
    qed
  qed
qed

lemma olt_iff_seqlex:
  assumes bM: "blockok d M"
    and bN: "blockok d N"
    and ne: "M \<noteq> N"
  shows "translate M <o translate N \<longleftrightarrow>
    seqlex M N"
proof
  assume "seqlex M N"
  then show "translate M <o translate N"
    by (rule seqlex_imp_olt[OF bM bN])
next
  assume o: "translate M <o translate N"
  show "seqlex M N"
  proof (rule ccontr)
    assume "\<not> seqlex M N"
    then have "seqlex N M"
      using seqlex_total[of M N] ne by blast
    then have "translate N <o translate M"
      by (rule seqlex_imp_olt[OF bN bM])
    with o show False
      using olt_trans olt_irrefl by blast
  qed
qed

lemma getLastD_eq_getD:
  "getLastD l d =
    nth_default d l (length l - 1)"
proof (cases "l = []")
  case True
  then show ?thesis
    by (simp add: getLastD_def nth_default_def)
next
  case False
  have idx: "length l - 1 < length l"
    using False by (cases l) auto
  show ?thesis
    using False idx
    by (simp add: getLastD_def nth_default_nth
        last_conv_nth)
qed

lemma getLastD_ne_nil_indep:
  assumes "B \<noteq> []"
  shows "getLastD B d = getLastD B d'"
  using assms by (simp add: getLastD_def)

lemma headI_append_left:
  assumes "A \<noteq> []"
  shows "hd (A @ B) = hd A"
  using assms by (cases A) auto

lemma getLastD_append_right:
  assumes "B \<noteq> []"
  shows "getLastD (A @ B) d = getLastD B d"
  using assms
  by (simp add: getLastD_def last_append)

lemma steps1_flatMap:
  assumes F1: "\<forall>k<n. steps1 (F k)"
    and Fne: "\<forall>k<n. F k \<noteq> []"
    and Fj: "\<forall>k. k + 1 < n \<longrightarrow>
      fst (hd (F (k + 1))) \<le>
        fst (getLastD (F k) (0, 0)) + 1"
  shows
    "steps1 (concat (map F [0..<n])) \<and>
      (0 < n \<longrightarrow>
        concat (map F [0..<n]) \<noteq> [] \<and>
        hd (concat (map F [0..<n])) = hd (F 0) \<and>
        getLastD (concat (map F [0..<n])) (0, 0) =
          getLastD (F (n - 1)) (0, 0))"
  using assms
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc m)
  have IH:
    "steps1 (concat (map F [0..<m])) \<and>
      (0 < m \<longrightarrow>
        concat (map F [0..<m]) \<noteq> [] \<and>
        hd (concat (map F [0..<m])) = hd (F 0) \<and>
        getLastD (concat (map F [0..<m])) (0, 0) =
          getLastD (F (m - 1)) (0, 0))"
    using Suc.IH Suc.prems by simp
  have dec:
    "concat (map F [0..<Suc m]) =
      concat (map F [0..<m]) @ F m"
    by simp
  show ?case
  proof (cases "m = 0")
    case True
    then have e:
      "concat (map F [0..<Suc m]) = F 0"
      by simp
    have s: "steps1 (F 0)"
      using Suc.prems(1) by simp
    have ne: "F 0 \<noteq> []"
      using Suc.prems(2) by simp
    show ?thesis using True e s ne by simp
  next
    case False
    have mpos: "0 < m" using False by simp
    from IH mpos have cs:
        "steps1 (concat (map F [0..<m]))"
      and cne:
        "concat (map F [0..<m]) \<noteq> []"
      and chd:
        "hd (concat (map F [0..<m])) = hd (F 0)"
      and clast:
        "getLastD (concat (map F [0..<m])) (0, 0) =
          getLastD (F (m - 1)) (0, 0)"
      by blast+
    have fmst: "steps1 (F m)"
      using Suc.prems(1) by simp
    have fmne: "F m \<noteq> []"
      using Suc.prems(2) by simp
    have junction:
      "fst (hd (F m)) \<le>
        fst
          (getLastD
            (concat (map F [0..<m])) (0, 0)) + 1"
    proof -
      have "fst (hd (F m)) \<le>
          fst (getLastD (F (m - 1)) (0, 0)) + 1"
        using Suc.prems(3)[rule_format, of "m - 1"]
          mpos by simp
      then show ?thesis using clast by simp
    qed
    have sall:
      "steps1
        (concat (map F [0..<m]) @ F m)"
      using steps1_append cs fmst cne fmne junction
      by blast
    have allne:
      "concat (map F [0..<Suc m]) \<noteq> []"
      using dec cne by auto
    have allhd:
      "hd (concat (map F [0..<Suc m])) = hd (F 0)"
      using dec cne chd headI_append_left by simp
    have alllast:
      "getLastD (concat (map F [0..<Suc m])) (0, 0) =
        getLastD (F m) (0, 0)"
      using dec fmne getLastD_append_right by simp
    show ?thesis
      using dec sall allne allhd alllast by simp
  qed
qed

lemma steps1_diag_range:
  "steps1
    (map (\<lambda>j. (j, j)) [s..<s + m])"
  unfolding steps1_iff
proof (intro allI impI)
  fix j
  assume jl:
    "j + 1 <
      length (map (\<lambda>j. (j, j)) [s..<s + m])"
  have j1: "j + 1 < m" using jl by simp
  have j0: "j < m" using j1 by simp
  show "fst
          (nth_default (0, 0)
            (map (\<lambda>j. (j, j)) [s..<s + m])
            (j + 1))
        \<le> fst
            (nth_default (0, 0)
              (map (\<lambda>j. (j, j)) [s..<s + m]) j) +
          1"
    using j0 j1
    by (simp add: nth_default_nth)
qed

lemma blockok_diagSeq:
  "blockok 0 (diagSeq 0 v)"
proof -
  have ne: "diagSeq 0 v \<noteq> []"
    by (simp add: diagSeq_def)
  have hd: "fst (hd (diagSeq 0 v)) = 0"
    using diagSeq_cons[of 0 v] by simp
  have elems:
    "\<forall>p\<in>set (diagSeq 0 v). 0 \<le> fst p"
    by simp
  have st: "steps1 (diagSeq 0 v)"
    unfolding diagSeq_def
    using steps1_diag_range[of 0 "Suc v"]
    by simp
  show ?thesis
    unfolding blockok_def using ne hd elems st by blast
qed

lemma blockok_oper:
  assumes b: "blockok 0 M"
    and n1: "1 \<le> n"
  shows "blockok 0 (M\<lbrakk>n\<rbrakk>)"
proof (cases "length M - 1 = 0")
  case short: True
  have "M\<lbrakk>n\<rbrakk> = M"
    by (rule oper_eq_self_of_short[OF short])
  then show ?thesis using b by simp
next
  case short: False
  have L1: "1 < length M" using short by simp
  have Mne: "M \<noteq> []" using L1 by auto
  have hPred: "Pred M = butlast M"
    using L1 by (simp add: Pred_def)
  show ?thesis
  proof (cases
      "entry M 0 (length M - 1) = 0 \<and>
       entry M 1 (length M - 1) = 0")
    case zero: True
    have eq: "M\<lbrakk>n\<rbrakk> = Pred M"
      by (rule oper_eq_pred_of_zero[OF short zero])
    show ?thesis
      using blockok_dropLast[OF b] eq hPred by simp
  next
    case nz: False
    show ?thesis
    proof (cases
        "hasParent M (idx1 M (length M - 1))
          (length M - 1)")
      case noParent: False
      have eq: "M\<lbrakk>n\<rbrakk> = Pred M"
        by (rule oper_eq_pred_of_noParent[
          OF short nz noParent])
      show ?thesis
        using blockok_dropLast[OF b] eq hPred by simp
    next
      case hp: True
      define j1 where "j1 = length M - 1"
      define i1 where "i1 = idx1 M j1"
      define j0 where "j0 = parent M i1 j1"
      define D where
        "D =
          (if 0 < i1
           then entry M 0 j1 - entry M 0 j0
           else 0)"
      define F where
        "F =
          (\<lambda>k.
            map
              (\<lambda>j.
                (entry M 0 j + k * D,
                 entry M 1 j))
              [j0..<j1])"
      have hp': "hasParent M i1 j1"
        using hp unfolding i1_def j1_def .
      have np: "nextR M i1 j0 j1"
        unfolding j0_def by (rule parent_nextR[OF hp'])
      have j0lt: "j0 < j1"
        by (rule nextR_index_lt[OF np])
      have j1len: "j1 < length M"
        using short unfolding j1_def by simp
      have bst: "steps1 M"
        using b unfolding blockok_def by blast
      have e0step:
        "\<forall>j. j + 1 < length M \<longrightarrow>
          entry M 0 (j + 1) \<le> entry M 0 j + 1"
      proof (intro allI impI)
        fix j
        assume hj: "j + 1 < length M"
        have h:
          "fst (nth_default (0, 0) M (j + 1))
            \<le> fst (nth_default (0, 0) M j) + 1"
          using steps1_iff[THEN iffD1, OF bst] hj
          by blast
        show "entry M 0 (j + 1) \<le> entry M 0 j + 1"
          using h hj
          by (simp add: entry_def nth_default_nth)
      qed
      have e0j1:
        "entry M 0 j1 \<le>
          entry M 0 (j1 - 1) + 1"
      proof -
        have "j1 - 1 + 1 = j1" using j0lt by simp
        moreover have "j1 - 1 + 1 < length M"
          using j1len j0lt by simp
        ultimately show ?thesis
          using e0step[rule_format, of "j1 - 1"] by simp
      qed
      have e0le:
        "entry M 0 j0 + D \<le>
          entry M 0 (j1 - 1) + 1"
      proof (cases "0 < i1")
        case True
        have i1nz: "i1 \<noteq> 0" using True by simp
        have nl1: "nextrel1 M j0 j1"
          using np i1nz by (simp add: nextR_def)
        have l01: "le0 M j0 j1"
          using nl1 by (simp add: nextrel1_def)
        have le01:
          "entry M 0 j0 \<le> entry M 0 j1"
          by (rule le0_entry0_mono[OF l01])
        have De:
          "D = entry M 0 j1 - entry M 0 j0"
          using True by (simp add: D_def)
        have "entry M 0 j0 + D = entry M 0 j1"
          using De le01 by simp
        then show ?thesis using e0j1 by simp
      next
        case False
        have i1z: "i1 = 0" using False by simp
        have nl0: "nextrel0 M j0 j1"
          using np i1z by (simp add: nextR_def)
        have lt01:
          "entry M 0 j0 < entry M 0 j1"
          by (rule nextrel0_entry0_less[OF nl0])
        have De: "D = 0"
          using False by (simp add: D_def)
        show ?thesis using lt01 e0j1 De by simp
      qed
      have opeq:
        "M\<lbrakk>n\<rbrakk> =
          take j0 M @ concat (map F [0..<n])"
        using oper_bad_unfold[OF short nz hp, of n]
        unfolding F_def D_def j0_def i1_def j1_def
        by simp
      have Fne: "\<forall>k. F k \<noteq> []"
        using j0lt by (simp add: F_def)
      have Fhead:
        "\<forall>k.
          hd (F k) =
            (entry M 0 j0 + k * D,
             entry M 1 j0)"
        using j0lt
        by (simp add: F_def upt_conv_Cons)
      have lenF: "\<forall>k. length (F k) = j1 - j0"
        by (simp add: F_def)
      have FgetD:
        "\<forall>k j. j < j1 - j0 \<longrightarrow>
          nth_default (0, 0) (F k) j =
            (entry M 0 (j0 + j) + k * D,
             entry M 1 (j0 + j))"
      proof (intro allI impI)
        fix k j
        assume hj: "j < j1 - j0"
        have jf: "j < length (F k)"
          using hj lenF by simp
        show "nth_default (0, 0) (F k) j =
            (entry M 0 (j0 + j) + k * D,
             entry M 1 (j0 + j))"
          using hj jf j0lt
          by (simp add: F_def nth_default_nth)
      qed
      have Flast:
        "\<forall>k.
          getLastD (F k) (0, 0) =
            (entry M 0 (j1 - 1) + k * D,
             entry M 1 (j1 - 1))"
      proof
        fix k
        have pos: "0 < j1 - j0" using j0lt by simp
        have ix: "j1 - j0 - 1 < j1 - j0"
          using pos by simp
        have add: "j0 + (j1 - j0 - 1) = j1 - 1"
          using j0lt by simp
        have get:
          "nth_default (0, 0) (F k) (j1 - j0 - 1) =
            (entry M 0 (j0 + (j1 - j0 - 1)) + k * D,
             entry M 1 (j0 + (j1 - j0 - 1)))"
          using FgetD ix by blast
        show "getLastD (F k) (0, 0) =
            (entry M 0 (j1 - 1) + k * D,
             entry M 1 (j1 - 1))"
          using getLastD_eq_getD[of "F k" "(0, 0)"]
            lenF[rule_format, of k]
            get add
          by simp
      qed
      have Fsteps: "\<forall>k. steps1 (F k)"
      proof
        fix k
        show "steps1 (F k)"
          unfolding steps1_iff
        proof (intro allI impI)
          fix j
          assume hj: "j + 1 < length (F k)"
          have hlen: "j + 1 < j1 - j0"
            using hj lenF by simp
          have h0: "j < j1 - j0" using hlen by simp
          have hM:
            "entry M 0 (j0 + j + 1)
              \<le> entry M 0 (j0 + j) + 1"
          proof (rule e0step[rule_format])
            show "j0 + j + 1 < length M"
              using hlen j1len j0lt by simp
          qed
          have add: "j0 + (j + 1) = j0 + j + 1"
            by simp
          have get0:
            "nth_default (0, 0) (F k) j =
              (entry M 0 (j0 + j) + k * D,
               entry M 1 (j0 + j))"
            using FgetD h0 by blast
          have get1:
            "nth_default (0, 0) (F k) (j + 1) =
              (entry M 0 (j0 + (j + 1)) + k * D,
               entry M 1 (j0 + (j + 1)))"
            using FgetD hlen by blast
          show "fst
                (nth_default (0, 0) (F k) (j + 1))
              \<le> fst
                  (nth_default (0, 0) (F k) j) +
                1"
            using get0 get1 hM add
            by simp
        qed
      qed
      have Fjunc:
        "\<forall>k. k + 1 < n \<longrightarrow>
          fst (hd (F (k + 1))) \<le>
            fst (getLastD (F k) (0, 0)) + 1"
      proof (intro allI impI)
        fix k
        assume "k + 1 < n"
        have mult: "(k + 1) * D = k * D + D"
          by simp
        show "fst (hd (F (k + 1))) \<le>
            fst (getLastD (F k) (0, 0)) + 1"
          using Fhead[rule_format, of "k + 1"]
            Flast[rule_format, of k] e0le mult
          by simp
      qed
      have fan:
        "steps1 (concat (map F [0..<n])) \<and>
          (0 < n \<longrightarrow>
            concat (map F [0..<n]) \<noteq> [] \<and>
            hd (concat (map F [0..<n])) = hd (F 0) \<and>
            getLastD (concat (map F [0..<n])) (0, 0) =
              getLastD (F (n - 1)) (0, 0))"
        by (rule steps1_flatMap[
          OF _ _ Fjunc]) (use Fsteps Fne in auto)
      have npos: "0 < n" using n1 by simp
      from fan npos have fsteps:
          "steps1 (concat (map F [0..<n]))"
        and fne: "concat (map F [0..<n]) \<noteq> []"
        and fhd:
          "hd (concat (map F [0..<n])) = hd (F 0)"
        by blast+
      have fhd0:
        "hd (concat (map F [0..<n])) =
          (entry M 0 j0, entry M 1 j0)"
        using fhd Fhead[rule_format, of 0] by simp
      have tk: "steps1 (take j0 M)"
        unfolding steps1_iff
      proof (intro allI impI)
        fix j
        assume hj:
          "j + 1 < length (take j0 M)"
        have hj0: "j + 1 < j0"
          using hj by simp
        have hjM: "j + 1 < length M"
          using hj0 j0lt j1len by simp
        have orig:
          "entry M 0 (j + 1) \<le> entry M 0 j + 1"
          by (rule e0step[rule_format, OF hjM])
        show "fst
              (nth_default (0, 0)
                (take j0 M) (j + 1))
            \<le> fst
                (nth_default (0, 0)
                  (take j0 M) j) + 1"
          using hj hj0 hjM orig
          by (simp add: nth_default_nth nth_take
              entry_def)
      qed
      have junc0:
        "take j0 M = [] \<or>
          concat (map F [0..<n]) = [] \<or>
          fst (hd (concat (map F [0..<n]))) \<le>
            fst (getLastD (take j0 M) (0, 0)) + 1"
      proof (cases "j0 = 0")
        case True
        then show ?thesis by simp
      next
        case False
        have j0len: "j0 \<le> length M"
          using j0lt j1len by simp
        have ix: "j0 - 1 < j0" using False by simp
        have ixM: "j0 - 1 < length M"
          using ix j0len by simp
        have last:
          "getLastD (take j0 M) (0, 0) =
            M ! (j0 - 1)"
          using getLastD_eq_getD[
              of "take j0 M" "(0, 0)"]
            j0len ix False
          by (simp add: nth_default_nth nth_take)
        have hstep:
          "entry M 0 j0 \<le>
            entry M 0 (j0 - 1) + 1"
        proof -
          have add: "j0 - 1 + 1 = j0"
            using False by simp
          have "j0 - 1 + 1 < length M"
            using j0lt j1len False by simp
          then show ?thesis
            using e0step[rule_format, of "j0 - 1"]
              add by simp
        qed
        have fstlast:
          "fst (getLastD (take j0 M) (0, 0)) =
            entry M 0 (j0 - 1)"
          using last ixM
          by (simp add: entry_def)
        show ?thesis
          using fhd0 hstep fstlast by simp
      qed
      have hd0:
        "M\<lbrakk>n\<rbrakk> \<noteq> [] \<longrightarrow>
          fst (hd (M\<lbrakk>n\<rbrakk>)) = 0"
      proof
        assume "M\<lbrakk>n\<rbrakk> \<noteq> []"
        show "fst (hd (M\<lbrakk>n\<rbrakk>)) = 0"
        proof (cases "j0 = 0")
          case True
          have hdo:
            "hd (M\<lbrakk>n\<rbrakk>) =
              (entry M 0 j0, entry M 1 j0)"
            using opeq fne fhd0 True by simp
          have entry0: "entry M 0 0 = fst (hd M)"
            using Mne
            by (cases M)
              (simp_all add: entry_def)
          have bhead: "fst (hd M) = 0"
            using b Mne unfolding blockok_def by blast
          show ?thesis using hdo True entry0 bhead by simp
        next
          case False
          have tne: "take j0 M \<noteq> []"
            using False j0lt j1len Mne by simp
          have "hd (M\<lbrakk>n\<rbrakk>) = hd M"
            using opeq tne headI_append_left by simp
          moreover have "fst (hd M) = 0"
            using b Mne unfolding blockok_def by blast
          ultimately show ?thesis by simp
        qed
      qed
      have allsteps: "steps1 (M\<lbrakk>n\<rbrakk>)"
      proof -
        have "steps1
            (take j0 M @ concat (map F [0..<n]))"
          using tk fsteps junc0
          by (subst steps1_append; blast)
        then show ?thesis using opeq by simp
      qed
      have elems:
        "\<forall>p\<in>set (M\<lbrakk>n\<rbrakk>). 0 \<le> fst p"
        by simp
      show ?thesis
        unfolding blockok_def
        using hd0 elems allsteps by blast
    qed
  qed
qed

lemma blockok_ST_PS:
  assumes "ST_PS M"
  shows "blockok 0 M"
  using assms
proof (induction rule: ST_PS.induct)
  case (diag v)
  show ?case by (rule blockok_diagSeq)
next
  case (oper M n)
  show ?case
    by (rule blockok_oper[OF oper.IH oper.hyps(2)])
qed

lemma olt_ST_iff_seqlex:
  assumes "ST_PS M" "ST_PS N" "M \<noteq> N"
  shows "translate M <o translate N \<longleftrightarrow>
    seqlex M N"
  by (rule olt_iff_seqlex[
      OF blockok_ST_PS[OF assms(1)]
        blockok_ST_PS[OF assms(2)] assms(3)])

end
