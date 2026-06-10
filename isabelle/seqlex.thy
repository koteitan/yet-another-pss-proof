theory seqlex
  imports wf
begin

text \<open>\<^bold>\<open>The translation is an order isomorphism onto the column-lex order.\<close>

  On pair sequences whose row-0 values start at the block depth and step up by at
  most one (true of all standard forms and hereditarily of their sub-blocks), the
  pure-lex order \<open><o\<close> on translations coincides with the \<^emph>\<open>column lexicographic\<close>
  order on the sequences themselves.  This recasts the residual well-foundedness
  obligation in BMS-native terms: no infinite column-lex descending chain of
  standard forms.  (Empirically calibrated: 162006 pairs, 0 mismatches.)\<close>

subsection \<open>The column-lex order\<close>

definition pairlt :: "nat \<times> nat \<Rightarrow> nat \<times> nat \<Rightarrow> bool" where
  "pairlt p q \<longleftrightarrow> fst p < fst q \<or> (fst p = fst q \<and> snd p < snd q)"

fun seqlex :: "pairseq \<Rightarrow> pairseq \<Rightarrow> bool" where
  "seqlex [] N = (N \<noteq> [])"
| "seqlex (p # M) [] = False"
| "seqlex (p # M) (q # N) = (pairlt p q \<or> (p = q \<and> seqlex M N))"

lemma seqlex_append_cancel: "seqlex (A @ u) (A @ v) \<longleftrightarrow> seqlex u v"
  by (induction A) (auto simp: pairlt_def)

lemma seqlex_prefix: "v \<noteq> [] \<Longrightarrow> seqlex u (u @ v)"
  by (induction u) (auto simp: pairlt_def)

subsection \<open>The block discipline\<close>

text \<open>\<open>blockok d B\<close>: \<open>B\<close> is a depth-\<open>d\<close> block — every row-0 value is \<open>\<ge> d\<close>, the head
  (if any) sits exactly at \<open>d\<close>, and row 0 increases by at most one at each step.\<close>

definition blockok :: "nat \<Rightarrow> pairseq \<Rightarrow> bool" where
  "blockok d B \<longleftrightarrow>
     (B \<noteq> [] \<longrightarrow> fst (hd B) = d)
     \<and> (\<forall>p \<in> set B. d \<le> fst p)
     \<and> (\<forall>j. Suc j < length B \<longrightarrow> fst (B ! Suc j) \<le> Suc (fst (B ! j)))"

lemma blockok_Nil [simp]: "blockok d []"
  by (simp add: blockok_def)

lemma stepprops_tl:
  assumes "\<forall>x \<in> set (p # rr). d \<le> fst x"
    and "\<forall>j. Suc j < length (p # rr) \<longrightarrow> fst ((p # rr) ! Suc j) \<le> Suc (fst ((p # rr) ! j))"
  shows "(\<forall>x \<in> set rr. d \<le> fst x) \<and>
         (\<forall>j. Suc j < length rr \<longrightarrow> fst (rr ! Suc j) \<le> Suc (fst (rr ! j)))"
proof (intro conjI ballI allI impI)
  show "\<And>x. x \<in> set rr \<Longrightarrow> d \<le> fst x" using assms(1) by simp
next
  fix j assume j: "Suc j < length rr"
  have "Suc (Suc j) < length (p # rr)" using j by simp
  hence "fst ((p # rr) ! Suc (Suc j)) \<le> Suc (fst ((p # rr) ! Suc j))" using assms(2) by blast
  thus "fst (rr ! Suc j) \<le> Suc (fst (rr ! j))" by simp
qed

subsection \<open>Splitting a block at its head\<close>

text \<open>For a nonempty depth-\<open>d\<close> block \<open>(d,y) # r\<close>, the argument part
  \<open>takeWhile (\<lambda>q. d < fst q) r\<close> is a depth-\<open>Suc d\<close> block and the tail part
  \<open>dropWhile (\<lambda>q. d < fst q) r\<close> is a depth-\<open>d\<close> block.\<close>

lemma blockok_tl: "blockok d (p # r) \<Longrightarrow>
  (\<forall>q \<in> set r. d \<le> fst q) \<and> (\<forall>j. Suc j < length r \<longrightarrow> fst (r ! Suc j) \<le> Suc (fst (r ! j)))"
  unfolding blockok_def using stepprops_tl by fast

lemma blockok_arg:
  assumes "blockok d ((d, y) # r)"
  shows "blockok (Suc d) (takeWhile (\<lambda>q. d < fst q) r)"
proof -
  have rprops: "(\<forall>q \<in> set r. d \<le> fst q) \<and>
                (\<forall>j. Suc j < length r \<longrightarrow> fst (r ! Suc j) \<le> Suc (fst (r ! j)))"
    using blockok_tl[OF assms] .
  let ?A = "takeWhile (\<lambda>q. d < fst q) r"
  have setA: "\<forall>q \<in> set ?A. Suc d \<le> fst q"
    using set_takeWhileD by fastforce
  have hdA: "?A \<noteq> [] \<longrightarrow> fst (hd ?A) = Suc d"
  proof
    assume ne: "?A \<noteq> []"
    hence rne: "r \<noteq> []" by auto
    have h1: "hd ?A = hd r" using ne by (cases r) auto
    have dlt: "d < fst (hd r)" using ne hd_in_set takeWhile_eq_Nil_iff by (metis h1)
    have "Suc 0 < length ((d,y) # r)" using rne by simp
    hence "fst (((d,y) # r) ! Suc 0) \<le> Suc (fst (((d,y) # r) ! 0))"
      using assms unfolding blockok_def by blast
    hence ub: "fst (r ! 0) \<le> Suc d" by simp
    show "fst (hd ?A) = Suc d"
      using h1 rne dlt ub by (simp add: hd_conv_nth)
  qed
  have stepsA: "\<forall>j. Suc j < length ?A \<longrightarrow> fst (?A ! Suc j) \<le> Suc (fst (?A ! j))"
  proof (intro allI impI)
    fix j assume j: "Suc j < length ?A"
    have "?A ! Suc j = r ! Suc j" "?A ! j = r ! j"
      using j by (auto simp: takeWhile_nth)
    moreover have "Suc j < length r"
      using j length_takeWhile_le[of "\<lambda>q. d < fst q" r] by linarith
    ultimately show "fst (?A ! Suc j) \<le> Suc (fst (?A ! j))" using rprops by auto
  qed
  show ?thesis unfolding blockok_def using hdA setA stepsA by blast
qed

lemma blockok_tail:
  assumes "blockok d ((d, y) # r)"
  shows "blockok d (dropWhile (\<lambda>q. d < fst q) r)"
proof -
  have rprops: "(\<forall>q \<in> set r. d \<le> fst q) \<and>
                (\<forall>j. Suc j < length r \<longrightarrow> fst (r ! Suc j) \<le> Suc (fst (r ! j)))"
    using blockok_tl[OF assms] .
  let ?T = "dropWhile (\<lambda>q. d < fst q) r"
  have setT: "\<forall>q \<in> set ?T. d \<le> fst q" using rprops set_dropWhileD by fastforce
  have hdT: "?T \<noteq> [] \<longrightarrow> fst (hd ?T) = d"
  proof
    assume ne: "?T \<noteq> []"
    have "\<not> d < fst (hd ?T)" using hd_dropWhile[OF ne] .
    moreover have "d \<le> fst (hd ?T)" using setT ne hd_in_set by blast
    ultimately show "fst (hd ?T) = d" by simp
  qed
  have stepsT: "\<forall>j. Suc j < length ?T \<longrightarrow> fst (?T ! Suc j) \<le> Suc (fst (?T ! j))"
  proof (intro allI impI)
    fix j assume j: "Suc j < length ?T"
    have len: "length (takeWhile (\<lambda>q. d < fst q) r) + length ?T = length r"
      by (metis length_append takeWhile_dropWhile_id)
    define k where "k = length (takeWhile (\<lambda>q. d < fst q) r)"
    have "?T ! j = r ! (k + j)" "?T ! Suc j = r ! (k + Suc j)"
      unfolding k_def using j by (auto simp: dropWhile_nth add.commute)
    moreover have "k + Suc j < length r" unfolding k_def using j len k_def by linarith
    ultimately show "fst (?T ! Suc j) \<le> Suc (fst (?T ! j))" using rprops by auto
  qed
  show ?thesis unfolding blockok_def using hdT setT stepsT by blast
qed

text \<open>Every element of a depth-\<open>d\<close> block's argument zone exceeds \<open>d\<close>; the tail zone
  starts exactly at \<open>d\<close>.  Hence comparing two blocks with equal heads, the first
  column difference falls coherently into the argument or tail zones.\<close>

lemma seqlex_arg_or_tail:
  assumes bM: "blockok d ((d,y) # r)" and bN: "blockok d ((d,y) # r')"
    and sl: "seqlex r r'"
  shows "(takeWhile (\<lambda>q. d < fst q) r = takeWhile (\<lambda>q. d < fst q) r' \<and>
            seqlex (dropWhile (\<lambda>q. d < fst q) r) (dropWhile (\<lambda>q. d < fst q) r'))
         \<or> (takeWhile (\<lambda>q. d < fst q) r \<noteq> takeWhile (\<lambda>q. d < fst q) r' \<and>
            seqlex (takeWhile (\<lambda>q. d < fst q) r) (takeWhile (\<lambda>q. d < fst q) r'))"
  using blockok_tl[OF bM] blockok_tl[OF bN] sl
proof (induction r arbitrary: r')
  case Nil
  hence "r' \<noteq> []" by simp
  thus ?case
  proof (cases "takeWhile (\<lambda>q. d < fst q) r' = []")
    case True
    have "dropWhile (\<lambda>q. d < fst q) r' = r'"
      using True by (metis dropWhile_eq_self_iff takeWhile_eq_Nil_iff)
    thus ?thesis using True \<open>r' \<noteq> []\<close> by simp
  next
    case False
    thus ?thesis by simp
  qed
next
  case (Cons p rr)
  show ?case
  proof (cases r')
    case Nil thus ?thesis using Cons.prems(3) by simp
  next
    case Cons2: (Cons q rr')
    note r' = Cons2
    show ?thesis
    proof (cases "p = q")
      case True
      have slr: "seqlex rr rr'" using Cons.prems(3) r' True by (cases "pairlt p q") (auto simp: pairlt_def)
      have prM: "(\<forall>x \<in> set rr. d \<le> fst x) \<and> (\<forall>j. Suc j < length rr \<longrightarrow> fst (rr ! Suc j) \<le> Suc (fst (rr ! j)))"
        using Cons.prems(1) stepprops_tl by blast
      have prN: "(\<forall>x \<in> set rr'. d \<le> fst x) \<and> (\<forall>j. Suc j < length rr' \<longrightarrow> fst (rr' ! Suc j) \<le> Suc (fst (rr' ! j)))"
        using Cons.prems(2) r' stepprops_tl by blast
      show ?thesis
      proof (cases "d < fst p")
        case True2: True
        have IH: "(takeWhile (\<lambda>q. d < fst q) rr = takeWhile (\<lambda>q. d < fst q) rr' \<and>
                     seqlex (dropWhile (\<lambda>q. d < fst q) rr) (dropWhile (\<lambda>q. d < fst q) rr'))
                  \<or> (takeWhile (\<lambda>q. d < fst q) rr \<noteq> takeWhile (\<lambda>q. d < fst q) rr' \<and>
                     seqlex (takeWhile (\<lambda>q. d < fst q) rr) (takeWhile (\<lambda>q. d < fst q) rr'))"
          using Cons.IH prM prN slr by blast
        show ?thesis using IH True True2 r' by (auto simp: pairlt_def)
      next
        case False2: False
        \<comment> \<open>both heads in the tail zone: argument zones empty on both sides\<close>
        have "takeWhile (\<lambda>q. d < fst q) (p # rr) = []" using False2 by simp
        moreover have "takeWhile (\<lambda>q. d < fst q) r' = []" using False2 True r' by simp
        moreover have "dropWhile (\<lambda>q. d < fst q) (p # rr) = p # rr" using False2 by simp
        moreover have "dropWhile (\<lambda>q. d < fst q) r' = r'" using False2 True r' by simp
        ultimately show ?thesis using Cons.prems(3) r' by simp
      qed
    next
      case False
      have plt: "pairlt p q" using Cons.prems(3) r' False by auto
      show ?thesis
      proof (cases "d < fst p")
        case True2: True
        have "d < fst q"
        proof -
          have "fst p \<le> fst q \<or> (fst p = fst q)" using plt by (auto simp: pairlt_def)
          thus ?thesis using True2 by auto
        qed
        hence tw: "takeWhile (\<lambda>x. d < fst x) (p # rr) = p # takeWhile (\<lambda>x. d < fst x) rr"
              and tw': "takeWhile (\<lambda>x. d < fst x) r' = q # takeWhile (\<lambda>x. d < fst x) rr'"
          using True2 r' by auto
        have "seqlex (takeWhile (\<lambda>x. d < fst x) (p # rr)) (takeWhile (\<lambda>x. d < fst x) r')"
          using tw tw' plt by simp
        moreover have "takeWhile (\<lambda>x. d < fst x) (p # rr) \<noteq> takeWhile (\<lambda>x. d < fst x) r'"
          using tw tw' False by simp
        ultimately show ?thesis by blast
      next
        case False2: False
        \<comment> \<open>head of \<open>r\<close> is in the tail zone; head of \<open>r'\<close> with \<open>pairlt p q\<close>:
            if \<open>q\<close> is in the argument zone, \<open>fst p = d < fst q\<close> contradicts nothing —
            then \<open>argM = []\<close> is a proper prefix of \<open>argN\<close>\<close>
        show ?thesis
        proof (cases "d < fst q")
          case True3: True
          have "takeWhile (\<lambda>x. d < fst x) (p # rr) = []" using False2 by simp
          moreover have "takeWhile (\<lambda>x. d < fst x) r' \<noteq> []" using True3 r' by simp
          ultimately show ?thesis by simp
        next
          case False3: False
          have "takeWhile (\<lambda>x. d < fst x) (p # rr) = []" using False2 by simp
          moreover have "takeWhile (\<lambda>x. d < fst x) r' = []" using False3 r' by simp
          moreover have "dropWhile (\<lambda>x. d < fst x) (p # rr) = p # rr" using False2 by simp
          moreover have "dropWhile (\<lambda>x. d < fst x) r' = r'" using False3 r' by simp
          ultimately show ?thesis using Cons.prems(3) r' by simp
        qed
      qed
    qed
  qed
qed

subsection \<open>The order isomorphism\<close>

theorem seqlex_imp_olt:
  "blockok d M \<Longrightarrow> blockok d N \<Longrightarrow> seqlex M N \<Longrightarrow> translate M <o translate N"
proof (induction "length M + length N" arbitrary: d M N rule: less_induct)
  case less
  show ?case
  proof (cases M)
    case Nil
    have "N \<noteq> []" using less.prems(3) Nil by simp
    then obtain q N' where "N = q # N'" by (cases N) auto
    thus ?thesis using Nil by simp
  next
    case (Cons p r)
    obtain q r' where N: "N = q # r'" using less.prems(3) Cons by (cases N) auto
    have pd: "fst p = d" using less.prems(1) Cons by (simp add: blockok_def)
    have qd: "fst q = d" using less.prems(2) N by (simp add: blockok_def)
    obtain y where p: "p = (d, y)" using pd by (cases p) auto
    obtain y' where q: "q = (d, y')" using qd by (cases q) auto
    show ?thesis
    proof (cases "y = y'")
      case False
      have "pairlt p q" using less.prems(3) Cons N p q False by (auto simp: pairlt_def)
      hence yy: "y < y'" using p q by (simp add: pairlt_def)
      show ?thesis using Cons N p q yy by simp
    next
      case True
      have slr: "seqlex r r'"
        using less.prems(3) Cons N p q True by (auto simp: pairlt_def)
      have bM: "blockok d ((d,y) # r)" using less.prems(1) Cons p by simp
      have bN: "blockok d ((d,y) # r')" using less.prems(2) N q True by simp
      let ?aM = "takeWhile (\<lambda>x. d < fst x) r" and ?tM = "dropWhile (\<lambda>x. d < fst x) r"
      let ?aN = "takeWhile (\<lambda>x. d < fst x) r'" and ?tN = "dropWhile (\<lambda>x. d < fst x) r'"
      from seqlex_arg_or_tail[OF bM bN slr]
      consider (tails) "?aM = ?aN" "seqlex ?tM ?tN"
        | (args) "?aM \<noteq> ?aN" "seqlex ?aM ?aN" by blast
      thus ?thesis
      proof cases
        case tails
        have bT: "blockok d ?tM" by (rule blockok_tail[OF bM])
        have bT': "blockok d ?tN" by (rule blockok_tail[OF bN])
        have szM: "length ?tM \<le> length r" by (simp add: length_dropWhile_le)
        have szN: "length ?tN \<le> length r'" by (simp add: length_dropWhile_le)
        have "translate ?tM <o translate ?tN"
          by (rule less.hyps[OF _ bT bT' tails(2)]) (use szM szN Cons N in simp)
        moreover have "translate ?aM = translate ?aN" using tails(1) by simp
        ultimately show ?thesis using Cons N p q True by simp
      next
        case args
        have bA: "blockok (Suc d) ?aM" by (rule blockok_arg[OF bM])
        have bA': "blockok (Suc d) ?aN" by (rule blockok_arg[OF bN])
        have szM: "length ?aM \<le> length r" by (simp add: length_takeWhile_le)
        have szN: "length ?aN \<le> length r'" by (simp add: length_takeWhile_le)
        have "translate ?aM <o translate ?aN"
          by (rule less.hyps[OF _ bA bA' args(2)]) (use szM szN Cons N in simp)
        thus ?thesis using Cons N p q True by simp
      qed
    qed
  qed
qed

text \<open>With totality on both sides, the implication upgrades to an isomorphism.\<close>

lemma seqlex_total: "M = N \<or> seqlex M N \<or> seqlex N M"
proof (induction M arbitrary: N)
  case Nil thus ?case by (cases N) auto
next
  case (Cons p M)
  show ?case
  proof (cases N)
    case Nil thus ?thesis by simp
  next
    case Cons2: (Cons q N')
    show ?thesis
    proof (cases "p = q")
      case True thus ?thesis using Cons.IH Cons2 by auto
    next
      case False
      hence "pairlt p q \<or> pairlt q p"
        unfolding pairlt_def by (cases p; cases q) auto
      thus ?thesis using Cons2 by auto
    qed
  qed
qed

subsection \<open>Adjacent-step predicate and its composition laws\<close>

fun steps1 :: "pairseq \<Rightarrow> bool" where
  "steps1 [] = True"
| "steps1 [p] = True"
| "steps1 (p # q # r) = (fst q \<le> Suc (fst p) \<and> steps1 (q # r))"

lemma steps1_iff:
  "steps1 B \<longleftrightarrow> (\<forall>j. Suc j < length B \<longrightarrow> fst (B ! Suc j) \<le> Suc (fst (B ! j)))"
proof (induction B rule: steps1.induct)
  case 1 thus ?case by simp
next
  case (2 p) thus ?case by simp
next
  case (3 p q r)
  show ?case
  proof
    assume "steps1 (p # q # r)"
    hence h: "fst q \<le> Suc (fst p)" and t: "steps1 (q # r)" by auto
    show "\<forall>j. Suc j < length (p # q # r) \<longrightarrow>
            fst ((p # q # r) ! Suc j) \<le> Suc (fst ((p # q # r) ! j))"
    proof (intro allI impI)
      fix j assume jl: "Suc j < length (p # q # r)"
      show "fst ((p # q # r) ! Suc j) \<le> Suc (fst ((p # q # r) ! j))"
      proof (cases j)
        case 0 thus ?thesis using h by simp
      next
        case (Suc j')
        have "Suc j' < length (q # r)" using jl Suc by simp
        thus ?thesis using t "3.IH" Suc by simp
      qed
    qed
  next
    assume A: "\<forall>j. Suc j < length (p # q # r) \<longrightarrow>
                 fst ((p # q # r) ! Suc j) \<le> Suc (fst ((p # q # r) ! j))"
    have "Suc 0 < length (p # q # r)" by simp
    hence "fst ((p # q # r) ! Suc 0) \<le> Suc (fst ((p # q # r) ! 0))" using A by blast
    hence h: "fst q \<le> Suc (fst p)" by simp
    have "\<forall>j. Suc j < length (q # r) \<longrightarrow> fst ((q # r) ! Suc j) \<le> Suc (fst ((q # r) ! j))"
    proof (intro allI impI)
      fix j assume "Suc j < length (q # r)"
      hence "Suc (Suc j) < length (p # q # r)" by simp
      hence "fst ((p # q # r) ! Suc (Suc j)) \<le> Suc (fst ((p # q # r) ! Suc j))" using A by blast
      thus "fst ((q # r) ! Suc j) \<le> Suc (fst ((q # r) ! j))" by simp
    qed
    hence "steps1 (q # r)" using "3.IH" by blast
    thus "steps1 (p # q # r)" using h by simp
  qed
qed

lemma steps1_append:
  "steps1 (A @ B) \<longleftrightarrow>
     steps1 A \<and> steps1 B \<and> (A = [] \<or> B = [] \<or> fst (hd B) \<le> Suc (fst (last A)))"
proof (induction A rule: steps1.induct)
  case 1 thus ?case by simp
next
  case (2 p) thus ?case by (cases B) auto
next
  case (3 p q r) show ?case using "3.IH" by auto
qed

lemma steps1_butlast: "steps1 B \<Longrightarrow> steps1 (butlast B)"
proof -
  assume s: "steps1 B"
  have "B = butlast B @ (if B = [] then [] else [last B])" by simp
  thus "steps1 (butlast B)" using s steps1_append by metis
qed

lemma blockok_via_steps1:
  "blockok d B \<longleftrightarrow> (B \<noteq> [] \<longrightarrow> fst (hd B) = d) \<and> (\<forall>p \<in> set B. d \<le> fst p) \<and> steps1 B"
  by (simp add: blockok_def steps1_iff)

lemma blockok_butlast: "blockok d B \<Longrightarrow> blockok d (butlast B)"
proof -
  assume b: "blockok d B"
  have hd': "butlast B \<noteq> [] \<longrightarrow> fst (hd (butlast B)) = d"
  proof
    assume ne: "butlast B \<noteq> []"
    obtain x xs where B: "B = x # xs" using ne by (cases B) auto
    have xsne: "xs \<noteq> []" using ne B by auto
    have "hd (butlast B) = x" using B xsne by simp
    thus "fst (hd (butlast B)) = d" using b B unfolding blockok_def by simp
  qed
  have set': "\<forall>p \<in> set (butlast B). d \<le> fst p"
    using b unfolding blockok_def by (meson in_set_butlastD)
  have st': "steps1 (butlast B)"
    using b blockok_via_steps1 steps1_butlast by blast
  show ?thesis using hd' set' st' blockok_via_steps1 by blast
qed

lemma steps1_concat_map:
  assumes F1: "\<And>k. k < n \<Longrightarrow> steps1 (F k)"
    and Fne: "\<And>k. k < n \<Longrightarrow> F k \<noteq> []"
    and Fj: "\<And>k. Suc k < n \<Longrightarrow> fst (hd (F (Suc k))) \<le> Suc (fst (last (F k)))"
  shows "steps1 (concat (map F [0..<n]))
         \<and> (0 < n \<longrightarrow> concat (map F [0..<n]) \<noteq> []
              \<and> hd (concat (map F [0..<n])) = hd (F 0)
              \<and> last (concat (map F [0..<n])) = last (F (n - 1)))"
  using assms
proof (induction n)
  case 0 thus ?case by simp
next
  case (Suc n)
  have IH: "steps1 (concat (map F [0..<n]))
            \<and> (0 < n \<longrightarrow> concat (map F [0..<n]) \<noteq> []
                 \<and> hd (concat (map F [0..<n])) = hd (F 0)
                 \<and> last (concat (map F [0..<n])) = last (F (n - 1)))"
    using Suc.IH Suc.prems by simp
  have dec: "concat (map F [0..<Suc n]) = concat (map F [0..<n]) @ F n" by simp
  show ?case
  proof (cases "n = 0")
    case True
    thus ?thesis using Suc.prems(1)[of 0] Suc.prems(2)[of 0] dec by simp
  next
    case False
    hence npos: "0 < n" by simp
    have cne: "concat (map F [0..<n]) \<noteq> []" using IH npos by blast
    have lc: "last (concat (map F [0..<n])) = last (F (n - 1))" using IH npos by blast
    have junction: "fst (hd (F n)) \<le> Suc (fst (last (F (n - 1))))"
      using Suc.prems(3)[of "n - 1"] npos by simp
    have s: "steps1 (concat (map F [0..<n]) @ F n)"
      using steps1_append IH Suc.prems(1)[of n] junction lc cne by auto
    have hne: "F n \<noteq> []" using Suc.prems(2)[of n] by simp
    have lst: "last (concat (map F [0..<Suc n])) = last (F n)"
      using dec hne by (simp add: last_append)
    have hd': "hd (concat (map F [0..<Suc n])) = hd (F 0)"
    proof -
      obtain x xs where c0: "concat (map F [0..<n]) = x # xs"
        using cne by (cases "concat (map F [0..<n])") auto
      have "concat (map F [0..<Suc n]) = (x # xs) @ F n" by (simp only: dec c0)
      hence h1: "hd (concat (map F [0..<Suc n])) = x" by simp
      have h2: "hd (concat (map F [0..<n])) = x" using c0 by simp
      show ?thesis using h1 h2 IH npos by simp
    qed
    show ?thesis using s dec lst hd' cne by simp
  qed
qed

subsection \<open>Standard forms obey the block discipline\<close>

lemma parent_nextR:
  assumes "hasParent M i j1" shows "nextR M i (parent M i j1) j1"
  using assms by (metis hasParent_def parent_def theI')

lemma blockok_diagSeq: "blockok 0 (diagSeq 0 v)"
proof -
  have len: "length (diagSeq 0 v) = Suc v" by (simp add: diagSeq_def)
  have nth: "\<And>j. j < Suc v \<Longrightarrow> diagSeq 0 v ! j = (j, j)"
    by (auto simp: diagSeq_def nth_append)
  have ne: "diagSeq 0 v \<noteq> []" using len by auto
  have hd0: "fst (hd (diagSeq 0 v)) = 0"
    using nth[of 0] len ne by (simp add: hd_conv_nth)
  have steps: "\<forall>j. Suc j < length (diagSeq 0 v) \<longrightarrow>
                 fst (diagSeq 0 v ! Suc j) \<le> Suc (fst (diagSeq 0 v ! j))"
  proof (intro allI impI)
    fix j assume "Suc j < length (diagSeq 0 v)"
    hence "Suc j < Suc v" using len by simp
    thus "fst (diagSeq 0 v ! Suc j) \<le> Suc (fst (diagSeq 0 v ! j))"
      using nth[of j] nth[of "Suc j"] by simp
  qed
  show ?thesis unfolding blockok_def using hd0 steps by simp
qed

lemma blockok_oper:
  assumes b: "blockok 0 M" and n1: "1 \<le> n"
  shows "blockok 0 (oper M n)"
proof -
  define j1 where "j1 = Lng M - 1"
  show ?thesis
  proof (cases "j1 = 0")
    case True thus ?thesis using b unfolding oper_def Let_def j1_def by simp
  next
    case False
    have len2: "2 \<le> Lng M" using False j1_def by simp
    have Mne: "M \<noteq> []" using len2 by auto
    have j1len: "j1 < Lng M" using False j1_def by simp
    show ?thesis
    proof (cases "entry M 0 j1 = 0 \<and> entry M 1 j1 = 0")
      case True
      have "oper M n = Pred M" unfolding oper_def Let_def j1_def[symmetric] using False True by auto
      moreover have "blockok 0 (Pred M)"
        unfolding Pred_def using b blockok_butlast by simp
      ultimately show ?thesis by simp
    next
      case Fz: False
      define i1 where "i1 = idx1 M j1"
      show ?thesis
      proof (cases "hasParent M i1 j1")
        case False2: False
        have "oper M n = Pred M"
          unfolding oper_def Let_def j1_def[symmetric] i1_def[symmetric]
          using False Fz False2 by auto
        moreover have "blockok 0 (Pred M)"
          unfolding Pred_def using b blockok_butlast by simp
        ultimately show ?thesis by simp
      next
        case hp: True
        define j0 where "j0 = parent M i1 j1"
        define d0 where "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
        define d1 where "d1 = (if 1 < i1 then entry M 1 j1 - entry M 1 j0 else 0)"
        define blk where "blk = (\<lambda>k. map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j + k * d1)) [j0..<j1])"
        have opeq: "oper M n = take j0 M @ concat (map blk [0..<n])"
          unfolding oper_def Let_def j1_def[symmetric] i1_def[symmetric]
            j0_def[symmetric] d0_def[symmetric] d1_def[symmetric] blk_def
          using False Fz hp by auto
        have nR: "nextR M i1 j0 j1" unfolding j0_def by (rule parent_nextR[OF hp])
        have j0j1: "j0 < j1" using nR by (rule nextR_less)
        have e0step: "\<And>j. Suc j < Lng M \<Longrightarrow> entry M 0 (Suc j) \<le> Suc (entry M 0 j)"
        proof -
          fix j assume sj: "Suc j < Lng M"
          have "fst (M ! Suc j) \<le> Suc (fst (M ! j))" using b sj unfolding blockok_def by blast
          thus "entry M 0 (Suc j) \<le> Suc (entry M 0 j)" unfolding entry_def by simp
        qed
        have sj1: "Suc (j1 - 1) = j1" using False by simp
        have "Suc (j1 - 1) < Lng M" using sj1 j1len by simp
        hence "entry M 0 (Suc (j1 - 1)) \<le> Suc (entry M 0 (j1 - 1))" by (rule e0step)
        hence e0j1: "entry M 0 j1 \<le> Suc (entry M 0 (j1 - 1))" using sj1 by simp
        have e0le: "entry M 0 j0 + d0 \<le> Suc (entry M 0 (j1 - 1))"
        proof (cases "0 < i1")
          case True
          have "nextrel1 M j0 j1" using nR True unfolding nextR_def by simp
          hence "le0 M j0 j1" unfolding nextrel1_def by blast
          hence le01: "entry M 0 j0 \<le> entry M 0 j1" by (rule le0_entry0_mono)
          have d0v: "d0 = entry M 0 j1 - entry M 0 j0" using True d0_def by simp
          have "entry M 0 j0 + d0 = entry M 0 j1" using d0v le01 by simp
          thus ?thesis using e0j1 by simp
        next
          case False3: False
          have "nextrel0 M j0 j1" using nR False3 unfolding nextR_def i1_def by (simp add: idx1_def)
          hence lt01: "entry M 0 j0 < entry M 0 j1" by (rule nextrel0_entry0_less)
          have d0v: "d0 = 0" using False3 d0_def by simp
          show ?thesis using lt01 d0v e0j1 by simp
        qed
        have blkne: "\<And>k. k < n \<Longrightarrow> blk k \<noteq> []" unfolding blk_def using j0j1 by simp
        have blkhd: "\<And>k. hd (blk k) = (entry M 0 j0 + k * d0, entry M 1 j0 + k * d1)"
          unfolding blk_def using j0j1 by (simp add: hd_map upt_conv_Cons)
        have blklast: "\<And>k. last (blk k)
            = (entry M 0 (j1 - 1) + k * d0, entry M 1 (j1 - 1) + k * d1)"
          unfolding blk_def using j0j1 by (simp add: last_map)
        have blksteps: "\<And>k. k < n \<Longrightarrow> steps1 (blk k)"
        proof -
          fix k assume "k < n"
          show "steps1 (blk k)"
            unfolding steps1_iff
          proof (intro allI impI)
            fix j assume jl: "Suc j < length (blk k)"
            have lb: "length (blk k) = j1 - j0" unfolding blk_def by simp
            have idx: "blk k ! j = (entry M 0 (j0 + j) + k * d0, entry M 1 (j0 + j) + k * d1)"
                      "blk k ! Suc j = (entry M 0 (j0 + Suc j) + k * d0, entry M 1 (j0 + Suc j) + k * d1)"
              unfolding blk_def using jl lb by (auto simp: nth_map)
            have "Suc (j0 + j) < Lng M" using jl lb j1len by simp
            hence "entry M 0 (Suc (j0 + j)) \<le> Suc (entry M 0 (j0 + j))" by (rule e0step)
            thus "fst (blk k ! Suc j) \<le> Suc (fst (blk k ! j))" using idx by simp
          qed
        qed
        have blkjunc: "\<And>k. Suc k < n \<Longrightarrow> fst (hd (blk (Suc k))) \<le> Suc (fst (last (blk k)))"
        proof -
          fix k assume "Suc k < n"
          have "fst (hd (blk (Suc k))) = entry M 0 j0 + Suc k * d0" using blkhd by simp
          also have "entry M 0 j0 + Suc k * d0 = (entry M 0 j0 + d0) + k * d0" by simp
          also have "\<dots> \<le> Suc (entry M 0 (j1 - 1)) + k * d0" using e0le by simp
          also have "\<dots> = Suc (fst (last (blk k)))" using blklast by simp
          finally show "fst (hd (blk (Suc k))) \<le> Suc (fst (last (blk k)))" .
        qed
        have cprops: "steps1 (concat (map blk [0..<n]))
              \<and> (0 < n \<longrightarrow> concat (map blk [0..<n]) \<noteq> []
                   \<and> hd (concat (map blk [0..<n])) = hd (blk 0)
                   \<and> last (concat (map blk [0..<n])) = last (blk (n - 1)))"
          by (rule steps1_concat_map[where n = n and F = blk, OF blksteps blkne blkjunc])
        have npos: "0 < n" using n1 by simp
        have cne: "concat (map blk [0..<n]) \<noteq> []" using cprops npos by blast
        have chd: "hd (concat (map blk [0..<n])) = (entry M 0 j0, entry M 1 j0)"
          using cprops npos blkhd[of 0] by simp
        \<comment> \<open>head of the result\<close>
        have hd0: "fst (hd (oper M n)) = 0"
        proof (cases "j0 = 0")
          case True
          have "hd (oper M n) = (entry M 0 0, entry M 1 0)" using opeq True cne chd by simp
          moreover have "entry M 0 0 = fst (hd M)"
            unfolding entry_def using Mne by (simp add: hd_conv_nth)
          ultimately show ?thesis using b Mne unfolding blockok_def by simp
        next
          case False4: False
          have tne: "take j0 M \<noteq> []" using False4 Mne by simp
          have "hd (oper M n) = hd M" using opeq tne by (simp add: hd_append)
          thus ?thesis using b Mne unfolding blockok_def by simp
        qed
        \<comment> \<open>steps of the result\<close>
        have tk: "steps1 (take j0 M)"
          unfolding steps1_iff
        proof (intro allI impI)
          fix j assume sj: "Suc j < length (take j0 M)"
          have sjm: "Suc j < Lng M" and sj0: "Suc j < j0" using sj by auto
          have "fst (M ! Suc j) \<le> Suc (fst (M ! j))" using b sjm unfolding blockok_def by blast
          thus "fst (take j0 M ! Suc j) \<le> Suc (fst (take j0 M ! j))" using sj0 by simp
        qed
        have junc0: "take j0 M = [] \<or> concat (map blk [0..<n]) = [] \<or>
                       fst (hd (concat (map blk [0..<n]))) \<le> Suc (fst (last (take j0 M)))"
        proof (cases "j0 = 0")
          case True thus ?thesis by simp
        next
          case False5: False
          have j0len: "j0 \<le> Lng M" using j0j1 j1len by simp
          have lentk: "length (take j0 M) = j0" using j0len by simp
          have tkne: "take j0 M \<noteq> []" using False5 j0len Mne by simp
          have "last (take j0 M) = take j0 M ! (j0 - 1)"
            using tkne lentk by (simp add: last_conv_nth)
          also have "\<dots> = M ! (j0 - 1)" using False5 by simp
          finally have lt: "last (take j0 M) = M ! (j0 - 1)" .
          have "Suc (j0 - 1) < Lng M" using False5 j0j1 j1len by simp
          hence "entry M 0 (Suc (j0 - 1)) \<le> Suc (entry M 0 (j0 - 1))" by (rule e0step)
          hence "entry M 0 j0 \<le> Suc (entry M 0 (j0 - 1))" using False5 by simp
          moreover have "fst (last (take j0 M)) = entry M 0 (j0 - 1)"
            using lt unfolding entry_def by simp
          ultimately show ?thesis using chd by simp
        qed
        have stepsR: "steps1 (oper M n)"
          using opeq steps1_append tk cprops junc0 by auto
        have setR: "\<forall>p \<in> set (oper M n). (0::nat) \<le> fst p" by simp
        have neR: "oper M n \<noteq> [] \<longrightarrow> fst (hd (oper M n)) = 0" using hd0 by simp
        show ?thesis using blockok_via_steps1 neR setR stepsR by blast
      qed
    qed
  qed
qed

theorem olt_iff_seqlex:
  assumes "blockok d M" "blockok d N" "M \<noteq> N"
  shows "translate M <o translate N \<longleftrightarrow> seqlex M N"
proof
  assume "seqlex M N"
  thus "translate M <o translate N" by (rule seqlex_imp_olt[OF assms(1,2)])
next
  assume o: "translate M <o translate N"
  show "seqlex M N"
  proof (rule ccontr)
    assume "\<not> seqlex M N"
    hence "seqlex N M" using seqlex_total assms(3) by blast
    hence "translate N <o translate M" by (rule seqlex_imp_olt[OF assms(2,1)])
    thus False using o olt_trans olt_irrefl by blast
  qed
qed

theorem blockok_ST_PS: "M \<in> ST_PS \<Longrightarrow> blockok 0 M"
proof (induction M rule: ST_PS.induct)
  case (diag v) show ?case by (rule blockok_diagSeq)
next
  case (oper M n) show ?case by (rule blockok_oper[OF oper.IH oper.hyps(2)])
qed

theorem olt_ST_iff_seqlex:
  assumes "M \<in> ST_PS" "N \<in> ST_PS" "M \<noteq> N"
  shows "translate M <o translate N \<longleftrightarrow> seqlex M N"
  by (rule olt_iff_seqlex[OF blockok_ST_PS[OF assms(1)] blockok_ST_PS[OF assms(2)] assms(3)])

end
