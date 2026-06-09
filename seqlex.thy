theory seqlex
  imports proofs
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

end
