theory Cofinality
  imports Column
begin

lemma pairlt_trans:
  assumes "pairlt p q" "pairlt q r"
  shows "pairlt p r"
  using assms unfolding pairlt_def by auto

lemma seqlex_trans:
  assumes "seqlex A B" "seqlex B C"
  shows "seqlex A C"
  using assms
proof (induction A arbitrary: B C)
  case Nil
  then show ?case by (cases B; cases C) auto
next
  case (Cons a A)
  show ?case using Cons.prems
    by (cases B; cases C)
       (auto intro: pairlt_trans Cons.IH)
qed

definition sle :: "pairseq \<Rightarrow> pairseq \<Rightarrow> bool" where
  "sle M N \<longleftrightarrow> M = N \<or> seqlex M N"

lemma sle_refl:
  "sle M M"
  unfolding sle_def by simp

lemma seqlex_sle_trans:
  assumes "seqlex A B" "sle B C"
  shows "seqlex A C"
  using assms seqlex_trans unfolding sle_def by auto

lemma seqlex_append_mono:
  assumes "seqlex A B"
  shows "seqlex A (B @ C)"
  using assms
proof (induction A arbitrary: B)
  case Nil
  then show ?case by (cases B) simp_all
next
  case (Cons a A)
  show ?case
  proof (cases B)
    case Nil
    then show ?thesis using Cons.prems by simp
  next
    case (Cons b B')
    from Cons.prems have
      "pairlt a b \<or> (a = b \<and> seqlex A B')"
      using Cons by simp
    then show ?thesis
    proof
      assume "pairlt a b"
      then show ?thesis using Cons by simp
    next
      assume rest: "a = b \<and> seqlex A B'"
      have "seqlex A (B' @ C)"
        by (rule Cons.IH) (use rest in simp)
      then show ?thesis using rest Cons by simp
    qed
  qed
qed

lemma sle_append_mono:
  assumes "sle A B"
  shows "sle A (B @ C)"
proof (cases "A = B")
  case True
  show ?thesis
  proof (cases C)
    case Nil
    show ?thesis using True Nil unfolding sle_def by simp
  next
    case (Cons c C')
    have "seqlex A (A @ C)"
      by (rule seqlex_prefix) (use Cons in simp)
    then show ?thesis using True unfolding sle_def by simp
  qed
next
  case False
  have "seqlex A B"
    using assms False unfolding sle_def by simp
  then have "seqlex A (B @ C)"
    by (rule seqlex_append_mono)
  then show ?thesis unfolding sle_def by simp
qed

lemma seqlex_snoc_cases:
  assumes "seqlex N (D @ [lp])"
  shows
    "sle N D \<or>
      (\<exists>q S. N = D @ q # S \<and> pairlt q lp)"
  using assms
proof (induction D arbitrary: N)
  case Nil
  show ?case
  proof (cases N)
    case Nil
    show ?thesis using Nil unfolding sle_def by simp
  next
    case (Cons q S)
    have "pairlt q lp"
      using Nil.prems Cons by (cases S) auto
    then show ?thesis using Cons by auto
  qed
next
  case (Cons d D)
  show ?case
  proof (cases N)
    case Nil
    then show ?thesis unfolding sle_def by simp
  next
    case (Cons q S)
    from Cons.prems have split:
      "pairlt q d \<or> (q = d \<and> seqlex S (D @ [lp]))"
      using Cons by simp
    from split show ?thesis
    proof
      assume "pairlt q d"
      then show ?thesis using Cons unfolding sle_def by simp
    next
      assume right:
        "q = d \<and> seqlex S (D @ [lp])"
      then have qd: "q = d"
        and tail: "seqlex S (D @ [lp])" by auto
      from Cons.IH[OF tail] show ?thesis
      proof
        assume "sle S D"
        then show ?thesis using qd Cons
          unfolding sle_def by auto
      next
        assume "\<exists>x T. S = D @ x # T \<and> pairlt x lp"
        then obtain x T where
          S: "S = D @ x # T" and xlp: "pairlt x lp"
          by blast
        show ?thesis using qd Cons S xlp by auto
      qed
    qed
  qed
qed

definition SeqlexCofinality :: bool where
  "SeqlexCofinality \<longleftrightarrow>
    (\<forall>M N. ST_PS M \<longrightarrow> ST_PS N
      \<longrightarrow> seqlex N M
      \<longrightarrow>
      (\<exists>n. 1 \<le> n \<and> sle N (M\<lbrakk>n\<rbrakk>)))"

lemma pss_cofinality_of_seqlex:
  assumes H: "SeqlexCofinality"
    and Mst: "ST_PS M"
    and Nst: "ST_PS N"
    and lt: "translate N <o translate M"
  shows
    "\<exists>n. 1 \<le> n \<and>
      translate N \<le>o translate (M\<lbrakk>n\<rbrakk>)"
proof -
  have ne: "N \<noteq> M"
  proof
    assume "N = M"
    with lt show False using olt_irrefl by blast
  qed
  have sl: "seqlex N M"
    using olt_ST_iff_seqlex[OF Nst Mst ne] lt by simp
  have main:
    "\<forall>M N. ST_PS M \<longrightarrow> ST_PS N
      \<longrightarrow> seqlex N M
      \<longrightarrow>
      (\<exists>n. 1 \<le> n \<and> sle N (M\<lbrakk>n\<rbrakk>))"
    using H unfolding SeqlexCofinality_def by simp
  obtain n where n1: "1 \<le> n"
    and res: "sle N (M\<lbrakk>n\<rbrakk>)"
    using main[rule_format, OF Mst Nst sl] by blast
  show ?thesis
  proof (intro exI[of _ n] conjI)
    show "1 \<le> n" by (rule n1)
    show "translate N \<le>o translate (M\<lbrakk>n\<rbrakk>)"
    proof (cases "N = M\<lbrakk>n\<rbrakk>")
      case True
      show ?thesis using True unfolding ole_def by simp
    next
      case False
      have sl': "seqlex N (M\<lbrakk>n\<rbrakk>)"
        using res False unfolding sle_def by simp
      have ost: "ST_PS (M\<lbrakk>n\<rbrakk>)"
        by (rule ST_PS.oper[OF Mst n1])
      have "translate N <o translate (M\<lbrakk>n\<rbrakk>)"
        using olt_ST_iff_seqlex[OF Nst ost False] sl'
        by simp
      then show ?thesis unfolding ole_def by simp
    qed
  qed
qed

lemma entry_zero:
  "entry M 0 j = fst (nth_default (0, 0) M j)"
  by (cases "j < length M")
     (simp_all add: entry_def nth_default_nth
        nth_default_beyond)

lemma entry_one:
  "entry M 1 j = snd (nth_default (0, 0) M j)"
  by (cases "j < length M")
     (simp_all add: entry_def nth_default_nth
        nth_default_beyond)

lemma dropLast_snoc_getD:
  assumes "M \<noteq> []"
  shows
    "butlast M @
      [nth_default (0, 0) M (length M - 1)] = M"
proof -
  have last:
    "nth_default (0, 0) M (length M - 1) = last M"
    using assms
    by (simp add: nth_default_nth last_conv_nth)
  show ?thesis using assms last by simp
qed

lemma seqlex_cof_short:
  assumes short: "length M - 1 = 0"
    and sl: "seqlex N M"
  shows
    "\<exists>n. 1 \<le> n \<and> sle N (M\<lbrakk>n\<rbrakk>)"
proof (intro exI[of _ 1] conjI)
  show "1 \<le> (1::nat)" by simp
  have eq: "M\<lbrakk>1\<rbrakk> = M"
    by (rule oper_eq_self_of_short[OF short])
  show "sle N (M\<lbrakk>1\<rbrakk>)"
    using sl eq unfolding sle_def by simp
qed

lemma seqlex_cof_zero:
  assumes L: "1 < length M"
    and zero:
      "entry M 0 (length M - 1) = 0 \<and>
       entry M 1 (length M - 1) = 0"
    and sl: "seqlex N M"
  shows
    "\<exists>n. 1 \<le> n \<and> sle N (M\<lbrakk>n\<rbrakk>)"
proof -
  have Mne: "M \<noteq> []" using L by auto
  have lpzero:
    "nth_default (0, 0) M (length M - 1) = (0, 0)"
  proof (rule prod_eqI)
    show
      "fst (nth_default (0, 0) M (length M - 1)) =
        fst (0, 0)"
      using zero entry_zero[of M "length M - 1"] by simp
    show
      "snd (nth_default (0, 0) M (length M - 1)) =
        snd (0, 0)"
      using zero entry_one[of M "length M - 1"] by simp
  qed
  have split:
    "butlast M @
      [nth_default (0, 0) M (length M - 1)] = M"
    by (rule dropLast_snoc_getD[OF Mne])
  have oper: "M\<lbrakk>1\<rbrakk> = butlast M"
  proof -
    have pred: "M\<lbrakk>1\<rbrakk> = Pred M"
      by (rule oper_eq_pred_of_zero) (use L zero in simp_all)
    show ?thesis using pred L unfolding Pred_def by simp
  qed
  have snoc:
    "seqlex N
      (butlast M @
        [nth_default (0, 0) M (length M - 1)])"
    using sl split by simp
  have cases:
    "sle N (butlast M) \<or>
      (\<exists>q S.
        N = butlast M @ q # S \<and>
        pairlt q
          (nth_default (0, 0) M (length M - 1)))"
    by (rule seqlex_snoc_cases[OF snoc])
  have res: "sle N (butlast M)"
    using cases
  proof
    assume "sle N (butlast M)"
    then show ?thesis .
  next
    assume
      "\<exists>q S.
        N = butlast M @ q # S \<and>
        pairlt q
          (nth_default (0, 0) M (length M - 1))"
    then obtain q S where
      qlt:
        "pairlt q
          (nth_default (0, 0) M (length M - 1))"
      by blast
    have "pairlt q (0, 0)" using qlt lpzero by simp
    then show ?thesis unfolding pairlt_def by simp
  qed
  show ?thesis
    by (intro exI[of _ 1]) (use res oper in simp)
qed

lemma hasParent_last_ST_PS:
  assumes Mst: "ST_PS M"
    and Mpos: "0 < length M"
    and nz:
      "\<not> (entry M 0 (length M - 1) = 0 \<and>
        entry M 1 (length M - 1) = 0)"
  shows
    "hasParent M (idx1 M (length M - 1))
      (length M - 1)"
proof (rule hp_last)
  show "blockok 0 M" by (rule blockok_ST_PS[OF Mst])
  show "z0ok M" by (rule z0ok_ST_PS[OF Mst])
  show "0 < length M" by (rule Mpos)
  show
    "nth_default (0, 0) M (length M - 1) \<noteq> (0, 0)"
  proof
    assume eq:
      "nth_default (0, 0) M (length M - 1) = (0, 0)"
    have e0: "entry M 0 (length M - 1) = 0"
      using entry_zero[of M "length M - 1"] eq by simp
    have e1: "entry M 1 (length M - 1) = 0"
      using entry_one[of M "length M - 1"] eq by simp
    show False using nz e0 e1 by simp
  qed
qed

lemma sle_append_cancel:
  "sle (A @ u) (A @ v) \<longleftrightarrow> sle u v"
  unfolding sle_def
  by (simp add: seqlex_append_cancel)

lemma getD_append_right':
  "nth_default (0, 0) (A @ B) (length A + i) =
    nth_default (0, 0) B i"
proof (cases "i < length B")
  case True
  then show ?thesis
    by (simp add: nth_default_nth nth_append)
next
  case False
  then show ?thesis
    by (simp add: nth_default_beyond)
qed

lemma getD_last_of_snoc:
  "nth_default (0, 0) (D @ [lp])
      (length (D @ [lp]) - 1) = lp"
  by (simp add: nth_default_nth nth_append)

lemma nextrel1_snd_succ:
  assumes hr: "r1ok M"
    and h: "nextrel1 M j0 j1"
  shows "entry M 1 j1 = entry M 1 j0 + 1"
proof -
  have j0M: "j0 < length M"
    and j1M: "j1 < length M"
    and j0j1: "j0 < j1"
    and inc: "entry M 1 j0 < entry M 1 j1"
    and le: "le0 M j0 j1"
    and minimal:
      "\<forall>j. j0 < j \<and> le0 M j j1
        \<longrightarrow> entry M 1 j1 \<le> entry M 1 j"
    using h unfolding nextrel1_def by auto
  have rt: "(nextrel0 M)\<^sup>*\<^sup>* j0 j1"
    using le unfolding le0_def by simp
  obtain c where edge: "nextrel0 M j0 c"
    and tail: "(nextrel0 M)\<^sup>*\<^sup>* c j1"
  proof -
    from rt show ?thesis
    proof (rule converse_rtranclpE)
      assume "j0 = j1"
      then show ?thesis using j0j1 by simp
    next
      fix y
      assume edge: "nextrel0 M j0 y"
        and tail: "(nextrel0 M)\<^sup>*\<^sup>* y j1"
      show ?thesis
        by (rule that[OF edge tail])
    qed
  qed
  have j0c: "j0 < c"
    and cM: "c < length M"
    using edge unfolding nextrel0_def by auto
  have cle: "le0 M c j1"
    unfolding le0_def using cM j1M tail by simp
  have upper1: "entry M 1 j1 \<le> entry M 1 c"
    by (rule minimal[rule_format]) (use j0c cle in simp)
  have c0: "0 < fst (nth_default (0, 0) M c)"
  proof -
    have strict0: "entry M 0 j0 < entry M 0 c"
      using edge unfolding nextrel0_def by simp
    show ?thesis
      using strict0 entry_zero[of M j0]
        entry_zero[of M c] by simp
  qed
  have rmain:
    "\<forall>j. j < length M \<longrightarrow>
      0 < fst (nth_default (0, 0) M j)
      \<longrightarrow>
      (\<exists>k. k < j \<and>
        fst (nth_default (0, 0) M k) + 1 =
          fst (nth_default (0, 0) M j) \<and>
        (\<forall>l. k < l \<longrightarrow> l < j
          \<longrightarrow>
          fst (nth_default (0, 0) M j) \<le>
            fst (nth_default (0, 0) M l)) \<and>
        snd (nth_default (0, 0) M j) \<le>
          snd (nth_default (0, 0) M k) + 1)"
    using hr unfolding r1ok_def by simp
  obtain k where kc: "k < c"
    and level:
      "fst (nth_default (0, 0) M k) + 1 =
        fst (nth_default (0, 0) M c)"
    and valley:
      "\<forall>l. k < l \<longrightarrow> l < c
        \<longrightarrow>
        fst (nth_default (0, 0) M c) \<le>
          fst (nth_default (0, 0) M l)"
    and snd:
      "snd (nth_default (0, 0) M c) \<le>
        snd (nth_default (0, 0) M k) + 1"
    using rmain[rule_format, OF cM c0] by blast
  have kM: "k < length M" using kc cM by simp
  have nk: "nextrel0 M k c"
  proof (unfold nextrel0_def, intro conjI)
    show "k < length M" by (rule kM)
    show "c < length M" by (rule cM)
    show "k < c" by (rule kc)
    show "entry M 0 k < entry M 0 c"
      using level entry_zero[of M k]
        entry_zero[of M c] by simp
    show
      "\<forall>l. k < l \<and> l < c
        \<longrightarrow> entry M 0 c \<le> entry M 0 l"
      using valley entry_zero[of M c]
      by (auto simp: entry_zero)
  qed
  have kj0: "k = j0"
    by (rule nextrel0_unique[OF nk edge])
  have upper2: "entry M 1 c \<le> entry M 1 j0 + 1"
    using snd kj0 entry_one[of M c]
      entry_one[of M j0] by simp
  show ?thesis using inc upper1 upper2 by presburger
qed

lemma oper_bad_blocks_all:
  assumes L: "1 < length M"
    and st: "steps1 M"
    and r1: "r1ok M"
    and zero:
      "\<not> (entry M 0 (length M - 1) = 0 \<and>
        entry M 1 (length M - 1) = 0)"
    and hp:
      "hasParent M (idx1 M (length M - 1))
        (length M - 1)"
  shows
    "\<exists>G v0 w0 R d0 lp.
      M = G @ ((v0, w0) # R) @ [lp] \<and>
      (\<forall>n. 1 \<le> n \<longrightarrow>
        M\<lbrakk>n\<rbrakk> =
          G @ copies d0 ((v0, w0) # R) n) \<and>
      (\<forall>x\<in>set R. v0 < fst x) \<and>
      v0 < fst lp \<and>
      ((d0 = 0 \<and> snd lp = 0 \<and>
          fst lp = v0 + 1) \<or>
       (0 < d0 \<and> snd lp = w0 + 1 \<and>
          fst lp = v0 + d0 \<and>
          nextrel1 M (length G) (length M - 1)))"
proof -
  obtain G v0 w0 R d0 lp where
    M:
      "M = G @ ((v0, w0) # R) @ [lp]"
    and X1:
      "M\<lbrakk>1\<rbrakk> =
        G @ concat
          (map
            (\<lambda>k.
              map
                (\<lambda>p. (fst p + k * d0, snd p))
                ((v0, w0) # R))
            [0..<1])"
    and dom: "\<forall>x\<in>set R. v0 < fst x"
    and lpgt: "v0 < fst lp"
    and branches:
      "(d0 = 0 \<and>
          idx1 M (length M - 1) = 0) \<or>
       (0 < d0 \<and> w0 < snd lp \<and>
          fst lp = v0 + d0 \<and>
          nextrel1 M (length G) (length M - 1))"
    and nr:
      "nextR M (idx1 M (length M - 1))
        (length G) (length M - 1)"
  proof (rule oper_bad_blocks)
    show "1 < length M" by (rule L)
    show
      "\<not> (entry M 0 (length M - 1) = 0 \<and>
        entry M 1 (length M - 1) = 0)"
      by (rule zero)
    show
      "hasParent M (idx1 M (length M - 1))
        (length M - 1)"
      by (rule hp)
    show "1 \<le> (1::nat)" by simp
  qed
  let ?B = "(v0, w0) # R"
  have lpM:
    "lp = nth_default (0, 0) M (length M - 1)"
  proof -
    have at:
      "nth_default (0, 0) (G @ ?B @ [lp])
        (length (G @ ?B @ [lp]) - 1) = lp"
      by (simp add: nth_default_nth nth_append)
    show ?thesis using at M by simp
  qed
  have M': "M = G @ (?B @ [lp])"
    using M by simp
  have len:
    "length M = length G + (length R + 2)"
    using M by simp
  have atG:
    "nth_default (0, 0) M (length G) = (v0, w0)"
  proof -
    have
      "nth_default (0, 0) (G @ (?B @ [lp]))
          (length G + 0) =
        nth_default (0, 0) (?B @ [lp]) 0"
      by (rule getD_append_right')
    then show ?thesis using M' by simp
  qed
  have atG1:
    "nth_default (0, 0) M (length G + 1) =
      nth_default (0, 0) (R @ [lp]) 0"
  proof -
    have
      "nth_default (0, 0) (G @ (?B @ [lp]))
          (length G + 1) =
        nth_default (0, 0) (?B @ [lp]) 1"
      by (rule getD_append_right')
    then show ?thesis using M' by simp
  qed
  have refined:
    "(d0 = 0 \<and> snd lp = 0 \<and>
        fst lp = v0 + 1) \<or>
     (0 < d0 \<and> snd lp = w0 + 1 \<and>
        fst lp = v0 + d0 \<and>
        nextrel1 M (length G) (length M - 1))"
  proof (cases "d0 = 0")
    case d0: True
    from branches d0 have idx:
      "idx1 M (length M - 1) = 0" by auto
    have last1zero:
      "entry M 1 (length M - 1) = 0"
    proof -
      show ?thesis using idx
        unfolding idx1_def by (auto split: if_splits)
    qed
    have lpsnd: "snd lp = 0"
      using last1zero lpM
        entry_one[of M "length M - 1"] by simp
    have nr0:
      "nextrel0 M (length G) (length M - 1)"
      using nr idx unfolding nextR_def by simp
    have j1:
      "length M - 1 = length G + 1 + length R"
      using len by simp
    have Gbound: "length G + 1 < length M"
      using len by simp
    have stepG:
      "entry M 0 (length G + 1) \<le>
        entry M 0 (length G) + 1"
    proof -
      have raw:
        "fst (nth_default (0, 0) M (length G + 1)) \<le>
          fst (nth_default (0, 0) M (length G)) + 1"
        using steps1_iff[THEN iffD1, OF st,
          rule_format, of "length G"] Gbound
        by simp
      show ?thesis using raw entry_zero[of M "length G + 1"]
        entry_zero[of M "length G"] by simp
    qed
    have eG: "entry M 0 (length G) = v0"
      using entry_zero[of M "length G"] atG by simp
    have elast:
      "fst lp = entry M 0 (length M - 1)"
      using entry_zero[of M "length M - 1"] lpM
      by simp
    have minimum:
      "entry M 0 (length M - 1) \<le>
        entry M 0 (length G + 1)"
    proof (cases
        "length G + 1 = length M - 1")
      case True
      show ?thesis using True by simp
    next
      case False
      have between:
        "length G < length G + 1 \<and>
          length G + 1 < length M - 1"
        using len False by simp
      have all:
        "\<forall>j. length G < j \<and>
          j < length M - 1
          \<longrightarrow>
          entry M 0 (length M - 1) \<le>
            entry M 0 j"
        using nr0 unfolding nextrel0_def by simp
      show ?thesis
        by (rule all[rule_format, OF between])
    qed
    have lpfirst: "fst lp = v0 + 1"
      using lpgt stepG eG elast minimum by presburger
    show ?thesis using d0 lpsnd lpfirst by simp
  next
    case d0: False
    from branches d0 have d0pos: "0 < d0"
      and lp1: "fst lp = v0 + d0"
      and nl1:
        "nextrel1 M (length G) (length M - 1)"
      by auto
    have succ:
      "entry M 1 (length M - 1) =
        entry M 1 (length G) + 1"
      by (rule nextrel1_snd_succ[OF r1 nl1])
    have lpsnd: "snd lp = w0 + 1"
      using succ lpM atG entry_one[of M "length M - 1"]
        entry_one[of M "length G"] by simp
    show ?thesis using d0pos lpsnd lp1 nl1 by simp
  qed
  have uniform:
    "\<forall>n. 1 \<le> n \<longrightarrow>
      M\<lbrakk>n\<rbrakk> =
        G @ copies d0 ?B n"
  proof (intro allI impI)
    fix n :: nat
    assume n1: "1 \<le> n"
    obtain G' v0' w0' R' d0' lp' where
      M2:
        "M = G' @ ((v0', w0') # R') @ [lp']"
      and X2:
        "M\<lbrakk>n\<rbrakk> =
          G' @ concat
            (map
              (\<lambda>k.
                map
                  (\<lambda>p.
                    (fst p + k * d0', snd p))
                  ((v0', w0') # R'))
              [0..<n])"
      and dom2: "\<forall>x\<in>set R'. v0' < fst x"
      and lpgt2: "v0' < fst lp'"
      and branches2:
        "(d0' = 0 \<and>
            idx1 M (length M - 1) = 0) \<or>
         (0 < d0' \<and> w0' < snd lp' \<and>
            fst lp' = v0' + d0' \<and>
            nextrel1 M (length G') (length M - 1))"
      and nr2:
        "nextR M (idx1 M (length M - 1))
          (length G') (length M - 1)"
      by (rule oper_bad_blocks[OF L zero hp n1])
    have Glen: "length G' = length G"
    proof -
      have unique:
        "\<forall>y. nextR M (idx1 M (length M - 1)) y
          (length M - 1) \<longrightarrow>
          y = length G"
      proof -
        obtain p where np:
            "nextR M (idx1 M (length M - 1)) p
              (length M - 1)"
          and uniq:
            "\<forall>y. nextR M (idx1 M (length M - 1)) y
              (length M - 1) \<longrightarrow> y = p"
          using hp unfolding hasParent_def by blast
        have pG: "length G = p" using uniq nr by simp
        show ?thesis using uniq pG by simp
      qed
      show ?thesis using unique[rule_format, OF nr2] by simp
    qed
    have full:
      "G' @ (((v0', w0') # R') @ [lp']) =
        G @ (?B @ [lp])"
      using M2 M by simp
    have parts:
      "G' = G \<and>
       ((v0', w0') # R') @ [lp'] = ?B @ [lp]"
      using full Glen by simp
    have Geq: "G' = G" using parts by simp
    have tails:
      "((v0', w0') # R') @ [lp'] = ?B @ [lp]"
      using parts by simp
    have blockeq:
      "(v0', w0') # R' = ?B"
      and lpeq: "lp' = lp"
      using tails by auto
    have veq: "v0' = v0"
      and weq: "w0' = w0"
      and Req: "R' = R"
      using blockeq by auto
    have dEq: "d0' = d0"
    proof -
      have next1_nonzero:
        "\<And>e. nextrel1 M e (length M - 1)
          \<Longrightarrow>
          idx1 M (length M - 1) \<noteq> 0"
      proof -
        fix e
        assume nl: "nextrel1 M e (length M - 1)"
        have lastpos:
          "0 < entry M 1 (length M - 1)"
          using nl unfolding nextrel1_def by simp
        show "idx1 M (length M - 1) \<noteq> 0"
          unfolding idx1_def using lastpos by simp
      qed
      show ?thesis
      proof (cases "d0 = 0")
        case d0z: True
        from branches d0z have idx:
          "idx1 M (length M - 1) = 0" by auto
        have d0'z: "d0' = 0"
        proof (rule ccontr)
          assume "d0' \<noteq> 0"
          from branches2 this obtain nl where
            "nextrel1 M (length G') (length M - 1)"
            by auto
          then show False using idx next1_nonzero by blast
        qed
        show ?thesis using d0z d0'z by simp
      next
        case d0nz: False
        from branches d0nz have
          lp1: "fst lp = v0 + d0"
          and nl:
            "nextrel1 M (length G) (length M - 1)"
          by auto
        have idxnz:
          "idx1 M (length M - 1) \<noteq> 0"
          by (rule next1_nonzero[OF nl])
        from branches2 idxnz have
          lp1': "fst lp' = v0' + d0'"
          by auto
        show ?thesis using lp1 lp1' lpeq veq by simp
      qed
    qed
    show
      "M\<lbrakk>n\<rbrakk> = G @ copies d0 ?B n"
      using X2 Geq veq weq Req dEq
      unfolding copies_def shiftr0_def by simp
  qed
  show ?thesis
    by (intro exI[of _ G] exI[of _ v0]
          exI[of _ w0] exI[of _ R]
          exI[of _ d0] exI[of _ lp])
       (use M uniform dom lpgt refined in simp)
qed

lemma seqlex_splice:
  assumes sl: "seqlex A B"
    and reopen:
      "U = [] \<or>
        (\<forall>x\<in>set B. pairlt (hd U) x)"
  shows "seqlex (A @ U) (B @ C)"
  using sl reopen
proof (induction A arbitrary: B U)
  case Nil
  show ?case
  proof (cases B)
    case BNil: Nil
    then show ?thesis using Nil.prems by simp
  next
    case BCons: (Cons b B')
    show ?thesis
    proof (cases U)
      case UNil: Nil
      then show ?thesis using BCons by simp
    next
      case UCons: (Cons u U')
      have "pairlt u b"
        using Nil.prems(2) BCons UCons
        by auto
      then show ?thesis using BCons UCons by simp
    qed
  qed
next
  case outer: (Cons a A)
  show ?case
  proof (cases B)
    case BNil: Nil
    then show ?thesis using outer.prems by simp
  next
    case BCons: (Cons b B')
    from outer.prems(1) have split:
      "pairlt a b \<or> (a = b \<and> seqlex A B')"
      using BCons by simp
    from split show ?thesis
    proof
      assume "pairlt a b"
      then show ?thesis using BCons by simp
    next
      assume right: "a = b \<and> seqlex A B'"
      have reopen':
        "U = [] \<or>
          (\<forall>x\<in>set B'. pairlt (hd U) x)"
        using outer.prems(2) BCons by auto
      have "seqlex (A @ U) (B' @ C)"
        by (rule outer.IH[OF _ reopen'])
           (use right in simp)
      then show ?thesis using right BCons by simp
    qed
  qed
qed

lemma split_block:
  assumes Rgt: "\<forall>x\<in>set R. v0 < fst x"
    and Yhead:
      "Y = [] \<or> \<not> v0 < fst (hd Y)"
  shows
    "takeWhile (\<lambda>q. v0 < fst q) (R @ Y) = R \<and>
     dropWhile (\<lambda>q. v0 < fst q) (R @ Y) = Y"
proof -
  have allR:
    "\<And>x. x \<in> set R \<Longrightarrow> v0 < fst x"
    using Rgt by simp
  show ?thesis
  proof (cases Y)
    case Nil
    show ?thesis using allR Nil
      by (simp add: takeWhile_eq_all_conv
          dropWhile_eq_Nil_conv)
  next
    case (Cons y Y')
    have ny: "\<not> v0 < fst y"
      using Yhead Cons by simp
    have take:
      "takeWhile (\<lambda>q. v0 < fst q) (R @ y # Y') = R"
      using allR ny
      by (simp add: takeWhile_append2)
    have drop:
      "dropWhile (\<lambda>q. v0 < fst q) (R @ y # Y') =
        y # Y'"
      using allR ny
      by (simp add: dropWhile_append2)
    show ?thesis using take drop Cons by simp
  qed
qed

lemma copy_dom_zero:
  assumes len: "length Y \<le> d"
    and bo: "blockok v0 ((v0, w0) # (R @ Y))"
    and Rgt: "\<forall>x\<in>set R. v0 < fst x"
    and Yhead:
      "Y = [] \<or> \<not> v0 < fst (hd Y)"
    and c:
      "cnf (translate ((v0, w0) # (R @ Y)))"
  shows
    "\<exists>m. 1 \<le> m \<and>
      sle Y (copies 0 ((v0, w0) # R) m)"
  using assms
proof (induction d arbitrary: Y v0 w0 R)
  case 0
  have Ynil: "Y = []" using "0.prems"(1) by simp
  have cp:
    "copies 0 ((v0, w0) # R) 1 = (v0, w0) # R"
    by (rule copies_one)
  show ?case
  proof (intro exI[of _ 1] conjI)
    show "1 \<le> (1::nat)" by simp
    show "sle Y (copies 0 ((v0, w0) # R) 1)"
      unfolding sle_def using Ynil cp by simp
  qed
next
  case (Suc d)
  show ?case
  proof (cases Y)
    case Nil
    have cp:
      "copies 0 ((v0, w0) # R) 1 = (v0, w0) # R"
      by (rule copies_one)
    show ?thesis
    proof (intro exI[of _ 1] conjI)
      show "1 \<le> (1::nat)" by simp
      show "sle Y (copies 0 ((v0, w0) # R) 1)"
        unfolding sle_def using Nil cp by simp
    qed
  next
    case Y: (Cons y Y')
    have elems:
      "\<forall>x\<in>set ((v0, w0) # (R @ y # Y')).
        v0 \<le> fst x"
      using Suc.prems(2) Y unfolding blockok_def by simp
    have yle: "v0 \<le> fst y" using elems by simp
    have nyl: "\<not> v0 < fst y"
      using Suc.prems(4) Y by simp
    have yv: "fst y = v0" using yle nyl by simp
    have yeq: "y = (v0, snd y)"
      by (cases y) (use yv in simp)
    let ?R' = "takeWhile (\<lambda>q. v0 < fst q) Y'"
    let ?Y'' = "dropWhile (\<lambda>q. v0 < fst q) Y'"
    have split: "?R' @ ?Y'' = Y'"
      by simp
    have R'gt: "\<forall>x\<in>set ?R'. v0 < fst x"
      using set_takeWhileD by fastforce
    have Y''head:
      "?Y'' = [] \<or> \<not> v0 < fst (hd ?Y'')"
    proof (cases "?Y'' = []")
      case True
      show ?thesis using True by simp
    next
      case False
      have "\<not> v0 < fst (hd ?Y'')"
        by (rule hd_dropWhile[OF False])
      then show ?thesis by simp
    qed
    have Ty:
      "translate (y # Y') =
        P (snd y) (translate ?R') (translate ?Y'')"
    proof -
      have seq:
        "((v0, snd y) # ?R') @ ?Y'' = y # Y'"
        using yeq split by simp
      have tr:
        "translate (((v0, snd y) # ?R') @ ?Y'') =
          P (snd y) (translate ?R') (translate ?Y'')"
        by (rule translate_block_append[OF R'gt Y''head])
      show ?thesis using seq tr by simp
    qed
    have Tall:
      "translate ((v0, w0) # (R @ y # Y')) =
        P w0 (translate R) (translate (y # Y'))"
    proof -
      have seq:
        "((v0, w0) # R) @ (y # Y') =
          (v0, w0) # (R @ y # Y')" by simp
      have tr:
        "translate (((v0, w0) # R) @ (y # Y')) =
          P w0 (translate R) (translate (y # Y'))"
        by (rule translate_block_append[
              OF Suc.prems(3)])
           (use Suc.prems(4) Y in simp)
      show ?thesis using seq tr by simp
    qed
    have cnfshape:
      "cnf
        (P w0 (translate R)
          (P (snd y) (translate ?R')
            (translate ?Y'')))"
      using Suc.prems(5) Y Tall Ty by simp
    have sib:
      "\<not> (P w0 (translate R) Z <o
        P (snd y) (translate ?R') Z)"
      and ctail:
        "cnf
          (P (snd y) (translate ?R')
            (translate ?Y''))"
      using cnfshape by simp_all
    have yw: "snd y \<le> w0"
    proof (rule ccontr)
      assume "\<not> snd y \<le> w0"
      then have
        "P w0 (translate R) Z <o
          P (snd y) (translate ?R') Z"
        by simp
      with sib show False by simp
    qed
    show ?thesis
    proof (cases "snd y < w0")
      case True
      have plt: "pairlt y (v0, w0)"
        using yv True unfolding pairlt_def by simp
      have sl:
        "seqlex (y # Y') ((v0, w0) # R)"
        using plt by simp
      have cp:
        "copies 0 ((v0, w0) # R) 1 = (v0, w0) # R"
        by (rule copies_one)
      show ?thesis
      proof (intro exI[of _ 1] conjI)
        show "1 \<le> (1::nat)" by simp
        show "sle Y (copies 0 ((v0, w0) # R) 1)"
          using Y sl cp unfolding sle_def by simp
      qed
    next
      case False
      have ywEq: "snd y = w0" using yw False by simp
      have yeqB: "y = (v0, w0)"
        using yeq ywEq by simp
      have notBody:
        "\<not> (translate R <o translate ?R')"
      proof
        assume body: "translate R <o translate ?R'"
        have
          "P w0 (translate R) Z <o
            P (snd y) (translate ?R') Z"
          using body ywEq by simp
        with sib show False by simp
      qed
      have blockY:
        "blockok v0 (y # Y')"
      proof -
        have tail:
          "blockok v0
            (dropWhile (\<lambda>q. v0 < fst q)
              (R @ y # Y'))"
          by (rule blockok_tail)
             (use Suc.prems(2) Y in simp)
        have sp:
          "dropWhile (\<lambda>q. v0 < fst q)
            (R @ y # Y') = y # Y'"
          using Suc.prems(3) nyl
          by (simp add: dropWhile_append2)
        show ?thesis using tail sp by simp
      qed
      have blockR: "blockok (v0 + 1) R"
      proof -
        have arg:
          "blockok (v0 + 1)
            (takeWhile (\<lambda>q. v0 < fst q)
              (R @ y # Y'))"
          by (rule blockok_arg)
             (use Suc.prems(2) Y in simp)
        have sp:
          "takeWhile (\<lambda>q. v0 < fst q)
            (R @ y # Y') = R"
          using Suc.prems(3) nyl
          by (simp add: takeWhile_append2)
        show ?thesis using arg sp by simp
      qed
      have blockR':
        "blockok (v0 + 1) ?R'"
      proof -
        have b:
          "blockok v0 ((v0, snd y) # Y')"
          using blockY yeq by simp
        show ?thesis by (rule blockok_arg[OF b])
      qed
      show ?thesis
      proof (cases "?R' = R")
        case True
        have Yeq:
          "y # Y' = ((v0, w0) # R) @ ?Y''"
          using yeqB split True by simp
        have lenY: "length ?Y'' \<le> d"
        proof -
          have a: "length Y' \<le> d"
            using Suc.prems(1) Y by simp
          have b: "length ?Y'' \<le> length Y'"
            by (rule length_dropWhile_le)
          show ?thesis using a b by simp
        qed
        have boY:
          "blockok v0 ((v0, w0) # (R @ ?Y''))"
          using blockY Yeq by simp
        have cY:
          "cnf (translate
            ((v0, w0) # (R @ ?Y'')))"
        proof -
          have
            "translate ((v0, w0) # (R @ ?Y'')) =
              P (snd y) (translate ?R')
                (translate ?Y'')"
            using Yeq Ty ywEq by simp
          then show ?thesis using ctail by simp
        qed
        obtain m where m1: "1 \<le> m"
          and sm:
            "sle ?Y'' (copies 0 ((v0, w0) # R) m)"
          using Suc.IH[OF lenY boY Suc.prems(3)
            Y''head cY] by blast
        have cancel:
          "sle (((v0, w0) # R) @ ?Y'')
            (((v0, w0) # R) @
              copies 0 ((v0, w0) # R) m)"
          using sle_append_cancel[
            of "(v0, w0) # R" ?Y''
              "copies 0 ((v0, w0) # R) m"] sm
          by simp
        have copies:
          "copies 0 ((v0, w0) # R) (m + 1) =
            ((v0, w0) # R) @
              copies 0 ((v0, w0) # R) m"
          using copies_succ_front[
            of 0 "(v0, w0) # R" m] by simp
        have res:
          "sle Y
            (copies 0 ((v0, w0) # R) (m + 1))"
          using Y Yeq cancel copies by simp
        show ?thesis
          by (intro exI[of _ "m + 1"])
             (use m1 res in simp)
      next
        case False
        have slR: "seqlex ?R' R"
        proof -
          from seqlex_total[of ?R' R] show ?thesis
          proof
            assume "?R' = R"
            then show ?thesis using False by simp
          next
            assume "seqlex ?R' R \<or> seqlex R ?R'"
            then show ?thesis
            proof
              assume "seqlex ?R' R"
              then show ?thesis .
            next
              assume "seqlex R ?R'"
              then have "translate R <o translate ?R'"
                by (rule seqlex_imp_olt[
                      OF blockR blockR'])
              with notBody show ?thesis by simp
            qed
          qed
        qed
        have splice:
          "seqlex (?R' @ ?Y'') (R @ ((v0, w0) # R))"
        proof (rule seqlex_splice[OF slR])
          show
            "?Y'' = [] \<or>
              (\<forall>x\<in>set R.
                pairlt (hd ?Y'') x)"
          proof (cases "?Y'' = []")
            case True
            show ?thesis using True by simp
          next
            case False
            have nh:
              "\<not> v0 < fst (hd ?Y'')"
              by (rule hd_dropWhile[OF False])
            show ?thesis
            proof (rule disjI2, intro ballI)
              fix x
              assume "x \<in> set R"
              then have "v0 < fst x"
                using Suc.prems(3) by simp
              then show "pairlt (hd ?Y'') x"
                using nh unfolding pairlt_def by simp
            qed
          qed
        qed
        have target:
          "copies 0 ((v0, w0) # R) (Suc (Suc 0)) =
            (v0, w0) # (R @ ((v0, w0) # R))"
        proof -
          have cp1:
            "copies 0 ((v0, w0) # R) 1 =
              (v0, w0) # R"
            by (rule copies_one)
          have cp2:
            "copies 0 ((v0, w0) # R) (1 + 1) =
              ((v0, w0) # R) @
                shiftr0 0
                  (copies 0 ((v0, w0) # R) 1)"
            by (rule copies_succ_front)
          show ?thesis using cp1 cp2 by simp
        qed
        have sl:
          "seqlex (y # Y')
            (copies 0 ((v0, w0) # R) (Suc (Suc 0)))"
          using yeqB split splice target by simp
        show ?thesis
        proof (intro exI[of _ "Suc (Suc 0)"] conjI)
          show "1 \<le> Suc (Suc 0)" by simp
          show
            "sle Y
              (copies 0 ((v0, w0) # R) (Suc (Suc 0)))"
            using Y sl unfolding sle_def by simp
        qed
      qed
    qed
  qed
qed

lemma copies_zero_succ:
  "copies 0 blk (m + 1) = copies 0 blk m @ blk"
  unfolding copies_def shiftr0_def
  by (simp add: upt_Suc_append)

lemma crux_zero:
  assumes Nst:
      "ST_PS ((G @ ((v0, w0) # R)) @ q # S)"
    and Rgt: "\<forall>x\<in>set R. v0 < fst x"
    and lp2: "snd lp = 0"
    and lp1: "fst lp = v0 + 1"
    and qlp: "pairlt q lp"
  shows
    "\<exists>m. 1 \<le> m \<and>
      sle (q # S) (copies 0 ((v0, w0) # R) m)"
proof -
  have qle: "fst q \<le> v0"
    using qlp lp1 lp2 unfolding pairlt_def by auto
  show ?thesis
  proof (cases "fst q < v0")
    case True
    have plt: "pairlt q (v0, w0)"
      using True unfolding pairlt_def by simp
    have sl: "seqlex (q # S) ((v0, w0) # R)"
      using plt by simp
    have cp:
      "copies 0 ((v0, w0) # R) 1 = (v0, w0) # R"
      by (rule copies_one)
    show ?thesis
    proof (intro exI[of _ 1] conjI)
      show "1 \<le> (1::nat)" by simp
      show "sle (q # S)
          (copies 0 ((v0, w0) # R) 1)"
        using sl cp unfolding sle_def by simp
    qed
  next
    case False
    have qv: "fst q = v0" using qle False by simp
    let ?Y = "takeWhile (\<lambda>p. v0 \<le> fst p) (q # S)"
    let ?V = "dropWhile (\<lambda>p. v0 \<le> fst p) (q # S)"
    have YV: "?Y @ ?V = q # S" by simp
    have Ycons:
      "?Y = q # takeWhile (\<lambda>p. v0 \<le> fst p) S"
      using qv by simp
    have Yhead: "fst (hd ?Y) = v0"
      using Ycons qv by simp
    have Yge: "\<forall>x\<in>set ?Y. v0 \<le> fst x"
      using set_takeWhileD by fastforce
    have Vhead:
      "?V = [] \<or>
        (\<exists>z Z. ?V = z # Z \<and> fst z < v0)"
    proof (cases "?V = []")
      case True
      show ?thesis using True by simp
    next
      case False
      obtain z Z where V: "?V = z # Z"
        using False by (cases ?V) auto
      have nle: "\<not> v0 \<le> fst z"
      proof -
        have "\<not> v0 \<le> fst (hd ?V)"
          by (rule hd_dropWhile[OF False])
        then show ?thesis using V by simp
      qed
      have "fst z < v0" using nle by simp
      then show ?thesis using V by blast
    qed
    let ?B = "(v0, w0) # R"
    have Nsplit:
      "(G @ ?B) @ q # S =
        (G @ (?B @ ?Y)) @ ?V"
      using YV by simp
    have stN: "steps1 ((G @ ?B) @ q # S)"
      using blockok_ST_PS[OF Nst]
      unfolding blockok_def by simp
    have stSplit:
      "steps1 ((G @ (?B @ ?Y)) @ ?V)"
      using stN Nsplit by simp
    have stPrefix: "steps1 (G @ (?B @ ?Y))"
      using steps1_append[THEN iffD1, OF stSplit]
      by simp
    have stBY: "steps1 (?B @ ?Y)"
      using steps1_append[THEN iffD1, OF stPrefix]
      by simp
    have allBY:
      "\<forall>x\<in>set (?B @ ?Y). v0 \<le> fst x"
    proof (intro ballI)
      fix x
      assume "x \<in> set (?B @ ?Y)"
      then consider
          (root) "x = (v0, w0)"
        | (body) "x \<in> set R"
        | (tail) "x \<in> set ?Y"
        by auto
      then show "v0 \<le> fst x"
      proof cases
        case root
        show ?thesis using root by simp
      next
        case body
        show ?thesis using Rgt body by auto
      next
        case tail
        show ?thesis
          by (rule Yge[rule_format, OF tail])
      qed
    qed
    have bo:
      "blockok v0 (?B @ ?Y)"
      unfolding blockok_def
    proof (intro conjI)
      show "?B @ ?Y \<noteq> [] \<longrightarrow>
          fst (hd (?B @ ?Y)) = v0"
        by simp
      show "\<forall>p\<in>set (?B @ ?Y). v0 \<le> fst p"
        by (rule allBY)
      show "steps1 (?B @ ?Y)"
        by (rule stBY)
    qed
    have cnfN:
      "cnf (translate ((G @ ?B) @ q # S))"
      by (rule cnf_ST_PS[OF Nst])
    have cnfSplit:
      "cnf (translate ((G @ (?B @ ?Y)) @ ?V))"
      using cnfN Nsplit by simp
    have cnfPrefix:
      "cnf (translate (G @ (?B @ ?Y)))"
    proof -
      have raw:
        "cnf (translate
          (take (length (G @ (?B @ ?Y)))
            ((G @ (?B @ ?Y)) @ ?V)))"
        by (rule cnf_take[OF cnfSplit])
      show ?thesis using raw by simp
    qed
    have seq:
      "G @ (?B @ ?Y) =
        G @ (v0, w0) # (R @ ?Y)"
      by simp
    have cnfWindow:
      "cnf (translate ((v0, w0) # (R @ ?Y)))"
    proof (rule cnf_tail)
      show
        "\<forall>x\<in>set (R @ ?Y).
          fst (v0, w0) \<le> fst x"
      proof (intro ballI)
        fix x
        assume mem0: "x \<in> set (R @ ?Y)"
        have mem:
          "x \<in> set R \<or> x \<in> set ?Y"
          using mem0 by (auto simp only: set_append)
        from mem show "fst (v0, w0) \<le> fst x"
        proof
          assume body: "x \<in> set R"
          from Rgt[rule_format, OF body]
          show ?thesis by simp
        next
          assume tail: "x \<in> set ?Y"
          from Yge[rule_format, OF tail]
          show ?thesis by simp
        qed
      qed
      show
        "cnf (translate
          (G @ (v0, w0) # (R @ ?Y)))"
        using cnfPrefix seq by simp
    qed
    have boWindow:
      "blockok v0 ((v0, w0) # (R @ ?Y))"
      using bo by simp
    have Ystop:
      "?Y = [] \<or> \<not> v0 < fst (hd ?Y)"
      using Ycons Yhead by simp
    obtain m where m1: "1 \<le> m"
      and dom:
        "sle ?Y (copies 0 ?B m)"
      using copy_dom_zero[
        of ?Y "length ?Y" v0 w0 R]
        boWindow Rgt Ystop cnfWindow
      by auto
    have cp:
      "copies 0 ?B (m + 1) =
        copies 0 ?B m @ ?B"
      by (rule copies_zero_succ)
    show ?thesis
    proof (intro exI[of _ "m + 1"] conjI)
      show "1 \<le> m + 1" using m1 by simp
      show "sle (q # S) (copies 0 ?B (m + 1))"
      proof (cases "?Y = copies 0 ?B m")
        case True
        have tail:
          "seqlex ?V ?B"
        using Vhead
        proof
          assume Vnil: "?V = []"
          then show ?thesis by simp
        next
          assume "\<exists>z Z. ?V = z # Z \<and> fst z < v0"
          then obtain z Z where V: "?V = z # Z"
            and zv: "fst z < v0" by blast
          have "pairlt z (v0, w0)"
            using zv unfolding pairlt_def by simp
          then show ?thesis using V by simp
        qed
        have sl:
          "seqlex (?Y @ ?V)
            (copies 0 ?B m @ ?B)"
          using True tail seqlex_append_cancel[
            of "copies 0 ?B m" ?V ?B] by simp
        show ?thesis using YV cp sl
          unfolding sle_def by simp
      next
        case False
        have strict: "seqlex ?Y (copies 0 ?B m)"
          using dom False unfolding sle_def by simp
        have reopen:
          "?V = [] \<or>
            (\<forall>x\<in>set (copies 0 ?B m).
              pairlt (hd ?V) x)"
        using Vhead
        proof
          assume Vnil: "?V = []"
          show ?thesis using Vnil by simp
        next
          assume "\<exists>z Z. ?V = z # Z \<and> fst z < v0"
          then obtain z Z where V: "?V = z # Z"
            and zv: "fst z < v0" by blast
          show ?thesis
          proof (rule disjI2, intro ballI)
            fix x
            assume x:
              "x \<in> set (copies 0 ?B m)"
            have Rle:
              "\<forall>y\<in>set R. v0 \<le> fst y"
            proof (intro ballI)
              fix y
              assume yR: "y \<in> set R"
              show "v0 \<le> fst y"
                by (rule less_imp_le[
                      OF Rgt[rule_format, OF yR]])
            qed
            have copyall:
              "\<forall>y\<in>set (copies 0 ?B m).
                v0 \<le> fst y"
              by (rule copies_v0_le[OF Rle])
            have "v0 \<le> fst x"
              by (rule copyall[rule_format, OF x])
            then show "pairlt (hd ?V) x"
              using V zv unfolding pairlt_def by simp
          qed
        qed
        have sl:
          "seqlex (?Y @ ?V)
            (copies 0 ?B m @ ?B)"
          by (rule seqlex_splice[OF strict reopen])
        show ?thesis using YV cp sl
          unfolding sle_def by simp
      qed
    qed
  qed
qed

definition AscCrux :: bool where
  "AscCrux \<longleftrightarrow>
    (\<forall>G R S v0 w0 d0 lp q.
      ST_PS ((G @ ((v0, w0) # R)) @ [lp]) \<longrightarrow>
      ST_PS ((G @ ((v0, w0) # R)) @ q # S) \<longrightarrow>
      (\<forall>x\<in>set R. v0 < fst x) \<longrightarrow>
      0 < d0 \<longrightarrow>
      snd lp = w0 + 1 \<longrightarrow>
      fst lp = v0 + d0 \<longrightarrow>
      nextrel1
        ((G @ ((v0, w0) # R)) @ [lp])
        (length G)
        (length (G @ ((v0, w0) # R))) \<longrightarrow>
      pairlt q lp \<longrightarrow>
      (\<exists>m. 1 \<le> m \<and>
        sle (q # S)
          (shiftr0 d0
            (copies d0 ((v0, w0) # R) m))))"

definition AscCrux1 :: bool where
  "AscCrux1 \<longleftrightarrow>
    (\<forall>G R S v0 w0 d0.
      ST_PS
        ((G @ ((v0, w0) # R)) @
          [(v0 + d0, w0 + 1)]) \<longrightarrow>
      ST_PS
        ((G @ ((v0, w0) # R)) @
          (v0 + d0, w0) # S) \<longrightarrow>
      (\<forall>x\<in>set R. v0 < fst x) \<longrightarrow>
      0 < d0 \<longrightarrow>
      nextrel1
        ((G @ ((v0, w0) # R)) @
          [(v0 + d0, w0 + 1)])
        (length G)
        (length (G @ ((v0, w0) # R))) \<longrightarrow>
      (\<exists>m. 1 \<le> m \<and>
        sle ((v0 + d0, w0) # S)
          (shiftr0 d0
            (copies d0 ((v0, w0) # R) m))))"

lemma shiftr0_length:
  "length (shiftr0 d X) = length X"
  unfolding shiftr0_def by simp

lemma mem_shiftr0_le:
  assumes h: "\<forall>x\<in>set X. d \<le> fst x"
  shows "\<forall>x\<in>set (shiftr0 e X). d + e \<le> fst x"
proof (intro ballI)
  fix x
  assume x: "x \<in> set (shiftr0 e X)"
  then obtain p where
    p: "p \<in> set X"
    and xeq: "(fst p + e, snd p) = x"
    using mem_shiftr0[of x e X] by blast
  have dp: "d \<le> fst p"
    by (rule h[rule_format, OF p])
  have de: "d + e \<le> fst p + e"
    using dp by simp
  have fx: "fst p + e = fst x"
  proof -
    have "fst (fst p + e, snd p) = fst x"
      by (rule arg_cong[OF xeq])
    then show ?thesis by simp
  qed
  show "d + e \<le> fst x"
    using de fx by simp
qed

lemma shiftr0_copies:
  "shiftr0 d (copies d blk n) =
    copies d (shiftr0 d blk) n"
  unfolding shiftr0_def copies_def
  by (simp add: map_concat map_map o_def
      add.commute add.left_commute)

definition AscArgDom :: bool where
  "AscArgDom \<longleftrightarrow>
    (\<forall>G R S v0 w0 d0.
      ST_PS
        ((G @ ((v0, w0) # R)) @
          [(v0 + d0, w0 + 1)]) \<longrightarrow>
      ST_PS
        ((G @ ((v0, w0) # R)) @
          (v0 + d0, w0) # S) \<longrightarrow>
      (\<forall>x\<in>set R. v0 < fst x) \<longrightarrow>
      0 < d0 \<longrightarrow>
      nextrel1
        ((G @ ((v0, w0) # R)) @
          [(v0 + d0, w0 + 1)])
        (length G)
        (length (G @ ((v0, w0) # R))) \<longrightarrow>
      (\<exists>m.
        sle
          (takeWhile
            (\<lambda>p. v0 + d0 < fst p) S)
          (shiftr0 d0
            (R @
              copies d0
                (shiftr0 d0 ((v0, w0) # R))
                m))))"

lemma shiftr0_append:
  "shiftr0 d (A @ B) =
    shiftr0 d A @ shiftr0 d B"
  unfolding shiftr0_def by simp

lemma copies_succ_back:
  "copies d blk (n + 1) =
    copies d blk n @ shiftr0 (n * d) blk"
  unfolding copies_def
  by (simp add: upt_Suc_append)

lemma asc_crux1_of_argdom:
  assumes H: AscArgDom
  shows AscCrux1
  unfolding AscCrux1_def
proof (intro allI impI)
  fix G R S v0 w0 d0
  assume hM:
      "ST_PS
        ((G @ ((v0, w0) # R)) @
          [(v0 + d0, w0 + 1)])"
    and hN:
      "ST_PS
        ((G @ ((v0, w0) # R)) @
          (v0 + d0, w0) # S)"
    and hRgt: "\<forall>x\<in>set R. v0 < fst x"
    and hd: "0 < d0"
    and hnr:
      "nextrel1
        ((G @ ((v0, w0) # R)) @
          [(v0 + d0, w0 + 1)])
        (length G)
        (length (G @ ((v0, w0) # R)))"
  let ?Shi =
    "takeWhile (\<lambda>p. v0 + d0 < fst p) S"
  let ?Slo =
    "dropWhile (\<lambda>p. v0 + d0 < fst p) S"
  let ?blk =
    "shiftr0 d0 ((v0, w0) # R)"
  obtain m where hdom:
    "sle ?Shi
      (shiftr0 d0
        (R @ copies d0 ?blk m))"
    using H[unfolded AscArgDom_def, rule_format,
      OF hM hN hRgt[rule_format] hd hnr]
    by blast
  let ?arg =
    "shiftr0 d0 (R @ copies d0 ?blk m)"
  have Ssplit: "?Shi @ ?Slo = S"
    by simp
  have blkcons:
    "?blk =
      (v0 + d0, w0) # shiftr0 d0 R"
    by (simp add: shiftr0_cons)
  have DmGt:
    "\<forall>x\<in>set (R @ copies d0 ?blk m).
      v0 < fst x"
  proof (intro ballI)
    fix x
    assume x:
      "x \<in> set (R @ copies d0 ?blk m)"
    have split:
      "x \<in> set R \<or>
        x \<in> set (copies d0 ?blk m)"
      using x by auto
    from split show "v0 < fst x"
    proof
      assume xR: "x \<in> set R"
      show ?thesis
        by (rule hRgt[rule_format, OF xR])
    next
      assume xcopies:
        "x \<in> set (copies d0 ?blk m)"
      have Rle:
        "\<forall>y\<in>set R. v0 \<le> fst y"
      proof (intro ballI)
        fix y
        assume yR: "y \<in> set R"
        show "v0 \<le> fst y"
          by (rule less_imp_le[
                OF hRgt[rule_format, OF yR]])
      qed
      have shiftRle:
        "\<forall>y\<in>set (shiftr0 d0 R).
          v0 + d0 \<le> fst y"
        by (rule mem_shiftr0_le[OF Rle])
      have copyLe:
        "\<forall>y\<in>
          set
            (copies d0
              ((v0 + d0, w0) #
                shiftr0 d0 R) m).
          v0 + d0 \<le> fst y"
        by (rule copies_v0_le[OF shiftRle])
      have xcopies':
        "x \<in>
          set
            (copies d0
              ((v0 + d0, w0) #
                shiftr0 d0 R) m)"
        using xcopies blkcons by simp
      have rootle: "v0 + d0 \<le> fst x"
        by (rule copyLe[rule_format, OF xcopies'])
      have rootgt: "v0 < v0 + d0"
        using hd by simp
      show "v0 < fst x"
        using rootgt rootle by (rule less_le_trans)
    qed
  qed
  have SloHd:
    "?Slo = [] \<or>
      fst (hd ?Slo) \<le> v0 + d0"
  proof (cases "?Slo = []")
    case True
    then show ?thesis by simp
  next
    case False
    have nlt:
      "\<not> v0 + d0 < fst (hd ?Slo)"
      by (rule hd_dropWhile[OF False])
    then have "fst (hd ?Slo) \<le> v0 + d0"
      by simp
    then show ?thesis by simp
  qed
  let ?E =
    "shiftr0 d0
      (shiftr0 (m * d0) ?blk)"
  have inner:
    "shiftr0 d0
      (copies d0 ?blk (m + 1)) =
      shiftr0 d0 (copies d0 ?blk m) @ ?E"
    using copies_succ_back[of d0 ?blk m]
    by (simp add: shiftr0_append)
  have target:
    "shiftr0 d0
      (copies d0 ((v0, w0) # R) (m + 2)) =
      (v0 + d0, w0) #
        (?arg @ ?E)"
  proof -
    have
      "shiftr0 d0
        (copies d0 ((v0, w0) # R)
          (m + 2)) =
        copies d0 ?blk (m + 2)"
      by (rule shiftr0_copies)
    also have
      "\<dots> =
        ?blk @
          shiftr0 d0
            (copies d0 ?blk (m + 1))"
      using copies_succ_front[
        of d0 ?blk "m + 1"] by simp
    also have
      "\<dots> =
        ?blk @
          (shiftr0 d0
            (copies d0 ?blk m) @ ?E)"
      using inner by simp
    also have
      "\<dots> =
        (v0 + d0, w0) #
          (?arg @ ?E)"
      using blkcons
      by (simp add: shiftr0_append
          append_assoc)
    finally show ?thesis .
  qed
  have Ene: "?E \<noteq> []"
    using blkcons by simp
  have Ehd:
    "fst (hd ?E) =
      v0 + d0 + m * d0 + d0"
    using blkcons
    by (simp add: shiftr0_cons)
  have tailGoal:
    "sle S (?arg @ ?E)"
  proof -
    have hdomCases:
      "?Shi = ?arg \<or>
        seqlex ?Shi ?arg"
      using hdom unfolding sle_def .
    from hdomCases show ?thesis
    proof
      assume eq: "?Shi = ?arg"
      have sloE: "sle ?Slo ?E"
      proof -
        from SloHd show ?thesis
        proof
          assume SloNil: "?Slo = []"
          obtain b B where E: "?E = b # B"
            using Ene by (cases ?E) auto
          have seq0: "seqlex [] ?E"
            using E by simp
          have "seqlex ?Slo ?E"
            by (subst SloNil, rule seq0)
          then show ?thesis
            unfolding sle_def by simp
        next
          assume hdle:
            "fst (hd ?Slo) \<le> v0 + d0"
          show ?thesis
          proof (cases "?Slo = []")
            case True
            obtain b B where E: "?E = b # B"
              using Ene by (cases ?E) auto
            have seq0: "seqlex [] ?E"
              using E by simp
            have "seqlex ?Slo ?E"
              by (subst True, rule seq0)
            then show ?thesis
              unfolding sle_def by simp
          next
            case False
            obtain z Z where Slo:
              "?Slo = z # Z"
              using False by (cases ?Slo) auto
            obtain b B where E:
              "?E = b # B"
              using Ene by (cases ?E) auto
            have zle: "fst z \<le> v0 + d0"
              using hdle Slo by simp
            have bval:
              "fst b =
                v0 + d0 + m * d0 + d0"
              using Ehd E by simp
            have rootlt:
              "v0 + d0 <
                v0 + d0 + m * d0 + d0"
              using hd by simp
            have zlt0:
              "fst z <
                v0 + d0 + m * d0 + d0"
              by (rule le_less_trans[
                    OF zle rootlt])
            have zlt: "fst z < fst b"
              using zlt0 bval by simp
            have "pairlt z b"
              using zlt unfolding pairlt_def by simp
            then have "seqlex ?Slo ?E"
              using Slo E by simp
            then show ?thesis
              unfolding sle_def by simp
          qed
        qed
      qed
      have
        "sle (?arg @ ?Slo)
          (?arg @ ?E)"
        by (rule sle_append_cancel[THEN iffD2,
              OF sloE])
      then show ?thesis using Ssplit eq by simp
    next
      assume strict:
        "seqlex ?Shi ?arg"
      have reopen:
        "?Slo = [] \<or>
          (\<forall>x\<in>set ?arg.
            pairlt (hd ?Slo) x)"
      proof -
        from SloHd show ?thesis
        proof
          assume SloNil: "?Slo = []"
          then show ?thesis by simp
        next
          assume hdle:
            "fst (hd ?Slo) \<le> v0 + d0"
          show ?thesis
          proof (rule disjI2, intro ballI)
            fix x
            assume xarg: "x \<in> set ?arg"
            then obtain y where
              y: "y \<in>
                  set (R @ copies d0 ?blk m)"
              and xeq:
                "(fst y + d0, snd y) = x"
              using mem_shiftr0[
                of x d0
                  "R @ copies d0 ?blk m"]
              by blast
            have ygt: "v0 < fst y"
              by (rule DmGt[rule_format, OF y])
            have shifted:
              "v0 + d0 < fst y + d0"
              using ygt by simp
            have xfst: "fst y + d0 = fst x"
            proof -
              have
                "fst (fst y + d0, snd y) =
                  fst x"
                by (rule arg_cong[OF xeq])
              then show ?thesis by simp
            qed
            have hlt0:
              "fst (hd ?Slo) <
                fst y + d0"
              by (rule le_less_trans[
                    OF hdle shifted])
            have
              "fst (hd ?Slo) < fst x"
              using hlt0 xfst by simp
            then show "pairlt (hd ?Slo) x"
              unfolding pairlt_def by simp
          qed
        qed
      qed
      have
        "seqlex (?Shi @ ?Slo)
          (?arg @ ?E)"
        by (rule seqlex_splice[OF strict reopen])
      then show ?thesis using Ssplit
        unfolding sle_def by simp
    qed
  qed
  show
    "\<exists>k. 1 \<le> k \<and>
      sle ((v0 + d0, w0) # S)
        (shiftr0 d0
          (copies d0 ((v0, w0) # R) k))"
  proof (intro exI[of _ "m + 2"] conjI)
    show "1 \<le> m + 2" by simp
    have prefix:
      "sle
        ([(v0 + d0, w0)] @ S)
        ([(v0 + d0, w0)] @
          (?arg @ ?E))"
      by (rule sle_append_cancel[
            THEN iffD2, OF tailGoal])
    show
      "sle ((v0 + d0, w0) # S)
        (shiftr0 d0
          (copies d0 ((v0, w0) # R)
            (m + 2)))"
      using prefix target by simp
  qed
qed

lemma asc_head_step:
  assumes H: AscCrux1
  shows AscCrux
  unfolding AscCrux_def
proof (intro allI impI)
  fix G R S v0 w0 d0 lp q
  assume hM:
      "ST_PS
        ((G @ ((v0, w0) # R)) @ [lp])"
    and hN:
      "ST_PS
        ((G @ ((v0, w0) # R)) @ q # S)"
    and hRgt: "\<forall>x\<in>set R. v0 < fst x"
    and hd: "0 < d0"
    and lp2: "snd lp = w0 + 1"
    and lp1: "fst lp = v0 + d0"
    and hnr:
      "nextrel1
        ((G @ ((v0, w0) # R)) @ [lp])
        (length G)
        (length (G @ ((v0, w0) # R)))"
    and qlp: "pairlt q lp"
  have lpeq: "lp = (v0 + d0, w0 + 1)"
    using lp1 lp2 by (cases lp) simp
  show
    "\<exists>m. 1 \<le> m \<and>
      sle (q # S)
        (shiftr0 d0
          (copies d0 ((v0, w0) # R) m))"
  proof (cases "q = (v0 + d0, w0)")
    case True
    have hM':
      "ST_PS
        ((G @ ((v0, w0) # R)) @
          [(v0 + d0, w0 + 1)])"
      using hM lpeq by simp
    have hN':
      "ST_PS
        ((G @ ((v0, w0) # R)) @
          (v0 + d0, w0) # S)"
      using hN True by simp
    have hnr':
      "nextrel1
        ((G @ ((v0, w0) # R)) @
          [(v0 + d0, w0 + 1)])
        (length G)
        (length (G @ ((v0, w0) # R)))"
      using hnr lpeq by simp
    obtain m where m1: "1 \<le> m"
      and dom:
        "sle ((v0 + d0, w0) # S)
          (shiftr0 d0
            (copies d0 ((v0, w0) # R) m))"
      using H[unfolded AscCrux1_def,
        rule_format,
        OF hM' hN' hRgt[rule_format] hd hnr']
      by blast
    show ?thesis using True m1 dom by blast
  next
    case False
    have qroot:
      "pairlt q (v0 + d0, w0)"
      using qlp lpeq False
      unfolding pairlt_def
      by (cases q) auto
    have target1:
      "shiftr0 d0
        (copies d0 ((v0, w0) # R) 1) =
        (v0 + d0, w0) # shiftr0 d0 R"
    proof -
      have cp:
        "copies d0 ((v0, w0) # R) 1 =
          (v0, w0) # R"
        by (rule copies_one)
      have sh:
        "shiftr0 d0 ((v0, w0) # R) =
          (v0 + d0, w0) # shiftr0 d0 R"
        unfolding shiftr0_def by simp
      show ?thesis using cp sh by simp
    qed
    have sl0:
      "seqlex (q # S)
        ((v0 + d0, w0) #
          shiftr0 d0 R)"
      using qroot by simp
    have sl:
      "seqlex (q # S)
        (shiftr0 d0
          (copies d0 ((v0, w0) # R) 1))"
      using sl0 target1 by simp
    show ?thesis
    proof (intro exI[of _ 1] conjI)
      show "1 \<le> (1::nat)" by simp
      show
        "sle (q # S)
          (shiftr0 d0
            (copies d0 ((v0, w0) # R) 1))"
        using sl unfolding sle_def by simp
    qed
  qed
qed

lemma seqlex_cof_bad:
  assumes H: AscCrux
    and Mst: "ST_PS M"
    and Nst: "ST_PS N"
    and L: "1 < length M"
    and nz:
      "\<not> (entry M 0 (length M - 1) = 0 \<and>
        entry M 1 (length M - 1) = 0)"
    and sl: "seqlex N M"
  shows
    "\<exists>n. 1 \<le> n \<and>
      sle N (M\<lbrakk>n\<rbrakk>)"
proof -
  have Mpos: "0 < length M"
    by (rule less_trans[of 0 1 "length M"])
       (use L in simp_all)
  have hp:
    "hasParent M (idx1 M (length M - 1))
      (length M - 1)"
    by (rule hasParent_last_ST_PS[
          OF Mst Mpos nz])
  have bo: "blockok 0 M"
    by (rule blockok_ST_PS[OF Mst])
  have st: "steps1 M"
    using bo unfolding blockok_def by simp
  have r1: "r1ok M"
    by (rule r1ok_ST_PS[OF Mst])
  obtain G v0 w0 R d0 lp where
    Meq:
      "M = G @ ((v0, w0) # R) @ [lp]"
    and Mn:
      "\<forall>n. 1 \<le> n \<longrightarrow>
        M\<lbrakk>n\<rbrakk> =
          G @ copies d0 ((v0, w0) # R) n"
    and Rgt: "\<forall>x\<in>set R. v0 < fst x"
    and lpgt: "v0 < fst lp"
    and disj:
      "(d0 = 0 \<and> snd lp = 0 \<and>
          fst lp = v0 + 1) \<or>
       (0 < d0 \<and> snd lp = w0 + 1 \<and>
          fst lp = v0 + d0 \<and>
          nextrel1 M (length G)
            (length M - 1))"
    using oper_bad_blocks_all[
      OF L st r1 nz hp]
    by blast
  let ?D = "G @ ((v0, w0) # R)"
  have snocCases:
    "sle N ?D \<or>
      (\<exists>q S. N = ?D @ q # S \<and>
        pairlt q lp)"
  proof (rule seqlex_snoc_cases)
    show "seqlex N (?D @ [lp])"
      using sl Meq by simp
  qed
  from snocCases show ?thesis
  proof
    assume hle: "sle N ?D"
    have op1:
      "M\<lbrakk>1\<rbrakk> = ?D"
    proof -
      have
        "M\<lbrakk>1\<rbrakk> =
          G @ copies d0 ((v0, w0) # R) 1"
        by (rule Mn[rule_format]) simp
      also have "\<dots> = ?D"
        by (simp only: copies_one)
      finally show ?thesis .
    qed
    show ?thesis
    proof (intro exI[of _ 1] conjI)
      show "1 \<le> (1::nat)" by simp
      show "sle N (M\<lbrakk>1\<rbrakk>)"
        using hle op1 by simp
    qed
  next
    assume
      "\<exists>q S. N = ?D @ q # S \<and>
        pairlt q lp"
    then obtain q S where
      Neq: "N = ?D @ q # S"
      and qlp: "pairlt q lp"
      by blast
    have Nst':
      "ST_PS (?D @ q # S)"
      using Nst Neq by simp
    have mex:
      "\<exists>m. 1 \<le> m \<and>
        sle (q # S)
          (shiftr0 d0
            (copies d0 ((v0, w0) # R) m))"
    proof -
      from disj show
        "\<exists>m. 1 \<le> m \<and>
          sle (q # S)
            (shiftr0 d0
              (copies d0
                ((v0, w0) # R) m))"
      proof
        assume zero:
          "d0 = 0 \<and> snd lp = 0 \<and>
            fst lp = v0 + 1"
        have z0: "d0 = 0"
          using zero by simp
        have z2: "snd lp = 0"
          using zero by simp
        have z1: "fst lp = v0 + 1"
          using zero by simp
        obtain m where m1: "1 \<le> m"
          and dom:
            "sle (q # S)
              (copies 0 ((v0, w0) # R) m)"
          using crux_zero[
            OF Nst' Rgt
              z2 z1 qlp]
          by blast
        show ?thesis
        proof (intro exI[of _ m] conjI)
          show "1 \<le> m" by (rule m1)
          show
            "sle (q # S)
              (shiftr0 d0
                (copies d0
                  ((v0, w0) # R) m))"
            using dom z0 by simp
        qed
      next
        assume asc:
          "0 < d0 \<and>
            snd lp = w0 + 1 \<and>
            fst lp = v0 + d0 \<and>
            nextrel1 M (length G)
              (length M - 1)"
        have hd: "0 < d0" using asc by simp
        have lp2: "snd lp = w0 + 1"
          using asc by simp
        have lp1: "fst lp = v0 + d0"
          using asc by simp
        have hn1:
          "nextrel1 M (length G)
            (length M - 1)"
          using asc by simp
        have Mst':
          "ST_PS (?D @ [lp])"
          using Mst Meq by simp
        have len:
          "length M - 1 = length ?D"
          using Meq by simp
        have hnr:
          "nextrel1 (?D @ [lp])
            (length G) (length ?D)"
          using hn1 Meq len by simp
        obtain m where m1: "1 \<le> m"
          and dom:
            "sle (q # S)
              (shiftr0 d0
                (copies d0
                  ((v0, w0) # R) m))"
          using H[unfolded AscCrux_def,
            rule_format,
            OF Mst' Nst' Rgt[rule_format]
              hd lp2 lp1 hnr qlp]
          by blast
        show ?thesis using m1 dom by blast
      qed
    qed
    obtain m where m1: "1 \<le> m"
      and hsle:
        "sle (q # S)
          (shiftr0 d0
            (copies d0 ((v0, w0) # R) m))"
      using mex by blast
    show ?thesis
    proof (intro exI[of _ "m + 1"] conjI)
      show "1 \<le> m + 1" by simp
      have op:
        "M\<lbrakk>m + 1\<rbrakk> =
          ?D @
            shiftr0 d0
              (copies d0
                ((v0, w0) # R) m)"
      proof -
        have
          "M\<lbrakk>m + 1\<rbrakk> =
            G @
              copies d0
                ((v0, w0) # R) (m + 1)"
          by (rule Mn[rule_format]) simp
        also have
          "\<dots> =
            ?D @
              shiftr0 d0
                (copies d0
                  ((v0, w0) # R) m)"
          using copies_succ_front[
            of d0 "(v0, w0) # R" m]
          by simp
        finally show ?thesis .
      qed
      have pref:
        "sle
          (?D @ q # S)
          (?D @
            shiftr0 d0
              (copies d0
                ((v0, w0) # R) m))"
        by (rule sle_append_cancel[
              THEN iffD2, OF hsle])
      show
        "sle N (M\<lbrakk>m + 1\<rbrakk>)"
        using Neq op pref by simp
    qed
  qed
qed

lemma seqlex_cofinality_of_crux:
  assumes H: AscCrux
  shows SeqlexCofinality
  unfolding SeqlexCofinality_def
proof (intro allI impI)
  fix M N
  assume Mst: "ST_PS M"
    and Nst: "ST_PS N"
    and sl: "seqlex N M"
  show
    "\<exists>n. 1 \<le> n \<and>
      sle N (M\<lbrakk>n\<rbrakk>)"
  proof (cases "length M - 1 = 0")
    case True
    show ?thesis
      by (rule seqlex_cof_short[OF True sl])
  next
    case False
    have L: "1 < length M"
      using False by presburger
    show ?thesis
    proof (cases
      "entry M 0 (length M - 1) = 0 \<and>
       entry M 1 (length M - 1) = 0")
      case True
      show ?thesis
        by (rule seqlex_cof_zero[
              OF L True sl])
    next
      case False
      show ?thesis
        by (rule seqlex_cof_bad[
              OF H Mst Nst L False sl])
    qed
  qed
qed

lemma pss_cofinality_of_crux:
  assumes H: AscCrux1
    and Mst: "ST_PS M"
    and Nst: "ST_PS N"
    and lt: "translate N <o translate M"
  shows
    "\<exists>n. 1 \<le> n \<and>
      translate N \<le>o
        translate (M\<lbrakk>n\<rbrakk>)"
proof -
  have crux: AscCrux
    by (rule asc_head_step[OF H])
  have cof: SeqlexCofinality
    by (rule seqlex_cofinality_of_crux[
          OF crux])
  show ?thesis
    by (rule pss_cofinality_of_seqlex[
          OF cof Mst Nst lt])
qed

lemma pss_cofinality_of_argdom:
  assumes H: AscArgDom
    and Mst: "ST_PS M"
    and Nst: "ST_PS N"
    and lt: "translate N <o translate M"
  shows
    "\<exists>n. 1 \<le> n \<and>
      translate N \<le>o
        translate (M\<lbrakk>n\<rbrakk>)"
proof -
  have crux1: AscCrux1
    by (rule asc_crux1_of_argdom[OF H])
  show ?thesis
    by (rule pss_cofinality_of_crux[
          OF crux1 Mst Nst lt])
qed

end
