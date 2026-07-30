theory ArgDom
  imports Cofinality "HOL-Library.Sublist"
begin

lemma seqlex_of_sle_not_prefix:
  assumes h: "sle X (W @ Y)"
    and hnp: "\<forall>X'. X \<noteq> W @ X'"
  shows "seqlex X (W @ Y')"
  using h hnp
proof (induction W arbitrary: X Y Y')
  case Nil
  have False
    using Nil.prems(2)[rule_format, of X]
    by simp
  then show ?case by blast
next
  case (Cons w W)
  show ?case
  proof (cases X)
    case Nil
    then show ?thesis by simp
  next
    case (Cons x Xs)
    have hsle:
      "sle (x # Xs)
        (w # (W @ Y))"
      using Cons.prems(1) Cons by simp
    have cases:
      "x # Xs = w # (W @ Y) \<or>
        seqlex (x # Xs)
          (w # (W @ Y))"
      using hsle unfolding sle_def .
    from cases show ?thesis
    proof
      assume eq:
        "x # Xs = w # (W @ Y)"
      have "X = (w # W) @ Y"
        using Cons eq by simp
      then have False
        using Cons.prems(2)[rule_format, of Y]
        by simp
      then show ?thesis by blast
    next
      assume sl:
        "seqlex (x # Xs)
          (w # (W @ Y))"
      have headCases:
        "pairlt x w \<or>
          (x = w \<and>
            seqlex Xs (W @ Y))"
        using sl by simp
      from headCases show ?thesis
      proof
        assume xw: "pairlt x w"
        show ?thesis using Cons xw by simp
      next
        assume rest:
          "x = w \<and>
            seqlex Xs (W @ Y)"
        have tailnp:
          "\<forall>Z. Xs \<noteq> W @ Z"
        proof (intro allI notI)
          fix Z
          assume eq: "Xs = W @ Z"
          have "X = (w # W) @ Z"
            using Cons rest eq by simp
          then show False
            using Cons.prems(2)[rule_format, of Z]
            by simp
        qed
        have tail:
          "seqlex Xs (W @ Y')"
        proof (rule Cons.IH)
          show "sle Xs (W @ Y)"
            using rest unfolding sle_def by simp
          show "\<forall>Z. Xs \<noteq> W @ Z"
            by (rule tailnp)
        qed
        show ?thesis using Cons rest tail by simp
      qed
    qed
  qed
qed

lemma peel_aux:
  assumes len: "length X \<le> n"
    and h:
      "sle X
        (Q @ (a, w) #
          shiftr0 d (X @ A2))"
  shows
    "\<exists>m.
      sle X
        (Q @
          copies d
            ((a, w) # shiftr0 d Q) m)"
  using len h
proof (induction n arbitrary: X Q A2 a)
  case 0
  have Xnil: "X = []"
    using "0.prems"(1) by simp
  show ?case
  proof (intro exI[of _ 0])
    show
      "sle X
        (Q @
          copies d
            ((a, w) # shiftr0 d Q) 0)"
      using Xnil
      unfolding sle_def
      by (cases Q) simp_all
  qed
next
  case (Suc n)
  show ?case
  proof (cases
    "\<exists>X'. X = Q @ (a, w) # X'")
    case True
    then obtain X' where Xeq:
      "X = Q @ (a, w) # X'"
      by blast
    have hc:
      "sle ((a, w) # X')
        ((a, w) #
          shiftr0 d
            ((Q @ (a, w) # X') @ A2))"
    proof -
      have
        "sle
          (Q @ ((a, w) # X'))
          (Q @
            ((a, w) #
              shiftr0 d
                ((Q @ (a, w) # X') @ A2)))"
        using Suc.prems(2) Xeq by simp
      then show ?thesis
        by (rule sle_append_cancel[
              THEN iffD1])
    qed
    have hc2:
      "sle X'
        (shiftr0 d
          ((Q @ (a, w) # X') @ A2))"
    proof -
      have
        "sle
          ([(a, w)] @ X')
          ([(a, w)] @
            shiftr0 d
              ((Q @ (a, w) # X') @ A2))"
        using hc by simp
      then show ?thesis
        by (rule sle_append_cancel[
              THEN iffD1])
    qed
    have shift:
      "shiftr0 d
        ((Q @ (a, w) # X') @ A2) =
        shiftr0 d Q @
          (a + d, w) #
            shiftr0 d (X' @ A2)"
      unfolding shiftr0_def by simp
    have hstep:
      "sle X'
        (shiftr0 d Q @
          (a + d, w) #
            shiftr0 d (X' @ A2))"
      using hc2 shift by simp
    have len':
      "length X' \<le> n"
    proof -
      have
        "length Q + 1 + length X'
          \<le> Suc n"
        using Suc.prems(1) Xeq by simp
      then show ?thesis by presburger
    qed
    have mex:
      "\<exists>m.
        sle X'
          (shiftr0 d Q @
            copies d
              ((a + d, w) #
                shiftr0 d
                  (shiftr0 d Q)) m)"
    proof (rule Suc.IH)
      show "length X' \<le> n" by (rule len')
      show
        "sle X'
          (shiftr0 d Q @
            (a + d, w) #
              shiftr0 d (X' @ A2))"
        by (rule hstep)
    qed
    then obtain m where hm:
      "sle X'
        (shiftr0 d Q @
          copies d
            ((a + d, w) #
              shiftr0 d
                (shiftr0 d Q)) m)"
      by blast
    let ?blk =
      "(a, w) # shiftr0 d Q"
    have cp:
      "copies d ?blk (m + 1) =
        ?blk @
          shiftr0 d
            (copies d ?blk m)"
      by (rule copies_succ_front)
    have shcp:
      "shiftr0 d
        (copies d ?blk m) =
        copies d
          (shiftr0 d ?blk) m"
      by (rule shiftr0_copies)
    have shblk:
      "shiftr0 d ?blk =
        (a + d, w) #
          shiftr0 d (shiftr0 d Q)"
      unfolding shiftr0_def by simp
    have target:
      "Q @ copies d ?blk (m + 1) =
        (Q @ [(a, w)]) @
          (shiftr0 d Q @
            copies d
              ((a + d, w) #
                shiftr0 d
                  (shiftr0 d Q)) m)"
      using cp shcp shblk by simp
    show ?thesis
    proof (intro exI[of _ "m + 1"])
      have pref:
        "sle
          ((Q @ [(a, w)]) @ X')
          ((Q @ [(a, w)]) @
            (shiftr0 d Q @
              copies d
                ((a + d, w) #
                  shiftr0 d
                    (shiftr0 d Q)) m))"
        by (rule sle_append_cancel[
              THEN iffD2, OF hm])
      show
        "sle X
          (Q @
            copies d
              ((a, w) # shiftr0 d Q)
              (m + 1))"
        using Xeq target pref by simp
    qed
  next
    case False
    let ?W = "Q @ [(a, w)]"
    have hW:
      "sle X
        (?W @ shiftr0 d (X @ A2))"
      using Suc.prems(2) by simp
    have hnp:
      "\<forall>X'. X \<noteq> ?W @ X'"
    proof (intro allI notI)
      fix X'
      assume eq: "X = ?W @ X'"
      have "X = Q @ (a, w) # X'"
        using eq by simp
      then show False using False by blast
    qed
    have sl:
      "seqlex X (?W @ shiftr0 d Q)"
      by (rule seqlex_of_sle_not_prefix[
            OF hW hnp])
    show ?thesis
    proof (intro exI[of _ 1])
      have cp:
        "copies d
          ((a, w) # shiftr0 d Q) 1 =
          (a, w) # shiftr0 d Q"
        by (rule copies_one)
      have
        "seqlex X
          (Q @
            copies d
              ((a, w) #
                shiftr0 d Q) 1)"
        using sl cp by simp
      then show
        "sle X
          (Q @
            copies d
              ((a, w) #
                shiftr0 d Q) 1)"
        unfolding sle_def by simp
    qed
  qed
qed

lemma sle_take_of_short:
  assumes h: "sle X (Pr @ Y)"
    and len: "length X \<le> length Pr"
  shows "sle X Pr"
  using h len
proof (induction Pr arbitrary: X Y)
  case Nil
  have "X = []" using Nil.prems(2) by simp
  then show ?case
    unfolding sle_def by simp
next
  case (Cons p Ps)
  show ?case
  proof (cases X)
    case Nil
    then show ?thesis
      unfolding sle_def by simp
  next
    case (Cons x Xs)
    have lenTail:
      "length Xs \<le> length Ps"
      using Cons.prems(2) Cons by simp
    have hsle:
      "sle (x # Xs)
        (p # (Ps @ Y))"
      using Cons.prems(1) Cons by simp
    have cases:
      "x # Xs = p # (Ps @ Y) \<or>
        seqlex (x # Xs)
          (p # (Ps @ Y))"
      using hsle unfolding sle_def .
    from cases show ?thesis
    proof
      assume eq:
        "x # Xs = p # (Ps @ Y)"
      have xp: "x = p" using eq by simp
      have tails: "Xs = Ps @ Y"
        using eq by simp
      have lens:
        "length Xs =
          length Ps + length Y"
        using tails by simp
      have "length Y = 0"
        using lenTail lens by presburger
      then have "Y = []" by simp
      with tails xp Cons show ?thesis
        unfolding sle_def by simp
    next
      assume sl:
        "seqlex (x # Xs)
          (p # (Ps @ Y))"
      have heads:
        "pairlt x p \<or>
          (x = p \<and>
            seqlex Xs (Ps @ Y))"
        using sl by simp
      from heads show ?thesis
      proof
        assume xp: "pairlt x p"
        have "seqlex X (p # Ps)"
          using Cons xp by simp
        then show ?thesis
          unfolding sle_def by simp
      next
        assume rest:
          "x = p \<and>
            seqlex Xs (Ps @ Y)"
        have tailSle: "sle Xs Ps"
        proof (rule Cons.IH)
          show "sle Xs (Ps @ Y)"
            using rest unfolding sle_def by simp
          show "length Xs \<le> length Ps"
            by (rule lenTail)
        qed
        have tailCases:
          "Xs = Ps \<or> seqlex Xs Ps"
          using tailSle unfolding sle_def .
        from tailCases show ?thesis
        proof
          assume "Xs = Ps"
          then have "X = p # Ps"
            using Cons rest by simp
          then show ?thesis
            unfolding sle_def by simp
        next
          assume tail: "seqlex Xs Ps"
          have "seqlex X (p # Ps)"
            using Cons rest tail by simp
          then show ?thesis
            unfolding sle_def by simp
        qed
      qed
    qed
  qed
qed

lemma sle_trans:
  assumes h1: "sle A B"
    and h2: "sle B C"
  shows "sle A C"
proof -
  have cases:
    "A = B \<or> seqlex A B"
    using h1 unfolding sle_def .
  from cases show ?thesis
  proof
    assume "A = B"
    then show ?thesis using h2 by simp
  next
    assume sl: "seqlex A B"
    have "seqlex A C"
      by (rule seqlex_sle_trans[OF sl h2])
    then show ?thesis
      unfolding sle_def by simp
  qed
qed

lemma sle_of_append_left:
  assumes h: "sle (X @ Y) W"
  shows "sle X W"
proof -
  have prefix: "sle X (X @ Y)"
    by (rule sle_append_mono[OF sle_refl])
  show ?thesis
    by (rule sle_trans[OF prefix h])
qed

lemma shiftr0_injective:
  assumes h: "shiftr0 d X = shiftr0 d Y"
  shows "X = Y"
  using h
proof (induction X arbitrary: Y)
  case Nil
  have "shiftr0 d Y = []"
    using Nil.prems by simp
  then have "Y = []" by simp
  then show ?case by simp
next
  case (Cons x X)
  show ?case
  proof (cases Y)
    case Nil
    then show ?thesis using Cons.prems
      unfolding shiftr0_def by simp
  next
    case (Cons y Y')
    have heads:
      "(fst x + d, snd x) =
        (fst y + d, snd y)"
      using Cons.prems Cons
      by (simp add: shiftr0_cons)
    have xy: "x = y"
      using heads
      by (cases x; cases y) simp
    have tails:
      "shiftr0 d X = shiftr0 d Y'"
      using Cons.prems Cons
      by (simp add: shiftr0_cons)
    have "X = Y'"
      by (rule Cons.IH[OF tails])
    then show ?thesis using Cons xy by simp
  qed
qed

lemma seqlex_shiftr0:
  "seqlex (shiftr0 d X)
    (shiftr0 d Y) \<longleftrightarrow>
   seqlex X Y"
proof (induction X arbitrary: Y)
  case Nil
  then show ?case
    by (cases Y) (simp_all add: shiftr0_def)
next
  case (Cons x X)
  show ?case
  proof (cases Y)
    case Nil
    then show ?thesis
      by (simp add: shiftr0_def)
  next
    case (Cons y Y')
    have pair:
      "pairlt
        (fst x + d, snd x)
        (fst y + d, snd y)
        \<longleftrightarrow> pairlt x y"
      unfolding pairlt_def by simp
    have eq:
      "(fst x + d, snd x) =
        (fst y + d, snd y)
        \<longleftrightarrow> x = y"
      by (cases x; cases y) simp
    show ?thesis
      using Cons.IH[of Y'] Cons pair eq
      by (simp add: shiftr0_cons)
  qed
qed

lemma sle_shiftr0:
  "sle (shiftr0 d X)
      (shiftr0 d Y)
    \<longleftrightarrow> sle X Y"
proof
  assume h:
    "sle (shiftr0 d X)
      (shiftr0 d Y)"
  have cases:
    "shiftr0 d X = shiftr0 d Y \<or>
      seqlex (shiftr0 d X)
        (shiftr0 d Y)"
    using h unfolding sle_def .
  from cases show "sle X Y"
  proof
    assume eq: "shiftr0 d X = shiftr0 d Y"
    have "X = Y"
      by (rule shiftr0_injective[OF eq])
    then show ?thesis unfolding sle_def by simp
  next
    assume sl:
      "seqlex (shiftr0 d X)
        (shiftr0 d Y)"
    have "seqlex X Y"
      using sl seqlex_shiftr0[of d X Y]
      by simp
    then show ?thesis unfolding sle_def by simp
  qed
next
  assume h: "sle X Y"
  from h show
    "sle (shiftr0 d X)
      (shiftr0 d Y)"
  proof (cases rule: disjE[OF h[unfolded sle_def]])
    case 1
    then show ?thesis
      unfolding sle_def by simp
  next
    case 2
    have
      "seqlex (shiftr0 d X)
        (shiftr0 d Y)"
      using 2 seqlex_shiftr0[of d X Y]
      by simp
    then show ?thesis unfolding sle_def by simp
  qed
qed

definition SpineOK ::
  "pairseq \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "SpineOK A L w \<longleftrightarrow>
    (\<forall>U V x.
      A = U @ x # V \<longrightarrow>
      fst x < L \<longrightarrow>
      (\<forall>y\<in>set V. fst x < fst y)
        \<longrightarrow>
      w \<le> snd x)"

definition ArgDomCore :: bool where
  "ArgDomCore \<longleftrightarrow>
    (\<forall>X A1 B A2 Z u w e.
      ST_PS
        ((X @
          (u, w) #
            (A1 @
              (u + e, w) #
                (B @ A2))) @ Z)
        \<longrightarrow>
      0 < e \<longrightarrow>
      (\<forall>x\<in>set A1. u < fst x)
        \<longrightarrow>
      (\<forall>x\<in>set B.
        u + e < fst x) \<longrightarrow>
      (\<forall>x\<in>set A2. u < fst x)
        \<longrightarrow>
      (A2 = [] \<or>
        fst (hd A2) \<le> u + e)
        \<longrightarrow>
      (Z = [] \<or>
        fst (hd Z) \<le> u)
        \<longrightarrow>
      SpineOK A1 (u + e) w
        \<longrightarrow>
      sle B
        (shiftr0 e
          (A1 @
            (u + e, w) #
              (B @ A2))))"

lemma spineOK_of_nextrel1_strict_raw:
  assumes hnr:
    "nextrel1
      ((G @ ((v0, w0) # R)) @
        [(v0 + d0, w0 + 1)])
      (length G)
      (length (G @ ((v0, w0) # R)))"
  shows "SpineOK R (v0 + d0) (w0 + 1)"
  unfolding SpineOK_def
proof (intro allI impI)
  fix U V x
  assume Req: "R = U @ x # V"
    and xlt: "fst x < v0 + d0"
    and Vgt: "\<forall>y\<in>set V. fst x < fst y"
  let ?lp = "(v0 + d0, w0 + 1)"
  let ?M =
    "(G @ ((v0, w0) # R)) @ [?lp]"
  let ?A = "G @ ((v0, w0) # U)"
  have hle0:
    "le0 ?M
      (length G)
      (length (G @ ((v0, w0) # R)))"
    and hmin:
      "\<forall>j.
        length G < j \<and>
          le0 ?M j
            (length
              (G @ ((v0, w0) # R)))
        \<longrightarrow>
        entry ?M 1
            (length
              (G @ ((v0, w0) # R)))
          \<le> entry ?M 1 j"
    using hnr unfolding nextrel1_def by blast+
  have Meq:
    "?M = ?A @ (x # (V @ [?lp]))"
    using Req by simp
  have Alen:
    "length ?A =
      length G + 1 + length U"
    by simp
  have hostlen:
    "length (G @ ((v0, w0) # R)) =
      length ?A + 1 + length V"
    using Req Alen by simp
  have gx:
    "nth_default (0, 0) ?M
      (length ?A) = x"
  proof -
    have get:
      "nth_default (0, 0)
          (?A @ (x # (V @ [?lp])))
          (length ?A + 0) =
        nth_default (0, 0)
          (x # (V @ [?lp])) 0"
      by (rule getD_append_right')
    show ?thesis using get Meq by simp
  qed
  have pivot:
    "\<forall>y.
      length ?A < y \<longrightarrow>
      y \<le>
        length (G @ ((v0, w0) # R))
      \<longrightarrow>
      entry ?M 0 (length ?A) <
        entry ?M 0 y"
  proof (intro allI impI)
    fix y
    assume Ay: "length ?A < y"
      and yhost:
        "y \<le>
          length (G @ ((v0, w0) # R))"
    let ?t = "y - length ?A - 1"
    have yeq:
      "y = length ?A + (?t + 1)"
      using Ay by presburger
    have gy:
      "nth_default (0, 0) ?M
          (length ?A + (?t + 1)) =
        nth_default (0, 0)
          (V @ [?lp]) ?t"
    proof -
      have get:
        "nth_default (0, 0)
            (?A @ (x # (V @ [?lp])))
            (length ?A + (?t + 1)) =
          nth_default (0, 0)
            (x # (V @ [?lp]))
            (?t + 1)"
        by (rule getD_append_right')
      show ?thesis using get Meq by simp
    qed
    have tbound: "?t \<le> length V"
      using yhost yeq hostlen by presburger
    have left:
      "entry ?M 0 (length ?A) = fst x"
      using gx by (simp only: entry_zero)
    have right0:
      "entry ?M 0 y =
        fst
          (nth_default (0, 0)
            (V @ [?lp]) ?t)"
    proof -
      have
        "entry ?M 0 y =
          fst (nth_default (0, 0) ?M y)"
        by (rule entry_zero)
      also have
        "\<dots> =
          fst
            (nth_default (0, 0) ?M
              (length ?A + (?t + 1)))"
        by (rule arg_cong[OF yeq])
      also have
        "\<dots> =
          fst
            (nth_default (0, 0)
              (V @ [?lp]) ?t)"
        by (rule arg_cong[OF gy])
      finally show ?thesis .
    qed
    show
      "entry ?M 0 (length ?A) <
        entry ?M 0 y"
    proof (cases "?t < length V")
      case True
      have mem:
        "nth_default (0, 0) V ?t
          \<in> set V"
      proof -
        have get:
          "nth_default (0, 0) V ?t =
            V ! ?t"
          using True by (simp add: nth_default_nth)
        have nthmem: "V ! ?t \<in> set V"
          by (rule nth_mem[OF True])
        show ?thesis using get nthmem by simp
      qed
      have appendGet:
        "nth_default (0, 0)
          (V @ [?lp]) ?t =
         nth_default (0, 0) V ?t"
        using True
        by (simp add: nth_default_nth nth_append)
      have gt:
        "fst x <
          fst (nth_default (0, 0) V ?t)"
        by (rule Vgt[rule_format, OF mem])
      have right:
        "entry ?M 0 y =
          fst (nth_default (0, 0) V ?t)"
        using right0 appendGet by simp
      show ?thesis using left right gt by simp
    next
      case False
      have teq: "?t = length V"
        using False tbound by simp
      have appendGet:
        "nth_default (0, 0)
          (V @ [?lp]) (length V) = ?lp"
      proof -
        have get:
          "nth_default (0, 0)
              (V @ [?lp])
              (length V + 0) =
            nth_default (0, 0) [?lp] 0"
          by (rule getD_append_right')
        show ?thesis using get by simp
      qed
      have right:
        "entry ?M 0 y = v0 + d0"
        using right0 teq appendGet by simp
      show ?thesis using left right xlt by simp
    qed
  qed
  have Ale:
    "length ?A \<le>
      length (G @ ((v0, w0) # R))"
    using hostlen by simp
  have GA: "length G < length ?A"
    by simp
  have xle0:
    "le0 ?M (length ?A)
      (length (G @ ((v0, w0) # R)))"
    by (rule le0_through_pivot[
          OF hle0 GA Ale pivot])
  have last:
    "entry ?M 1
      (length (G @ ((v0, w0) # R))) =
      w0 + 1"
  proof -
    have get:
      "nth_default (0, 0) ?M
        (length (G @ ((v0, w0) # R))) =
        ?lp"
    proof -
      have
        "nth_default (0, 0)
            ((G @ ((v0, w0) # R)) @ [?lp])
            (length
              (G @ ((v0, w0) # R)) + 0) =
          nth_default (0, 0) [?lp] 0"
        by (rule getD_append_right')
      then show ?thesis by simp
    qed
    have inbounds:
      "length (G @ ((v0, w0) # R)) <
        length ?M"
      by simp
    have nthEq:
      "?M !
        (length (G @ ((v0, w0) # R))) =
        ?lp"
      using get inbounds
      by (simp add: nth_default_nth)
    show ?thesis
      using nthEq inbounds
      unfolding entry_def by simp
  qed
  have min:
    "entry ?M 1
        (length (G @ ((v0, w0) # R)))
      \<le> entry ?M 1 (length ?A)"
    by (rule hmin[rule_format])
       (use GA xle0 in simp)
  have Ainbounds: "length ?A < length ?M"
    using Ale by simp
  have Anth:
    "?M ! (length ?A) = x"
    using gx Ainbounds
    by (simp add: nth_default_nth)
  have atA:
    "entry ?M 1 (length ?A) = snd x"
    using Anth Ainbounds
    unfolding entry_def by simp
  show "w0 + 1 \<le> snd x"
    using min last atA by simp
qed

lemma spineOK_of_nextrel1:
  assumes hnr:
    "nextrel1
      ((G @ ((v0, w0) # R)) @
        [(v0 + d0, w0 + 1)])
      (length G)
      (length (G @ ((v0, w0) # R)))"
  shows "SpineOK R (v0 + d0) w0"
  unfolding SpineOK_def
proof (intro allI impI)
  fix U V x
  assume Req: "R = U @ x # V"
    and xlt: "fst x < v0 + d0"
    and Vgt: "\<forall>y\<in>set V. fst x < fst y"
  have strong:
    "SpineOK R (v0 + d0) (w0 + 1)"
    by (rule spineOK_of_nextrel1_strict_raw[OF hnr])
  have "w0 + 1 \<le> snd x"
    by (rule strong[
          unfolded SpineOK_def,
          rule_format, OF Req xlt Vgt[rule_format]])
  then show "w0 \<le> snd x" by simp
qed

lemma ascArgDom_of_core:
  assumes H: ArgDomCore
  shows AscArgDom
  unfolding AscArgDom_def
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
    and Rgt: "\<forall>x\<in>set R. v0 < fst x"
    and dpos: "0 < d0"
    and hnr:
      "nextrel1
        ((G @ ((v0, w0) # R)) @
          [(v0 + d0, w0 + 1)])
        (length G)
        (length (G @ ((v0, w0) # R)))"
  let ?Shi =
    "takeWhile
      (\<lambda>p. v0 + d0 < fst p) S"
  let ?D =
    "dropWhile
      (\<lambda>p. v0 + d0 < fst p) S"
  let ?A2 =
    "takeWhile (\<lambda>p. v0 < fst p) ?D"
  let ?Z =
    "dropWhile (\<lambda>p. v0 < fst p) ?D"
  have Ssplit: "?Shi @ ?D = S" by simp
  have Dsplit: "?A2 @ ?Z = ?D" by simp
  have Shigt:
    "\<forall>x\<in>set ?Shi. v0 + d0 < fst x"
    using set_takeWhileD by fastforce
  have A2gt:
    "\<forall>x\<in>set ?A2. v0 < fst x"
    using set_takeWhileD by fastforce
  have Dhd:
    "?D = [] \<or>
      fst (hd ?D) \<le> v0 + d0"
  proof (cases "?D = []")
    case True
    then show ?thesis by simp
  next
    case False
    have
      "\<not> v0 + d0 < fst (hd ?D)"
      by (rule hd_dropWhile[OF False])
    then show ?thesis by simp
  qed
  have A2hd:
    "?A2 = [] \<or>
      fst (hd ?A2) \<le> v0 + d0"
  proof (cases "?A2 = []")
    case True
    then show ?thesis by simp
  next
    case False
    have Dne: "?D \<noteq> []"
    proof
      assume "?D = []"
      with False show False by simp
    qed
    obtain y Ys where Deq: "?D = y # Ys"
      using Dne by (cases ?D) auto
    have pred: "v0 < fst y"
    proof (rule ccontr)
      assume "\<not> v0 < fst y"
      then have "?A2 = []"
        using Deq by simp
      with False show False by simp
    qed
    have heads: "hd ?A2 = hd ?D"
      using Deq pred by simp
    have bound: "fst (hd ?D) \<le> v0 + d0"
    proof -
      from Dhd show ?thesis
      proof
        assume "?D = []"
        with Dne show ?thesis by blast
      next
        assume "fst (hd ?D) \<le> v0 + d0"
        then show ?thesis .
      qed
    qed
    show ?thesis using False heads bound by simp
  qed
  have Zhd:
    "?Z = [] \<or> fst (hd ?Z) \<le> v0"
  proof (cases "?Z = []")
    case True
    then show ?thesis by simp
  next
    case False
    have "\<not> v0 < fst (hd ?Z)"
      by (rule hd_dropWhile[OF False])
    then show ?thesis by simp
  qed
  have Neq:
    "(G @ ((v0, w0) # R)) @
        (v0 + d0, w0) # S =
      (G @
        (v0, w0) #
          (R @
            (v0 + d0, w0) #
              (?Shi @ ?A2))) @ ?Z"
    using Ssplit Dsplit by simp
  have Ncore:
    "ST_PS
      ((G @
        (v0, w0) #
          (R @
            (v0 + d0, w0) #
              (?Shi @ ?A2))) @ ?Z)"
    using hN Neq by simp
  have spine: "SpineOK R (v0 + d0) w0"
    by (rule spineOK_of_nextrel1[OF hnr])
  have core:
    "sle ?Shi
      (shiftr0 d0
        (R @
          (v0 + d0, w0) #
            (?Shi @ ?A2)))"
    using H[unfolded ArgDomCore_def,
      rule_format,
      OF Ncore dpos Rgt[rule_format]
        Shigt[rule_format] A2gt[rule_format]
        A2hd Zhd spine]
    by blast
  have bound:
    "shiftr0 d0
      (R @
        (v0 + d0, w0) #
          (?Shi @ ?A2)) =
      shiftr0 d0 R @
        (v0 + d0 + d0, w0) #
          shiftr0 d0 (?Shi @ ?A2)"
    unfolding shiftr0_def by simp
  have core':
    "sle ?Shi
      (shiftr0 d0 R @
        (v0 + d0 + d0, w0) #
          shiftr0 d0 (?Shi @ ?A2))"
    using core bound by simp
  have mex:
    "\<exists>m.
      sle ?Shi
        (shiftr0 d0 R @
          copies d0
            ((v0 + d0 + d0, w0) #
              shiftr0 d0
                (shiftr0 d0 R)) m)"
  proof (rule peel_aux[
      where n="length ?Shi"
        and X="?Shi"
        and Q="shiftr0 d0 R"
        and a="v0 + d0 + d0"
        and d=d0 and w=w0])
    show "length ?Shi \<le> length ?Shi" by simp
    show
      "sle ?Shi
        (shiftr0 d0 R @
          (v0 + d0 + d0, w0) #
            shiftr0 d0 (?Shi @ ?A2))"
      by (rule core')
  qed
  then obtain m where hm:
    "sle ?Shi
      (shiftr0 d0 R @
        copies d0
          ((v0 + d0 + d0, w0) #
            shiftr0 d0
              (shiftr0 d0 R)) m)"
    by blast
  have target:
    "shiftr0 d0
      (R @
        copies d0
          (shiftr0 d0
            ((v0, w0) # R)) m) =
      shiftr0 d0 R @
        copies d0
          ((v0 + d0 + d0, w0) #
            shiftr0 d0
              (shiftr0 d0 R)) m"
  proof -
    have append:
      "shiftr0 d0
        (R @
          copies d0
            (shiftr0 d0
              ((v0, w0) # R)) m) =
        shiftr0 d0 R @
          shiftr0 d0
            (copies d0
              (shiftr0 d0
                ((v0, w0) # R)) m)"
      by (rule shiftr0_append)
    have copies:
      "shiftr0 d0
        (copies d0
          (shiftr0 d0
            ((v0, w0) # R)) m) =
       copies d0
        (shiftr0 d0
          (shiftr0 d0
            ((v0, w0) # R))) m"
      by (rule shiftr0_copies)
    have head:
      "shiftr0 d0
        (shiftr0 d0
          ((v0, w0) # R)) =
       (v0 + d0 + d0, w0) #
        shiftr0 d0 (shiftr0 d0 R)"
      unfolding shiftr0_def by simp
    show ?thesis using append copies head by simp
  qed
  show
    "\<exists>m.
      sle ?Shi
        (shiftr0 d0
          (R @
            copies d0
              (shiftr0 d0
                ((v0, w0) # R)) m))"
  proof (intro exI[of _ m])
    show
      "sle ?Shi
        (shiftr0 d0
          (R @
            copies d0
              (shiftr0 d0
                ((v0, w0) # R)) m))"
      using hm target by simp
  qed
qed

lemma pss_cofinality_of_core:
  assumes H: ArgDomCore
    and Mst: "ST_PS M"
    and Nst: "ST_PS N"
    and lt: "translate N <o translate M"
  shows
    "\<exists>n. 1 \<le> n \<and>
      translate N \<le>o
        translate (M\<lbrakk>n\<rbrakk>)"
proof -
  have argdom: AscArgDom
    by (rule ascArgDom_of_core[OF H])
  show ?thesis
    by (rule pss_cofinality_of_argdom[
          OF argdom Mst Nst lt])
qed

definition ArgDomCoreOn ::
  "pairseq \<Rightarrow> bool"
where
  "ArgDomCoreOn N \<longleftrightarrow>
    (\<forall>X A1 B A2 Z u w e.
      N =
        (X @
          (u, w) #
            (A1 @
              (u + e, w) #
                (B @ A2))) @ Z
        \<longrightarrow>
      0 < e \<longrightarrow>
      (\<forall>x\<in>set A1. u < fst x)
        \<longrightarrow>
      (\<forall>x\<in>set B.
        u + e < fst x) \<longrightarrow>
      (\<forall>x\<in>set A2. u < fst x)
        \<longrightarrow>
      (A2 = [] \<or>
        fst (hd A2) \<le> u + e)
        \<longrightarrow>
      (Z = [] \<or> fst (hd Z) \<le> u)
        \<longrightarrow>
      SpineOK A1 (u + e) w
        \<longrightarrow>
      sle B
        (shiftr0 e
          (A1 @
            (u + e, w) #
              (B @ A2))))"

lemma argDomCore_of_on:
  assumes H:
    "\<forall>N. ST_PS N \<longrightarrow>
      ArgDomCoreOn N"
  shows ArgDomCore
  unfolding ArgDomCore_def
proof (intro allI impI)
  fix X A1 B A2 Z u w e
  assume st:
      "ST_PS
        ((X @
          (u, w) #
            (A1 @
              (u + e, w) #
                (B @ A2))) @ Z)"
    and epos: "0 < e"
    and A1gt: "\<forall>x\<in>set A1. u < fst x"
    and Bgt: "\<forall>x\<in>set B. u + e < fst x"
    and A2gt: "\<forall>x\<in>set A2. u < fst x"
    and A2hd:
      "A2 = [] \<or> fst (hd A2) \<le> u + e"
    and Zhd: "Z = [] \<or> fst (hd Z) \<le> u"
    and spine: "SpineOK A1 (u + e) w"
  have on:
    "ArgDomCoreOn
      ((X @
        (u, w) #
          (A1 @
            (u + e, w) #
              (B @ A2))) @ Z)"
    using H[rule_format, OF st] .
  show
    "sle B
      (shiftr0 e
        (A1 @
          (u + e, w) #
            (B @ A2)))"
    using on[unfolded ArgDomCoreOn_def,
      rule_format,
      OF refl epos A1gt[rule_format]
        Bgt[rule_format] A2gt[rule_format]
        A2hd Zhd spine]
    by blast
qed

lemma argdom_pos:
  assumes eq:
    "N =
      (X @
        (u, w) #
          (A1 @
            (u + e, w) #
              (B @ A2))) @ Zs"
  shows
    "nth_default (0, 0) N (length X) =
        (u, w) \<and>
     nth_default (0, 0) N
        (length X + (length A1 + 1)) =
        (u + e, w) \<and>
     length X + (length A1 + 1) <
        length N"
proof -
  have Neq:
    "N =
      X @
        ((u, w) #
          (A1 @
            (u + e, w) #
              ((B @ A2) @ Zs)))"
    using eq by simp
  have first:
    "nth_default (0, 0) N (length X) =
      (u, w)"
  proof -
    have get:
      "nth_default (0, 0)
          (X @
            ((u, w) #
              (A1 @
                (u + e, w) #
                  ((B @ A2) @ Zs))))
          (length X + 0) =
        nth_default (0, 0)
          ((u, w) #
            (A1 @
              (u + e, w) #
                ((B @ A2) @ Zs))) 0"
      by (rule getD_append_right')
    show ?thesis using get Neq by simp
  qed
  have second:
    "nth_default (0, 0) N
        (length X + (length A1 + 1)) =
      (u + e, w)"
  proof -
    have getX:
      "nth_default (0, 0)
          (X @
            ((u, w) #
              (A1 @
                (u + e, w) #
                  ((B @ A2) @ Zs))))
          (length X + (length A1 + 1)) =
        nth_default (0, 0)
          ((u, w) #
            (A1 @
              (u + e, w) #
                ((B @ A2) @ Zs)))
          (length A1 + 1)"
      by (rule getD_append_right')
    have getA:
      "nth_default (0, 0)
          (A1 @
            ((u + e, w) #
              ((B @ A2) @ Zs)))
          (length A1 + 0) =
        nth_default (0, 0)
          ((u + e, w) #
            ((B @ A2) @ Zs)) 0"
      by (rule getD_append_right')
    show ?thesis using Neq getX getA by simp
  qed
  have pos:
    "length X + (length A1 + 1) <
      length N"
    using Neq by simp
  show ?thesis using first second pos by simp
qed

lemma argDomCoreOn_diag:
  "ArgDomCoreOn (diagSeq 0 v)"
  unfolding ArgDomCoreOn_def
proof (intro allI impI)
  fix X A1 B A2 Z u w e
  assume eq:
      "diagSeq 0 v =
        (X @
          (u, w) #
            (A1 @
              (u + e, w) #
                (B @ A2))) @ Z"
    and epos: "0 < e"
    and A1gt: "\<forall>x\<in>set A1. u < fst x"
    and Bgt: "\<forall>x\<in>set B. u + e < fst x"
    and A2gt: "\<forall>x\<in>set A2. u < fst x"
    and A2hd:
      "A2 = [] \<or> fst (hd A2) \<le> u + e"
    and Zhd: "Z = [] \<or> fst (hd Z) \<le> u"
    and spine: "SpineOK A1 (u + e) w"
  note pos = argdom_pos[OF eq]
  have p:
    "nth_default (0, 0)
      (diagSeq 0 v) (length X) =
      (u, w)"
    using pos by simp
  have q:
    "nth_default (0, 0)
      (diagSeq 0 v)
        (length X + (length A1 + 1)) =
      (u + e, w)"
    using pos by simp
  have qlt:
    "length X + (length A1 + 1) <
      length (diagSeq 0 v)"
    using pos by simp
  have plen:
    "length X < v + 1"
    using qlt diagSeq0_length[of v]
    by simp
  have qlen:
    "length X + (length A1 + 1) <
      v + 1"
    using qlt diagSeq0_length[of v]
    by simp
  have pd:
    "nth_default (0, 0)
      (diagSeq 0 v) (length X) =
      (length X, length X)"
    by (rule diagSeq0_getD[OF plen])
  have qd:
    "nth_default (0, 0)
      (diagSeq 0 v)
        (length X + (length A1 + 1)) =
      (length X + (length A1 + 1),
       length X + (length A1 + 1))"
    by (rule diagSeq0_getD[OF qlen])
  have xu: "length X = u"
    using p pd by simp
  have xw: "length X = w"
    using p pd by simp
  have qe:
    "length X + (length A1 + 1) = u + e"
    using q qd by simp
  have qw:
    "length X + (length A1 + 1) = w"
    using q qd by simp
  have False using epos xu xw qe qw by presburger
  then show
    "sle B
      (shiftr0 e
        (A1 @
          (u + e, w) #
            (B @ A2)))"
    by blast
qed

lemma argDomCoreOn_snoc_zero:
  assumes p0: "fst p = 0"
    and H: "ArgDomCoreOn (N @ [p])"
  shows "ArgDomCoreOn N"
  unfolding ArgDomCoreOn_def
proof (intro allI impI)
  fix X A1 B A2 Z u w e
  assume eq:
      "N =
        (X @
          (u, w) #
            (A1 @
              (u + e, w) #
                (B @ A2))) @ Z"
    and epos: "0 < e"
    and A1gt: "\<forall>x\<in>set A1. u < fst x"
    and Bgt: "\<forall>x\<in>set B. u + e < fst x"
    and A2gt: "\<forall>x\<in>set A2. u < fst x"
    and A2hd:
      "A2 = [] \<or> fst (hd A2) \<le> u + e"
    and Zhd: "Z = [] \<or> fst (hd Z) \<le> u"
    and spine: "SpineOK A1 (u + e) w"
  have eq':
    "N @ [p] =
      (X @
        (u, w) #
          (A1 @
            (u + e, w) #
              (B @ A2))) @ (Z @ [p])"
    using eq by simp
  have Zhd':
    "Z @ [p] = [] \<or>
      fst (hd (Z @ [p])) \<le> u"
  proof (cases Z)
    case Nil
    show ?thesis using Nil p0 by simp
  next
    case (Cons z Zs)
    have "fst z \<le> u"
    proof -
      from Zhd show ?thesis
      proof
        assume "Z = []"
        then show ?thesis using Cons by simp
      next
        assume "fst (hd Z) \<le> u"
        then show ?thesis using Cons by simp
      qed
    qed
    then show ?thesis using Cons by simp
  qed
  show
    "sle B
      (shiftr0 e
        (A1 @
          (u + e, w) #
            (B @ A2)))"
    using H[unfolded ArgDomCoreOn_def,
      rule_format,
      OF eq' epos A1gt[rule_format]
        Bgt[rule_format] A2gt[rule_format]
        A2hd Zhd' spine]
    by blast
qed

lemma argDomCoreOn_drop_left:
  assumes H: "ArgDomCoreOn (Pr @ S)"
  shows "ArgDomCoreOn S"
  unfolding ArgDomCoreOn_def
proof (intro allI impI)
  fix X A1 B A2 Z u w e
  assume eq:
      "S =
        (X @
          (u, w) #
            (A1 @
              (u + e, w) #
                (B @ A2))) @ Z"
    and epos: "0 < e"
    and A1gt: "\<forall>x\<in>set A1. u < fst x"
    and Bgt: "\<forall>x\<in>set B. u + e < fst x"
    and A2gt: "\<forall>x\<in>set A2. u < fst x"
    and A2hd:
      "A2 = [] \<or> fst (hd A2) \<le> u + e"
    and Zhd: "Z = [] \<or> fst (hd Z) \<le> u"
    and spine: "SpineOK A1 (u + e) w"
  have eq':
    "Pr @ S =
      ((Pr @ X) @
        (u, w) #
          (A1 @
            (u + e, w) #
              (B @ A2))) @ Z"
    using eq by simp
  show
    "sle B
      (shiftr0 e
        (A1 @
          (u + e, w) #
            (B @ A2)))"
    using H[unfolded ArgDomCoreOn_def,
      rule_format,
      OF eq' epos A1gt[rule_format]
        Bgt[rule_format] A2gt[rule_format]
        A2hd Zhd spine]
    by blast
qed

definition shiftl0 ::
  "nat \<Rightarrow> pairseq \<Rightarrow> pairseq"
where
  "shiftl0 d M =
    map (\<lambda>p. (fst p - d, snd p)) M"

lemma shiftl0_cons:
  "shiftl0 d (p # A) =
    (fst p - d, snd p) # shiftl0 d A"
  unfolding shiftl0_def by simp

lemma shiftl0_append:
  "shiftl0 d (A @ B) =
    shiftl0 d A @ shiftl0 d B"
  unfolding shiftl0_def by simp

lemma mem_shiftl0:
  "x \<in> set (shiftl0 d M) \<longleftrightarrow>
    (\<exists>p\<in>set M.
      (fst p - d, snd p) = x)"
  unfolding shiftl0_def by auto

lemma shiftl0_shiftr0 [simp]:
  "shiftl0 d (shiftr0 d X) = X"
proof (induction X)
  case Nil
  then show ?case
    unfolding shiftl0_def shiftr0_def by simp
next
  case (Cons p X)
  show ?case
    using Cons.IH
    by (cases p)
       (simp add: shiftr0_cons shiftl0_cons)
qed

lemma shiftr0_shiftl0:
  assumes h: "\<forall>x\<in>set L. d \<le> fst x"
  shows "shiftr0 d (shiftl0 d L) = L"
  using h
proof (induction L)
  case Nil
  then show ?case
    unfolding shiftl0_def shiftr0_def by simp
next
  case (Cons p L)
  have pd: "d \<le> fst p"
    by (rule Cons.prems[rule_format]) simp
  have tail:
    "\<forall>x\<in>set L. d \<le> fst x"
  proof (intro ballI)
    fix x
    assume xL: "x \<in> set L"
    show "d \<le> fst x"
      by (rule Cons.prems[rule_format])
         (use xL in simp)
  qed
  have ih:
    "shiftr0 d (shiftl0 d L) = L"
    by (rule Cons.IH[OF tail])
  show ?case
    using pd ih
    by (cases p)
       (simp add: shiftl0_cons shiftr0_cons)
qed

lemma shiftr0_comm:
  "shiftr0 e (shiftr0 d L) =
    shiftr0 d (shiftr0 e L)"
  unfolding shiftr0_def
  by (simp add: map_map o_def add.commute
      add.left_commute)

lemma argDomCoreOn_shiftr0:
  assumes H: "ArgDomCoreOn W"
  shows "ArgDomCoreOn (shiftr0 d W)"
  unfolding ArgDomCoreOn_def
proof (intro allI impI)
  fix X A1 B A2 Z u w e
  assume eq:
      "shiftr0 d W =
        (X @
          (u, w) #
            (A1 @
              (u + e, w) #
                (B @ A2))) @ Z"
    and epos: "0 < e"
    and A1gt: "\<forall>x\<in>set A1. u < fst x"
    and Bgt: "\<forall>x\<in>set B. u + e < fst x"
    and A2gt: "\<forall>x\<in>set A2. u < fst x"
    and A2hd:
      "A2 = [] \<or> fst (hd A2) \<le> u + e"
    and Zhd: "Z = [] \<or> fst (hd Z) \<le> u"
    and spine: "SpineOK A1 (u + e) w"
  let ?whole =
    "(X @
      (u, w) #
        (A1 @
          (u + e, w) #
            (B @ A2))) @ Z"
  have all:
    "\<forall>x\<in>set ?whole. d \<le> fst x"
  proof (intro ballI)
    fix x
    assume xwhole: "x \<in> set ?whole"
    have xshift: "x \<in> set (shiftr0 d W)"
      using eq xwhole by simp
    then obtain q where
      qW: "q \<in> set W"
      and xeq: "(fst q + d, snd q) = x"
      using mem_shiftr0[of x d W] by blast
    have "d \<le> fst q + d" by simp
    then show "d \<le> fst x"
    proof -
      have fx: "fst q + d = fst x"
      proof -
        have
          "fst (fst q + d, snd q) = fst x"
          by (rule arg_cong[OF xeq])
        then show ?thesis by simp
      qed
      show ?thesis using fx by simp
    qed
  qed
  have Xle: "\<forall>x\<in>set X. d \<le> fst x"
  proof (intro ballI)
    fix x
    assume "x \<in> set X"
    then have "x \<in> set ?whole" by simp
    then show "d \<le> fst x"
      by (rule all[rule_format])
  qed
  have A1le: "\<forall>x\<in>set A1. d \<le> fst x"
  proof (intro ballI)
    fix x
    assume "x \<in> set A1"
    then have "x \<in> set ?whole" by simp
    then show "d \<le> fst x"
      by (rule all[rule_format])
  qed
  have Ble: "\<forall>x\<in>set B. d \<le> fst x"
  proof (intro ballI)
    fix x
    assume "x \<in> set B"
    then have "x \<in> set ?whole" by simp
    then show "d \<le> fst x"
      by (rule all[rule_format])
  qed
  have A2le: "\<forall>x\<in>set A2. d \<le> fst x"
  proof (intro ballI)
    fix x
    assume "x \<in> set A2"
    then have "x \<in> set ?whole" by simp
    then show "d \<le> fst x"
      by (rule all[rule_format])
  qed
  have Zle: "\<forall>x\<in>set Z. d \<le> fst x"
  proof (intro ballI)
    fix x
    assume "x \<in> set Z"
    then have "x \<in> set ?whole" by simp
    then show "d \<le> fst x"
      by (rule all[rule_format])
  qed
  have ule: "d \<le> u"
  proof -
    have "(u, w) \<in> set ?whole" by simp
    then show ?thesis
      using all[rule_format, of "(u, w)"]
      by simp
  qed
  let ?X' = "shiftl0 d X"
  let ?A1' = "shiftl0 d A1"
  let ?B' = "shiftl0 d B"
  let ?A2' = "shiftl0 d A2"
  let ?Z' = "shiftl0 d Z"
  have eX: "shiftr0 d ?X' = X"
    by (rule shiftr0_shiftl0[OF Xle])
  have eA1: "shiftr0 d ?A1' = A1"
    by (rule shiftr0_shiftl0[OF A1le])
  have eB: "shiftr0 d ?B' = B"
    by (rule shiftr0_shiftl0[OF Ble])
  have eA2: "shiftr0 d ?A2' = A2"
    by (rule shiftr0_shiftl0[OF A2le])
  have eZ: "shiftr0 d ?Z' = Z"
    by (rule shiftr0_shiftl0[OF Zle])
  have arith: "u + e - d = u - d + e"
    using ule by presburger
  have Weq:
    "W =
      (?X' @
        (u - d, w) #
          (?A1' @
            ((u - d) + e, w) #
              (?B' @ ?A2'))) @ ?Z'"
  proof -
    have pulled:
      "shiftl0 d (shiftr0 d W) =
        shiftl0 d ?whole"
      by (rule arg_cong[OF eq])
    show ?thesis
      using pulled arith
      by (simp add: shiftl0_append
          shiftl0_cons)
  qed
  have g1:
    "\<forall>x\<in>set ?A1'. u - d < fst x"
  proof (intro ballI)
    fix x
    assume x: "x \<in> set ?A1'"
    then obtain q where
      q: "q \<in> set A1"
      and xeq: "(fst q - d, snd q) = x"
      using mem_shiftl0[of x d A1] by blast
    have qgt: "u < fst q"
      by (rule A1gt[rule_format, OF q])
    have qle: "d \<le> fst q"
      by (rule A1le[rule_format, OF q])
    have "u - d < fst q - d"
      using qgt ule qle by presburger
    then show "u - d < fst x"
      using xeq by (cases x) simp
  qed
  have g2:
    "\<forall>x\<in>set ?B'.
      (u - d) + e < fst x"
  proof (intro ballI)
    fix x
    assume x: "x \<in> set ?B'"
    then obtain q where
      q: "q \<in> set B"
      and xeq: "(fst q - d, snd q) = x"
      using mem_shiftl0[of x d B] by blast
    have qgt: "u + e < fst q"
      by (rule Bgt[rule_format, OF q])
    have qle: "d \<le> fst q"
      by (rule Ble[rule_format, OF q])
    have "(u - d) + e < fst q - d"
      using qgt ule qle by presburger
    then show "(u - d) + e < fst x"
      using xeq by (cases x) simp
  qed
  have g3:
    "\<forall>x\<in>set ?A2'. u - d < fst x"
  proof (intro ballI)
    fix x
    assume x: "x \<in> set ?A2'"
    then obtain q where
      q: "q \<in> set A2"
      and xeq: "(fst q - d, snd q) = x"
      using mem_shiftl0[of x d A2] by blast
    have qgt: "u < fst q"
      by (rule A2gt[rule_format, OF q])
    have qle: "d \<le> fst q"
      by (rule A2le[rule_format, OF q])
    have "u - d < fst q - d"
      using qgt ule qle by presburger
    then show "u - d < fst x"
      using xeq by (cases x) simp
  qed
  have g4:
    "?A2' = [] \<or>
      fst (hd ?A2') \<le> (u - d) + e"
  proof (cases A2)
    case Nil
    then show ?thesis
      unfolding shiftl0_def by simp
  next
    case (Cons a As)
    have ahd: "fst a \<le> u + e"
    proof -
      from A2hd show ?thesis
      proof
        assume "A2 = []"
        then show ?thesis using Cons by simp
      next
        assume "fst (hd A2) \<le> u + e"
        then show ?thesis using Cons by simp
      qed
    qed
    have ale: "d \<le> fst a"
      by (rule A2le[rule_format]) (use Cons in simp)
    have "fst a - d \<le> (u - d) + e"
      using ahd ale ule by presburger
    then show ?thesis using Cons
      by (simp add: shiftl0_cons)
  qed
  have g5:
    "?Z' = [] \<or> fst (hd ?Z') \<le> u - d"
  proof (cases Z)
    case Nil
    then show ?thesis
      unfolding shiftl0_def by simp
  next
    case (Cons z Zs)
    have zhd: "fst z \<le> u"
    proof -
      from Zhd show ?thesis
      proof
        assume "Z = []"
        then show ?thesis using Cons by simp
      next
        assume "fst (hd Z) \<le> u"
        then show ?thesis using Cons by simp
      qed
    qed
    have zle: "d \<le> fst z"
      by (rule Zle[rule_format]) (use Cons in simp)
    have "fst z - d \<le> u - d"
      using zhd zle ule by presburger
    then show ?thesis using Cons
      by (simp add: shiftl0_cons)
  qed
  have g6:
    "SpineOK ?A1' ((u - d) + e) w"
    unfolding SpineOK_def
  proof (intro allI impI)
    fix U' V' x'
    assume dec: "?A1' = U' @ x' # V'"
      and xlt: "fst x' < (u - d) + e"
      and Vgt:
        "\<forall>y\<in>set V'. fst x' < fst y"
    have dec':
      "A1 =
        shiftr0 d U' @
          (fst x' + d, snd x') #
            shiftr0 d V'"
    proof -
      have
        "shiftr0 d ?A1' =
          shiftr0 d (U' @ x' # V')"
        by (rule arg_cong[OF dec])
      then show ?thesis
        using eA1
        by (simp add: shiftr0_append
            shiftr0_cons)
    qed
    have shiftedlt: "fst x' + d < u + e"
      using xlt ule by presburger
    have shiftedV:
      "\<forall>y\<in>set (shiftr0 d V').
        fst (fst x' + d, snd x') < fst y"
    proof (intro ballI)
      fix y
      assume y: "y \<in> set (shiftr0 d V')"
      then obtain q where
        q: "q \<in> set V'"
        and yeq: "(fst q + d, snd q) = y"
        using mem_shiftr0[of y d V'] by blast
      have qgt: "fst x' < fst q"
        by (rule Vgt[rule_format, OF q])
      have "fst x' + d < fst q + d"
        using qgt by simp
      then show
        "fst (fst x' + d, snd x') < fst y"
        using yeq by (cases y) simp
    qed
    have raw:
      "w \<le> snd (fst x' + d, snd x')"
    proof (rule spine[
        unfolded SpineOK_def, rule_format])
      show
        "A1 =
          shiftr0 d U' @
            (fst x' + d, snd x') #
              shiftr0 d V'"
        by (rule dec')
      show
        "fst (fst x' + d, snd x') < u + e"
        using shiftedlt by simp
      fix y
      assume y:
        "y \<in> set (shiftr0 d V')"
      show
        "fst (fst x' + d, snd x') < fst y"
        by (rule shiftedV[rule_format, OF y])
    qed
    show "w \<le> snd x'" using raw by simp
  qed
  have hcore:
    "sle ?B'
      (shiftr0 e
        (?A1' @
          ((u - d) + e, w) #
            (?B' @ ?A2')))"
    using H[unfolded ArgDomCoreOn_def,
      rule_format,
      OF Weq epos g1[rule_format]
        g2[rule_format] g3[rule_format]
        g4 g5 g6]
    by blast
  let ?pulled =
    "?A1' @
      ((u - d) + e, w) #
        (?B' @ ?A2')"
  have segment:
    "shiftr0 d ?pulled =
      A1 @ (u + e, w) # (B @ A2)"
  proof -
    have root: "(u - d) + e + d = u + e"
      using ule by presburger
    show ?thesis
      using eA1 eB eA2 root
      by (simp add: shiftr0_append
          shiftr0_cons)
  qed
  have goalEq:
    "shiftr0 e
      (A1 @ (u + e, w) # (B @ A2)) =
     shiftr0 d (shiftr0 e ?pulled)"
  proof -
    have
      "shiftr0 e
        (A1 @ (u + e, w) # (B @ A2)) =
       shiftr0 e (shiftr0 d ?pulled)"
      using segment by simp
    also have "\<dots> =
      shiftr0 d (shiftr0 e ?pulled)"
      by (rule shiftr0_comm)
    finally show ?thesis .
  qed
  have lifted:
    "sle (shiftr0 d ?B')
      (shiftr0 d (shiftr0 e ?pulled))"
    using sle_shiftr0[of d ?B'
      "shiftr0 e ?pulled"]
      hcore by simp
  show
    "sle B
      (shiftr0 e
        (A1 @
          (u + e, w) #
            (B @ A2)))"
    using lifted eB goalEq by simp
qed

lemma split_prefix_left:
  assumes eq: "C @ D = E @ F"
    and len: "length E \<le> length C"
  shows
    "C = E @ drop (length E) C \<and>
     F = drop (length E) C @ D"
proof -
  have take: "take (length E) C = E"
  proof -
    have
      "take (length E) (C @ D) =
        take (length E) (E @ F)"
      by (rule arg_cong[OF eq])
    then show ?thesis using len by simp
  qed
  have C:
    "C = E @ drop (length E) C"
  proof -
    have
      "C =
        take (length E) C @
          drop (length E) C"
      by (rule append_take_drop_id[symmetric])
    then show ?thesis using take by simp
  qed
  have
    "E @ (drop (length E) C @ D) =
      E @ F"
  proof -
    have
      "E @ (drop (length E) C @ D) =
        (E @ drop (length E) C) @ D"
      by simp
    also have "\<dots> = C @ D"
      using C by simp
    also have "\<dots> = E @ F"
      by (rule eq)
    finally show ?thesis .
  qed
  then have
    "drop (length E) C @ D = F"
    by simp
  then show ?thesis using C by simp
qed

lemma split_prefix_right:
  assumes eq: "C @ D = E @ F"
    and len: "length C \<le> length E"
  shows
    "E = C @ drop (length C) E \<and>
     D = drop (length C) E @ F"
  using split_prefix_left[OF eq[symmetric] len]
  by simp

lemma copies_headI:
  assumes ne: "blk \<noteq> []"
    and n1: "1 \<le> n"
  shows "hd (copies d blk n) = hd blk"
proof -
  have mex: "\<exists>m. n = m + 1"
  proof (intro exI[of _ "n - 1"])
    show "n = n - 1 + 1"
      using n1 by presburger
  qed
  then obtain m where neq: "n = m + 1"
    by blast
  have cp:
    "copies d blk n =
      blk @ shiftr0 d (copies d blk m)"
    using copies_succ_front[of d blk m] neq
    by simp
  obtain b bs where blk: "blk = b # bs"
    using ne by (cases blk) auto
  show ?thesis using cp blk by simp
qed

lemma argbound_split:
  "shiftr0 e
      (A1 @
        (u + e, w) # (B @ A2)) =
    (shiftr0 e A1 @
      (u + e + e, w) #
        shiftr0 e B) @
      shiftr0 e A2"
  unfolding shiftr0_def by simp

lemma argbound_len:
  "length B <
    length
      (shiftr0 e A1 @
        (u + e + e, w) #
          shiftr0 e B)"
  using shiftr0_length[of e A1]
    shiftr0_length[of e B]
  by simp

lemma argDomCoreOn_bad_A1:
  assumes Mst: "ST_PS M"
    and Mon: "ArgDomCoreOn M"
    and Meq:
      "M = G @ ((v0, w0) # R) @ [lp]"
    and Rgt: "\<forall>x\<in>set R. v0 < fst x"
    and lpgt: "v0 < fst lp"
    and disj:
      "(d0 = 0 \<and> snd lp = 0 \<and>
          fst lp = v0 + 1) \<or>
       (0 < d0 \<and> snd lp = w0 + 1 \<and>
          fst lp = v0 + d0 \<and>
          nextrel1 M (length G)
            (length M - 1))"
    and STn:
      "\<forall>m. 1 \<le> m \<longrightarrow>
        ST_PS
          (G @ copies d0
            ((v0, w0) # R) m)"
    and IH:
      "\<forall>m. 1 \<le> m \<longrightarrow>
        m < n \<longrightarrow>
        ArgDomCoreOn
          (G @ copies d0
            ((v0, w0) # R) m)"
    and n1: "1 \<le> n"
    and eq:
      "G @ copies d0 ((v0, w0) # R) n =
        (X @
          (u, w) #
            (A1 @
              (u + e, w) #
                (B @ A2))) @ Zs"
    and epos: "0 < e"
    and A1gt: "\<forall>x\<in>set A1. u < fst x"
    and Bgt: "\<forall>x\<in>set B. u + e < fst x"
    and A2gt: "\<forall>x\<in>set A2. u < fst x"
    and A2hd:
      "A2 = [] \<or> fst (hd A2) \<le> u + e"
    and Zhd: "Zs = [] \<or> fst (hd Zs) \<le> u"
    and spine: "SpineOK A1 (u + e) w"
    and layout:
      "length G + (length R + 1) \<le> length X"
  shows
    "sle B
      (shiftr0 e
        (A1 @
          (u + e, w) #
            (B @ A2)))"
proof -
  define m :: nat where "m = n - 1"
  have neq: "n = m + 1"
    unfolding m_def using n1 by presburger
  let ?blk = "(v0, w0) # R"
  let ?P = "G @ ?blk"
  let ?T =
    "(u, w) #
      (A1 @ (u + e, w) # (B @ A2))"
  have Plen:
    "length ?P = length G + (length R + 1)"
    by simp
  have eq':
    "?P @
      shiftr0 d0 (copies d0 ?blk m) =
      X @ (?T @ Zs)"
  proof -
    have cp:
      "copies d0 ?blk (m + 1) =
        ?blk @
          shiftr0 d0
            (copies d0 ?blk m)"
      by (rule copies_succ_front)
    show ?thesis using eq neq cp by simp
  qed
  have PX: "length ?P \<le> length X"
    using layout Plen by simp
  note split = split_prefix_right[OF eq' PX]
  have tailEq:
    "shiftr0 d0 (copies d0 ?blk m) =
      (drop (length ?P) X @ ?T) @ Zs"
    using split by simp
  show ?thesis
  proof (cases "m = 0")
    case True
    have left:
      "shiftr0 d0 (copies d0 ?blk m) = []"
      using True by simp
    have nonempty:
      "(drop (length ?P) X @ ?T) @ Zs
        \<noteq> []"
      by simp
    have False using tailEq left nonempty by simp
    then show ?thesis by blast
  next
    case False
    have m1: "1 \<le> m" using False by simp
    have mn: "m < n" using neq by simp
    have inherited:
      "ArgDomCoreOn
        (G @ copies d0 ?blk m)"
      by (rule IH[rule_format, OF m1 mn])
    have dropped:
      "ArgDomCoreOn (copies d0 ?blk m)"
      by (rule argDomCoreOn_drop_left[
            OF inherited])
    have shifted:
      "ArgDomCoreOn
        (shiftr0 d0
          (copies d0 ?blk m))"
      by (rule argDomCoreOn_shiftr0[
            OF dropped])
    show ?thesis
      using shifted[unfolded ArgDomCoreOn_def,
        rule_format,
        OF tailEq epos A1gt[rule_format]
          Bgt[rule_format] A2gt[rule_format]
          A2hd Zhd spine]
      by blast
  qed
qed

lemma arg_split:
  fixes L :: nat
    and E :: pairseq
  shows "\<exists>Bp Rp.
    E = Bp @ Rp \<and>
    (\<forall>x\<in>set Bp. L < fst x) \<and>
    (Rp = [] \<or> fst (hd Rp) \<le> L)"
proof (induction E)
  case Nil
  show ?case
    by (intro exI[of _ "[]"] exI[of _ "[]"])
       simp
next
  case (Cons a E)
  show ?case
  proof (cases "L < fst a")
    case True
    obtain Bp Rp where
      split: "E = Bp @ Rp"
      and Bpgt: "\<forall>x\<in>set Bp. L < fst x"
      and Rphd:
        "Rp = [] \<or> fst (hd Rp) \<le> L"
      using Cons.IH by blast
    have eqw: "a # E = (a # Bp) @ Rp"
      using split by simp
    have allw:
      "\<forall>x\<in>set (a # Bp). L < fst x"
      using True Bpgt by auto
    show ?thesis using eqw allw Rphd by blast
  next
    case False
    have eqw: "a # E = [] @ (a # E)" by simp
    have allw: "\<forall>x\<in>set []. L < fst x"
      by simp
    have order_iff:
      "(\<not> (L::nat) < fst a) \<longleftrightarrow>
        fst a \<le> L"
      by (rule linorder_not_less)
    have ale: "fst a \<le> L"
      by (rule order_iff[THEN iffD1, OF False])
    have hdw:
      "a # E = [] \<or> fst (hd (a # E)) \<le> L"
      using ale by simp
    show ?thesis using eqw allw hdw by blast
  qed
qed

lemma seqlex_of_sle_snoc':
  assumes h: "sle (X @ [lp]) (V @ E)"
    and qlp: "pairlt q lp"
    and len: "length X < length V"
  shows "seqlex (X @ q # S') (V @ E')"
  using h qlp len
proof (induction X arbitrary: V E lp q S' E')
  case Nil
  obtain v Vs where V: "V = v # Vs"
    using Nil.prems(3) by (cases V) auto
  have hsle:
    "sle [lp] (v # (Vs @ E))"
    using Nil.prems(1) V by simp
  have cases:
    "[lp] = v # (Vs @ E) \<or>
      seqlex [lp] (v # (Vs @ E))"
    using hsle unfolding sle_def .
  have qv: "pairlt q v"
  proof -
    from cases show ?thesis
    proof
      assume eq: "[lp] = v # (Vs @ E)"
      have "lp = v" using eq by simp
      then show ?thesis using Nil.prems(2) by simp
    next
      assume sl:
        "seqlex [lp] (v # (Vs @ E))"
      have
        "pairlt lp v \<or> lp = v"
        using sl by auto
      then show ?thesis
      proof
        assume "pairlt lp v"
        then show ?thesis
          by (rule pairlt_trans[
                OF Nil.prems(2)])
      next
        assume "lp = v"
        then show ?thesis using Nil.prems(2) by simp
      qed
    qed
  qed
  show ?case using V qv by simp
next
  case (Cons x X)
  obtain v Vs where V: "V = v # Vs"
    using Cons.prems(3) by (cases V) auto
  have hsle:
    "sle (x # (X @ [lp]))
      (v # (Vs @ E))"
    using Cons.prems(1) V by simp
  have cases:
    "x # (X @ [lp]) =
        v # (Vs @ E) \<or>
      seqlex (x # (X @ [lp]))
        (v # (Vs @ E))"
    using hsle unfolding sle_def .
  from cases show ?case
  proof
    assume eq:
      "x # (X @ [lp]) =
        v # (Vs @ E)"
    have xv: "x = v" using eq by simp
    have tailEq: "X @ [lp] = Vs @ E"
      using eq by simp
    have tailLen: "length X < length Vs"
      using Cons.prems(3) V by simp
    have tail:
      "seqlex (X @ q # S') (Vs @ E')"
    proof (rule Cons.IH)
      show "sle (X @ [lp]) (Vs @ E)"
        using tailEq unfolding sle_def by simp
      show "pairlt q lp" by (rule Cons.prems(2))
      show "length X < length Vs" by (rule tailLen)
    qed
    show ?thesis using V xv tail by simp
  next
    assume sl:
      "seqlex (x # (X @ [lp]))
        (v # (Vs @ E))"
    have head:
      "pairlt x v \<or>
        (x = v \<and>
          seqlex (X @ [lp]) (Vs @ E))"
      using sl by simp
    from head show ?thesis
    proof
      assume xv: "pairlt x v"
      show ?thesis using V xv by simp
    next
      assume rest:
        "x = v \<and>
          seqlex (X @ [lp]) (Vs @ E)"
      have tailLen: "length X < length Vs"
        using Cons.prems(3) V by simp
      have tail:
        "seqlex (X @ q # S') (Vs @ E')"
      proof (rule Cons.IH)
        show "sle (X @ [lp]) (Vs @ E)"
          using rest unfolding sle_def by simp
        show "pairlt q lp" by (rule Cons.prems(2))
        show "length X < length Vs" by (rule tailLen)
      qed
      show ?thesis using V rest tail by simp
    qed
  qed
qed

lemma argDomCoreOn_bad_B:
  assumes Mst: "ST_PS M"
    and Mon: "ArgDomCoreOn M"
    and Meq:
      "M = G @ ((v0, w0) # R) @ [lp]"
    and Rgt: "\<forall>x\<in>set R. v0 < fst x"
    and lpgt: "v0 < fst lp"
    and disj:
      "(d0 = 0 \<and> snd lp = 0 \<and>
          fst lp = v0 + 1) \<or>
       (0 < d0 \<and> snd lp = w0 + 1 \<and>
          fst lp = v0 + d0 \<and>
          nextrel1 M (length G)
            (length M - 1))"
    and STn:
      "\<forall>m. 1 \<le> m \<longrightarrow>
        ST_PS
          (G @ copies d0
            ((v0, w0) # R) m)"
    and IH:
      "\<forall>m. 1 \<le> m \<longrightarrow>
        m < n \<longrightarrow>
        ArgDomCoreOn
          (G @ copies d0
            ((v0, w0) # R) m)"
    and n1: "1 \<le> n"
    and eq:
      "G @ copies d0 ((v0, w0) # R) n =
        (X @
          (u, w) #
            (A1 @
              (u + e, w) #
                (B @ A2))) @ Zs"
    and epos: "0 < e"
    and A1gt: "\<forall>x\<in>set A1. u < fst x"
    and Bgt: "\<forall>x\<in>set B. u + e < fst x"
    and A2gt: "\<forall>x\<in>set A2. u < fst x"
    and A2hd:
      "A2 = [] \<or> fst (hd A2) \<le> u + e"
    and Zhd: "Zs = [] \<or> fst (hd Zs) \<le> u"
    and spine: "SpineOK A1 (u + e) w"
    and layout:
      "length X + (length A1 + 1) <
        length G + (length R + 1)"
  shows
    "sle B
      (shiftr0 e
        (A1 @
          (u + e, w) #
            (B @ A2)))"
proof -
  define m :: nat where "m = n - 1"
  have neq: "n = m + 1"
    unfolding m_def using n1 by presburger
  let ?blk = "(v0, w0) # R"
  let ?P = "G @ ?blk"
  let ?C =
    "X @
      (u, w) #
        (A1 @ [(u + e, w)])"
  let ?T = "shiftr0 d0 (copies d0 ?blk m)"
  have copy:
    "G @ copies d0 ?blk (m + 1) =
      ?P @ ?T"
    using copies_succ_front[of d0 ?blk m]
    by simp
  have splitEq:
    "?P @ ?T = ?C @ (B @ (A2 @ Zs))"
    using copy eq neq by simp
  have Clen: "length ?C \<le> length ?P"
    using layout by simp
  let ?D = "drop (length ?C) ?P"
  note split = split_prefix_left[OF splitEq Clen]
  have PD: "?P = ?C @ ?D"
    using split by simp
  have BAZ: "B @ (A2 @ Zs) = ?D @ ?T"
    using split by simp
  have Msplit:
    "M = ?C @ (?D @ [lp])"
    using Meq PD by simp
  have key:
    "\<forall>B' A2' Z'.
      ?D @ [lp] = B' @ (A2' @ Z') \<longrightarrow>
      (\<forall>x\<in>set B'. u + e < fst x)
        \<longrightarrow>
      (\<forall>x\<in>set A2'. u < fst x)
        \<longrightarrow>
      (A2' = [] \<or>
        fst (hd A2') \<le> u + e)
        \<longrightarrow>
      (Z' = [] \<or> fst (hd Z') \<le> u)
        \<longrightarrow>
      sle B'
        (shiftr0 e A1 @
          (u + e + e, w) #
            shiftr0 e B')"
  proof (intro allI impI)
    fix B' A2' Z'
    assume Dsplit:
        "?D @ [lp] = B' @ (A2' @ Z')"
      and B'gt:
        "\<forall>x\<in>set B'. u + e < fst x"
      and A2'gt:
        "\<forall>x\<in>set A2'. u < fst x"
      and A2'hd:
        "A2' = [] \<or>
          fst (hd A2') \<le> u + e"
      and Z'hd:
        "Z' = [] \<or> fst (hd Z') \<le> u"
    have Meq':
      "M =
        (X @
          (u, w) #
            (A1 @
              (u + e, w) #
                (B' @ A2'))) @ Z'"
      using Msplit Dsplit by simp
    have core:
      "sle B'
        (shiftr0 e
          (A1 @
            (u + e, w) #
              (B' @ A2')))"
      using Mon[unfolded ArgDomCoreOn_def,
        rule_format,
        OF Meq' epos A1gt[rule_format]
          B'gt[rule_format] A2'gt[rule_format]
          A2'hd Z'hd spine]
      by blast
    have core':
      "sle B'
        ((shiftr0 e A1 @
          (u + e + e, w) #
            shiftr0 e B') @
          shiftr0 e A2')"
      using core argbound_split[
        of e A1 u w B' A2']
      by simp
    have short:
      "length B' \<le>
        length
          (shiftr0 e A1 @
            (u + e + e, w) #
              shiftr0 e B')"
      using argbound_len[of B' e A1 u w]
      by simp
    show
      "sle B'
        (shiftr0 e A1 @
          (u + e + e, w) #
            shiftr0 e B')"
      by (rule sle_take_of_short[OF core' short])
  qed
  have goal_of:
    "sle B
      (shiftr0 e A1 @
        (u + e + e, w) #
          shiftr0 e B)
      \<longrightarrow>
     sle B
      (shiftr0 e
        (A1 @
          (u + e, w) #
            (B @ A2)))"
  proof
    assume h:
      "sle B
        (shiftr0 e A1 @
          (u + e + e, w) #
            shiftr0 e B)"
    have ext:
      "sle B
        ((shiftr0 e A1 @
          (u + e + e, w) #
            shiftr0 e B) @
          shiftr0 e A2)"
      by (rule sle_append_mono[OF h])
    show
      "sle B
        (shiftr0 e
          (A1 @
            (u + e, w) #
              (B @ A2)))"
      using ext argbound_split[
        of e A1 u w B A2]
      by simp
  qed
  show ?thesis
  proof (cases "length B < length ?D")
    case True
    let ?Dr = "drop (length B) ?D"
    have BD: "length B \<le> length ?D"
      using True by simp
    note split2 = split_prefix_right[OF BAZ BD]
    have D: "?D = B @ ?Dr"
      using split2 by simp
    have AZ: "A2 @ Zs = ?Dr @ ?T"
      using split2 by simp
    have Drne: "?Dr \<noteq> []"
    proof
      assume "?Dr = []"
      then have "?D = B" using D by simp
      then show False using True by simp
    qed
    have AZne: "A2 @ Zs \<noteq> []"
    proof
      assume empty: "A2 @ Zs = []"
      have "?Dr @ ?T = []"
        using AZ empty by simp
      then have "?Dr = []" by simp
      then show False using Drne by simp
    qed
    have Drhd: "fst (hd ?Dr) \<le> u + e"
    proof -
      have heads:
        "hd (A2 @ Zs) = hd ?Dr"
      proof -
        have h1:
          "hd (A2 @ Zs) = hd (?Dr @ ?T)"
          by (rule arg_cong[OF AZ])
        have h2: "hd (?Dr @ ?T) = hd ?Dr"
          by (rule headI_append_left[OF Drne])
        show ?thesis using h1 h2 by simp
      qed
      show ?thesis
      proof (cases "A2 = []")
        case True
        have Zne: "Zs \<noteq> []"
          using AZne True by simp
        have Zbound: "fst (hd Zs) \<le> u"
        proof -
          from Zhd show ?thesis
          proof
            assume "Zs = []"
            then show ?thesis using Zne by blast
          next
            assume "fst (hd Zs) \<le> u"
            then show ?thesis .
          qed
        qed
        show ?thesis using heads True Zbound by simp
      next
        case False
        have A2bound:
          "fst (hd A2) \<le> u + e"
        proof -
          from A2hd show ?thesis
          proof
            assume "A2 = []"
            then show ?thesis using False by blast
          next
            assume "fst (hd A2) \<le> u + e"
            then show ?thesis .
          qed
        qed
        show ?thesis
          using heads False A2bound
            headI_append_left by simp
      qed
    qed
    obtain A2' Z' where
      split3: "?Dr @ [lp] = A2' @ Z'"
      and A2'gt:
        "\<forall>x\<in>set A2'. u < fst x"
      and Z'hd:
        "Z' = [] \<or> fst (hd Z') \<le> u"
      using arg_split[
        where L=u and E="?Dr @ [lp]"]
      by blast
    have A2'hd:
      "A2' = [] \<or>
        fst (hd A2') \<le> u + e"
    proof (cases "A2' = []")
      case True
      then show ?thesis by simp
    next
      case False
      have lhs:
        "hd (?Dr @ [lp]) = hd (A2' @ Z')"
        by (rule arg_cong[OF split3])
      have rhs:
        "hd (A2' @ Z') = hd A2'"
        by (rule headI_append_left[OF False])
      have heads:
        "hd (?Dr @ [lp]) = hd A2'"
        using lhs rhs by simp
      have Drapp:
        "hd (?Dr @ [lp]) = hd ?Dr"
        by (rule headI_append_left[OF Drne])
      show ?thesis
        using heads Drapp Drhd by simp
    qed
    have Dsplit:
      "?D @ [lp] = B @ (A2' @ Z')"
      using D split3 by simp
    have host:
      "sle B
        (shiftr0 e A1 @
          (u + e + e, w) #
            shiftr0 e B)"
      by (rule key[rule_format,
            OF Dsplit Bgt[rule_format]
              A2'gt[rule_format] A2'hd Z'hd])
    show ?thesis by (rule goal_of[rule_format, OF host])
  next
    case False
    have DB: "length ?D \<le> length B"
      using False by simp
    let ?B2 = "drop (length ?D) B"
    note split2 = split_prefix_left[OF BAZ DB]
    have B: "B = ?D @ ?B2"
      using split2 by simp
    have T:
      "?T = ?B2 @ (A2 @ Zs)"
      using split2 by simp
    have Dgt:
      "\<forall>x\<in>set ?D. u + e < fst x"
    proof (intro ballI)
      fix x
      assume x: "x \<in> set ?D"
      have xDB: "x \<in> set (?D @ ?B2)"
        using UnI1[OF x] by (simp only: set_append)
      have "x \<in> set B"
        using B xDB by metis
      then show "u + e < fst x"
        by (rule Bgt[rule_format])
    qed
    have head:
      "\<forall>q B2'.
        ?B2 = q # B2' \<longrightarrow>
        q = (v0 + d0, w0)"
    proof (intro allI impI)
      fix q B2'
      assume B2: "?B2 = q # B2'"
      have mne: "m \<noteq> 0"
      proof
        assume "m = 0"
        then have "?T = []" by simp
        moreover have "?T \<noteq> []"
          using T B2 by simp
        ultimately show False by simp
      qed
      define k :: nat where "k = m - 1"
      have meq: "m = k + 1"
        unfolding k_def using mne by presburger
      have cp:
        "copies d0 ?blk m =
          ?blk @
            shiftr0 d0
              (copies d0 ?blk k)"
        using copies_succ_front[of d0 ?blk k]
          meq by simp
      have first:
        "hd ?T = (v0 + d0, w0)"
        using cp
        unfolding shiftr0_def by simp
      have "hd ?T = q"
        using T B2 by simp
      then show "q = (v0 + d0, w0)"
        using first by simp
    qed
    have qle:
      "\<forall>q B2'.
        ?B2 = q # B2' \<longrightarrow>
        fst q \<le> fst lp"
    proof (intro allI impI)
      fix q B2'
      assume B2: "?B2 = q # B2'"
      have qeq: "q = (v0 + d0, w0)"
        by (rule head[rule_format, OF B2])
      from disj show "fst q \<le> fst lp"
      proof
        assume z:
          "d0 = 0 \<and> snd lp = 0 \<and>
            fst lp = v0 + 1"
        show ?thesis using z qeq by simp
      next
        assume a:
          "0 < d0 \<and> snd lp = w0 + 1 \<and>
            fst lp = v0 + d0 \<and>
            nextrel1 M (length G)
              (length M - 1)"
        show ?thesis using a qeq by simp
      qed
    qed
    have qlt:
      "\<forall>q B2'.
        ?B2 = q # B2' \<longrightarrow>
        pairlt q lp"
    proof (intro allI impI)
      fix q B2'
      assume B2: "?B2 = q # B2'"
      have qeq: "q = (v0 + d0, w0)"
        by (rule head[rule_format, OF B2])
      from disj show "pairlt q lp"
      proof
        assume z:
          "d0 = 0 \<and> snd lp = 0 \<and>
            fst lp = v0 + 1"
        show ?thesis using z qeq
          unfolding pairlt_def by simp
      next
        assume a:
          "0 < d0 \<and> snd lp = w0 + 1 \<and>
            fst lp = v0 + d0 \<and>
            nextrel1 M (length G)
              (length M - 1)"
        show ?thesis using a qeq
          unfolding pairlt_def by simp
      qed
    qed
    show ?thesis
    proof (cases "u + e < fst lp")
      case True
      have Dlpgt:
        "\<forall>x\<in>set (?D @ [lp]).
          u + e < fst x"
        using Dgt True by auto
      have host:
        "sle (?D @ [lp])
          (shiftr0 e A1 @
            (u + e + e, w) #
              shiftr0 e (?D @ [lp]))"
        by (rule key[rule_format])
           (use Dlpgt in auto)
      have hostSplit:
        "sle (?D @ [lp])
          ((shiftr0 e A1 @
            (u + e + e, w) #
              shiftr0 e ?D) @
            shiftr0 e [lp])"
        using host
        by (simp add: shiftr0_append)
      show ?thesis
      proof (cases ?B2)
        case Nil
        have Beq: "B = ?D"
          using B Nil by simp
        have left:
          "sle ?D
            ((shiftr0 e A1 @
              (u + e + e, w) #
                shiftr0 e ?D) @
              shiftr0 e [lp])"
          by (rule sle_of_append_left[OF hostSplit])
        have short:
          "length ?D \<le>
            length
              (shiftr0 e A1 @
                (u + e + e, w) #
                  shiftr0 e ?D)"
          using argbound_len[of ?D e A1 u w]
          by simp
        have core:
          "sle ?D
            (shiftr0 e A1 @
              (u + e + e, w) #
                shiftr0 e ?D)"
          by (rule sle_take_of_short[
                OF left short])
        have coreB:
          "sle B
            (shiftr0 e A1 @
              (u + e + e, w) #
                shiftr0 e B)"
          using core Beq by simp
        show ?thesis
          by (rule goal_of[rule_format, OF coreB])
      next
        case (Cons q B2')
        have hlen:
          "length ?D <
            length
              (shiftr0 e A1 @
                (u + e + e, w) #
                  shiftr0 e ?D)"
          using argbound_len[of ?D e A1 u w] .
        have splice:
          "seqlex (?D @ q # B2')
            ((shiftr0 e A1 @
              (u + e + e, w) #
                shiftr0 e ?D) @
              (fst q + e, snd q) #
                shiftr0 e B2')"
          by (rule seqlex_of_sle_snoc'[
                OF hostSplit
                  qlt[rule_format, OF Cons]
                  hlen])
        have Beq: "B = ?D @ q # B2'"
          using B Cons by simp
        have target:
          "shiftr0 e A1 @
              (u + e + e, w) #
                shiftr0 e B =
            (shiftr0 e A1 @
              (u + e + e, w) #
                shiftr0 e ?D) @
              (fst q + e, snd q) #
                shiftr0 e B2'"
          using Beq
          unfolding shiftr0_def by simp
        have core:
          "sle B
            (shiftr0 e A1 @
              (u + e + e, w) #
                shiftr0 e B)"
          using splice Beq target
          unfolding sle_def by simp
        show ?thesis
          by (rule goal_of[rule_format, OF core])
      qed
    next
      case False
      have lple: "fst lp \<le> u + e"
      proof -
        have iff:
          "(\<not> u + e < fst lp) \<longleftrightarrow>
            fst lp \<le> u + e"
          by (rule linorder_not_less)
        show ?thesis
          by (rule iff[THEN iffD1, OF False])
      qed
      have B2nil: "?B2 = []"
      proof (cases ?B2)
        case Nil
        then show ?thesis .
      next
        case (Cons q B2')
        have qB: "q \<in> set B"
          using B Cons by simp
        have qgt: "u + e < fst q"
          by (rule Bgt[rule_format, OF qB])
        have qlp: "fst q \<le> fst lp"
          by (rule qle[rule_format, OF Cons])
        have qstrict: "u + e < fst lp"
          by (rule less_le_trans[OF qgt qlp])
        have False
          using qstrict lple by simp
        then show ?thesis by blast
      qed
      have Beq: "B = ?D"
        using B B2nil by simp
      show ?thesis
      proof (cases "u < fst lp")
        case True
        have ksplit:
          "?D @ [lp] = B @ ([lp] @ [])"
          using Beq by simp
        have kBgt:
          "\<forall>x\<in>set B. u + e < fst x"
          by (rule Bgt)
        have kA2gt:
          "\<forall>x\<in>set [lp]. u < fst x"
          using True by simp
        have kA2hd:
          "[lp] = [] \<or>
            fst (hd [lp]) \<le> u + e"
          using lple by simp
        have kZhd:
          "[] = [] \<or> fst (hd []) \<le> u"
          by simp
        have host:
          "sle B
            (shiftr0 e A1 @
              (u + e + e, w) #
                shiftr0 e B)"
          by (rule key[rule_format,
                OF ksplit kBgt[rule_format]
                  kA2gt[rule_format] kA2hd kZhd])
        show ?thesis
          by (rule goal_of[rule_format, OF host])
      next
        case False
        have ule: "fst lp \<le> u"
        proof -
          have iff:
            "(\<not> u < fst lp) \<longleftrightarrow>
              fst lp \<le> u"
            by (rule linorder_not_less)
          show ?thesis
            by (rule iff[THEN iffD1, OF False])
        qed
        have ksplit:
          "?D @ [lp] = B @ ([] @ [lp])"
          using Beq by simp
        have kBgt:
          "\<forall>x\<in>set B. u + e < fst x"
          by (rule Bgt)
        have kA2gt:
          "\<forall>x\<in>set []. u < fst x"
          by simp
        have kA2hd:
          "[] = [] \<or>
            fst (hd []) \<le> u + e"
          by simp
        have kZhd:
          "[lp] = [] \<or> fst (hd [lp]) \<le> u"
          using ule by simp
        have host:
          "sle B
            (shiftr0 e A1 @
              (u + e + e, w) #
                shiftr0 e B)"
          by (rule key[rule_format,
                OF ksplit kBgt[rule_format]
                  kA2gt[rule_format] kA2hd kZhd])
        show ?thesis
          by (rule goal_of[rule_format, OF host])
      qed
    qed
  qed
qed

lemma shiftr0_add:
  "shiftr0 (a + b) X =
    shiftr0 a (shiftr0 b X)"
  unfolding shiftr0_def
  by (induction X)
     (auto simp: add.assoc add.commute
       add.left_commute)

lemma sle_of_prefix:
  assumes h: "prefix X Y"
  shows "sle X Y"
proof -
  obtain T where Y: "Y = X @ T"
    using h by (rule prefixE)
  show ?thesis
  proof (cases T)
    case Nil
    then show ?thesis
      using Y unfolding sle_def by simp
  next
    case (Cons a T')
    have "seqlex X (X @ T)"
      by (rule seqlex_prefix)
         (use Cons in simp)
    then show ?thesis
      using Y unfolding sle_def by simp
  qed
qed

lemma shiftr0_prefix:
  assumes h: "prefix X Y"
  shows "prefix (shiftr0 d X) (shiftr0 d Y)"
proof -
  obtain T where Y: "Y = X @ T"
    using h by (rule prefixE)
  show ?thesis
    unfolding Y shiftr0_append
    by (rule prefixI) simp
qed

lemma prefix_append_left:
  assumes h: "prefix X Y"
  shows "prefix (Pr @ X) (Pr @ Y)"
  using h by simp

lemma copies_length:
  "length (copies d blk n) =
    n * length blk"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have cp:
    "copies d blk (Suc n) =
      blk @ shiftr0 d (copies d blk n)"
    using copies_succ_front[of d blk n]
    by simp
  have len:
    "length (copies d blk (Suc n)) =
      length blk +
        length (copies d blk n)"
    using cp by (simp add: shiftr0_length)
  show ?case
    using len Suc.IH by simp
qed

lemma split_append_left:
  assumes h: "C @ D = E @ F"
    and hle: "length E \<le> length C"
  shows
    "\<exists>K. C = E @ K \<and> F = K @ D"
  using split_prefix_left[OF h hle]
  by blast

lemma prefix_cons_append:
  assumes h: "prefix Pr Q"
  shows
    "prefix (A @ c # Pr) (A @ c # Q)"
  using h by simp

lemma spineOK_of_nextrel1_strict:
  assumes hnr:
    "nextrel1
      ((G @ ((v0, w0) # R)) @
        [(v0 + d0, w0 + 1)])
      (length G)
      (length (G @ ((v0, w0) # R)))"
  shows "SpineOK R (v0 + d0) (w0 + 1)"
  by (rule spineOK_of_nextrel1_strict_raw[OF hnr])

lemma argDomCoreOn_bad_A2:
  assumes hM: "ST_PS M"
    and hMon: "ArgDomCoreOn M"
    and hMeq:
      "M = (G @ ((v0, w0) # R)) @ [lp]"
    and hRgt: "\<forall>x\<in>set R. v0 < fst x"
    and hlp: "v0 < fst lp"
    and hdisj:
      "(d0 = 0 \<and> snd lp = 0 \<and>
          fst lp = v0 + 1) \<or>
       (0 < d0 \<and> snd lp = w0 + 1 \<and>
          fst lp = v0 + d0 \<and>
          nextrel1 M (length G)
            (length M - 1))"
    and hSTn:
      "\<forall>m. 1 \<le> m \<longrightarrow>
        ST_PS
          (G @ copies d0
            ((v0, w0) # R) m)"
    and hIH:
      "\<forall>m. 1 \<le> m \<longrightarrow>
        m < n \<longrightarrow>
        ArgDomCoreOn
          (G @ copies d0
            ((v0, w0) # R) m)"
    and hn: "1 \<le> n"
    and heq:
      "G @ copies d0 ((v0, w0) # R) n =
        (X @
          (u, w) #
            (A1 @
              (u + e, w) #
                (B @ A2))) @ Zs"
    and he: "0 < e"
    and h1: "\<forall>x\<in>set A1. u < fst x"
    and h2: "\<forall>x\<in>set B. u + e < fst x"
    and h3: "\<forall>x\<in>set A2. u < fst x"
    and h4:
      "A2 = [] \<or> fst (hd A2) \<le> u + e"
    and h5:
      "Zs = [] \<or> fst (hd Zs) \<le> u"
    and h6: "SpineOK A1 (u + e) w"
    and hcaseL:
      "length X <
        length G + (length R + 1)"
    and hcaseR:
      "length G + (length R + 1) \<le>
        length X + (length A1 + 1)"
  shows
    "sle B
      (shiftr0 e
        (A1 @
          (u + e, w) #
            (B @ A2)))"
proof -
  note hpos = argdom_pos[OF heq]
  have hlenN:
    "length
        (G @ copies d0
          ((v0, w0) # R) n) =
      length G +
        n * (length R + 1)"
    using copies_length[
      of d0 "(v0, w0) # R" n]
    by simp
  have hn2: "2 \<le> n"
  proof (rule ccontr)
    assume not2: "\<not> 2 \<le> n"
    have n1: "n = 1"
      using hn not2 by presburger
    have pos:
      "length X + (length A1 + 1) <
        length
          (G @ copies d0
            ((v0, w0) # R) n)"
      using hpos by blast
    have len1:
      "length
          (G @ copies d0
            ((v0, w0) # R) n) =
        length G + (length R + 1)"
      using hlenN n1 by simp
    show False
      using pos len1 hcaseR
      by presburger
  qed
  have mex: "\<exists>m. n = m + 1"
    by (intro exI[of _ "n - 1"])
       (use hn in presburger)
  then obtain m where neq: "n = m + 1"
    by blast
  have hm1: "1 \<le> m"
    using hn2 neq by presburger
  let ?blk = "(v0, w0) # R"
  let ?tail =
    "shiftr0 d0 (copies d0 ?blk m)"
  have hexp:
    "G @ copies d0 ?blk n =
      (G @ ?blk) @ ?tail"
    using copies_succ_front[
      of d0 ?blk m] neq
    by simp
  have heq2:
    "(G @ ?blk) @ ?tail =
      (X @ [(u, w)]) @
        (A1 @
          (u + e, w) #
            (B @ (A2 @ Zs)))"
    using hexp heq by simp
  have firstLen:
    "length (X @ [(u, w)]) \<le>
      length (G @ ?blk)"
    using hcaseL by simp
  obtain C where
      hC1: "G @ ?blk = (X @ [(u, w)]) @ C"
    and hC2:
      "A1 @
          (u + e, w) #
            (B @ (A2 @ Zs)) =
        C @ ?tail"
    using split_append_left[
      OF heq2 firstLen]
    by blast
  have hClen:
    "length C =
      length G + (length R + 1) -
        (length X + 1)"
  proof -
    note len = arg_cong[OF hC1,
      where f=length]
    show ?thesis using len by simp
  qed
  have CleA:
    "length C \<le> length A1"
    using hcaseR hClen by presburger
  obtain D where
      hD1: "A1 = C @ D"
    and hD2:
      "?tail =
        D @
          (u + e, w) #
            (B @ (A2 @ Zs))"
    using split_append_left[
      OF hC2 CleA]
    by blast
  have hA1len:
    "length A1 = length C + length D"
    using hD1 by simp
  have hDlen:
    "length D = length A1 - length C"
    using hA1len by presburger
  have hmem_ge:
    "\<forall>x\<in>set ?tail. d0 \<le> fst x"
  proof (intro ballI)
    fix x
    assume xt: "x \<in> set ?tail"
    obtain p where
        p: "p \<in> set (copies d0 ?blk m)"
      and px: "(fst p + d0, snd p) = x"
      using xt mem_shiftr0[
        of x d0 "copies d0 ?blk m"]
      by blast
    have fstpx: "fst x = fst p + d0"
    proof -
      have eqfst:
        "fst (fst p + d0, snd p) = fst x"
        by (rule arg_cong[OF px])
      show ?thesis using eqfst by simp
    qed
    show "d0 \<le> fst x"
      using fstpx by simp
  qed
  have hd0le: "d0 \<le> u + e"
  proof -
    have mem:
      "(u + e, w) \<in> set ?tail"
      using hD2 by simp
    have
      "d0 \<le> fst (u + e, w)"
      by (rule hmem_ge[rule_format, OF mem])
    then show ?thesis by simp
  qed
  have hSeq:
    "copies d0 ?blk m =
      shiftl0 d0 D @
        (u + e - d0, w) #
          (shiftl0 d0 B @
            (shiftl0 d0 A2 @
              shiftl0 d0 Zs))"
  proof -
    note shifted =
      arg_cong[OF hD2,
        where f="shiftl0 d0"]
    show ?thesis
      using shifted
      by (simp add: shiftl0_append
          shiftl0_cons)
  qed
  have trich:
      "length X < length G + length D \<or>
       length X = length G + length D \<or>
       length G + length D < length X"
    by presburger
  from trich consider
      (less)
        "length X <
          length G + length D"
    | (equal)
        "length X =
          length G + length D"
    | (greater)
        "length G + length D <
          length X"
    by blast
  then show ?thesis
  proof cases
    case less
    have mex': "\<exists>m'. m = m' + 1"
      by (intro exI[of _ "m - 1"])
         (use hm1 in presburger)
    then obtain m' where meq: "m = m' + 1"
      by blast
    have hpre_blk:
      "prefix ?blk (copies d0 ?blk m)"
      unfolding prefix_def
      using copies_succ_front[
        of d0 ?blk m'] meq
      by blast
    have hpre_SD:
      "prefix (shiftl0 d0 D)
        (copies d0 ?blk m)"
      unfolding prefix_def
      using hSeq by blast
    have hSDlen:
      "length (shiftl0 d0 D) =
        length D"
      unfolding shiftl0_def by simp
    have preXC:
      "prefix (X @ [(u, w)])
        (G @ ?blk)"
      unfolding prefix_def
      using hC1 by blast
    have preBlk:
      "prefix (G @ ?blk)
        (G @ copies d0 ?blk m)"
      by (rule prefix_append_left[
            OF hpre_blk])
    have p1:
      "prefix (X @ [(u, w)])
        (G @ copies d0 ?blk m)"
      by (rule prefix_order.trans[
            OF preXC preBlk])
    have p2:
      "prefix (G @ shiftl0 d0 D)
        (G @ copies d0 ?blk m)"
      by (rule prefix_append_left[
            OF hpre_SD])
    have plen:
      "length (X @ [(u, w)]) \<le>
        length
          (G @ shiftl0 d0 D)"
      using less hSDlen by simp
    have hp1:
      "prefix (X @ [(u, w)])
        (G @ shiftl0 d0 D)"
      by (rule prefix_length_prefix[
            OF p1 p2 plen])
    obtain A1' where hA1':
      "G @ shiftl0 d0 D =
        (X @ [(u, w)]) @ A1'"
      using hp1 by (rule prefixE)
    have hA1'len:
      "length A1' =
        length G + length D -
          (length X + 1)"
    proof -
      note len = arg_cong[OF hA1',
        where f=length]
      show ?thesis
        using len hSDlen by simp
    qed
    have hNm:
      "G @ copies d0 ?blk m =
        ((X @ [(u, w)]) @ A1') @
          (u + e - d0, w) #
            (shiftl0 d0 B @
              (shiftl0 d0 A2 @
                shiftl0 d0 Zs))"
      using hSeq hA1' by simp
    have hback:
      "G @ copies d0 ?blk n =
        (G @ copies d0 ?blk m) @
          shiftr0 (m * d0) ?blk"
      using copies_succ_back[
        of d0 ?blk m] neq
      by simp
    have hbig:
      "(X @ [(u, w)]) @
          (A1 @
            (u + e, w) #
              (B @ (A2 @ Zs))) =
        (X @ [(u, w)]) @
          (A1' @
            (u + e - d0, w) #
              ((shiftl0 d0 B @
                (shiftl0 d0 A2 @
                  shiftl0 d0 Zs)) @
                shiftr0 (m * d0) ?blk))"
      using heq2 hexp hback hNm
      by simp
    have hcancel:
      "A1 @
          (u + e, w) #
            (B @ (A2 @ Zs)) =
        A1' @
          (u + e - d0, w) #
            ((shiftl0 d0 B @
              (shiftl0 d0 A2 @
                shiftl0 d0 Zs)) @
              shiftr0 (m * d0) ?blk)"
      using hbig by simp
    have A1'le:
      "length A1' \<le> length A1"
      using hA1'len hA1len hClen hcaseL
      by presburger
    obtain Wnd where
        hW1: "A1 = A1' @ Wnd"
      and hW2:
        "(u + e - d0, w) #
            ((shiftl0 d0 B @
              (shiftl0 d0 A2 @
                shiftl0 d0 Zs)) @
              shiftr0 (m * d0) ?blk) =
          Wnd @
            (u + e, w) #
              (B @ (A2 @ Zs))"
      using split_append_left[
        OF hcancel A1'le]
      by blast
    have Cadd:
      "length C + (length X + 1) =
        length G + (length R + 1)"
      using hClen hcaseL by presburger
    have A1'add:
      "length A1' + (length X + 1) =
        length G + length D"
      using hA1'len less by presburger
    have Wlen:
      "length Wnd = length R + 1"
    proof -
      have A1W:
        "length A1 =
          length A1' + length Wnd"
        using hW1 by simp
      show ?thesis
        using A1W hA1len Cadd A1'add
        by presburger
    qed
    show ?thesis
    proof (cases Wnd)
      case Nil
      have False using Wlen Nil by simp
      then show ?thesis by blast
    next
      case (Cons wnd0 Wtl)
      have hwnd0:
        "wnd0 = (u + e - d0, w)"
        using hW2 Cons by simp
      have hWtl:
        "(shiftl0 d0 B @
            (shiftl0 d0 A2 @
              shiftl0 d0 Zs)) @
            shiftr0 (m * d0) ?blk =
          Wtl @
            (u + e, w) #
              (B @ (A2 @ Zs))"
        using hW2 Cons by simp
      have hA1dec:
        "A1 =
          A1' @
            (u + e - d0, w) # Wtl"
        using hW1 Cons hwnd0 by simp
      have hde: "d0 < e"
      proof -
        have mem:
          "(u + e - d0, w) \<in> set A1"
          using hA1dec by simp
        have gt0:
          "u < fst (u + e - d0, w)"
          by (rule h1[rule_format, OF mem])
        have gt:
          "u < u + e - d0"
          using gt0 by simp
        show ?thesis
          using gt hd0le by presburger
      qed
      have hued:
        "u + e - d0 = u + (e - d0)"
        using hde by presburger
      let ?SA2 = "shiftl0 d0 A2"
      let ?SZ = "shiftl0 d0 Zs"
      let ?A2' =
        "takeWhile (\<lambda>p. u < fst p) ?SA2"
      let ?DW =
        "dropWhile (\<lambda>p. u < fst p) ?SA2"
      let ?Z2 = "?DW @ ?SZ"
      have hA2Z:
        "?A2' @ ?Z2 = ?SA2 @ ?SZ"
        by simp
      have hA2'pre:
        "prefix ?A2' ?SA2"
        by (rule takeWhile_is_prefix)
      have hA2'gt:
        "\<forall>x\<in>set ?A2'. u < fst x"
      proof (intro ballI)
        fix x
        assume xm: "x \<in> set ?A2'"
        have both:
          "x \<in> set ?SA2 \<and> u < fst x"
          by (rule set_takeWhileD[OF xm])
        show "u < fst x"
          using both by simp
      qed
      have hA2'hd:
        "?A2' = [] \<or>
          fst (hd ?A2') \<le>
            u + (e - d0)"
      proof (cases A2)
        case Nil
        then show ?thesis
          unfolding shiftl0_def by simp
      next
        case (Cons a A2r)
        have ahd:
          "fst a \<le> u + e"
        proof -
          from h4 show ?thesis
          proof
            assume "A2 = []"
            then show ?thesis using Cons by simp
          next
            assume "fst (hd A2) \<le> u + e"
            then show ?thesis using Cons by simp
          qed
        qed
        show ?thesis
        proof (cases "u < fst a - d0")
          case True
          then have hd:
            "hd ?A2' =
              (fst a - d0, snd a)"
            using Cons
            by (simp add: shiftl0_cons)
          have bound:
            "fst a - d0 \<le>
              u + (e - d0)"
            using ahd hde hd0le
            by presburger
          show ?thesis
            using hd bound by simp
        next
          case False
          then have "?A2' = []"
            using Cons
            by (simp add: shiftl0_cons)
          then show ?thesis by simp
        qed
      qed
      have hZ2hd:
        "?Z2 = [] \<or>
          fst (hd ?Z2) \<le> u"
      proof (cases "?DW = []")
        case True
        show ?thesis
        proof (cases Zs)
          case Nil
          then show ?thesis
            using True
            unfolding shiftl0_def by simp
        next
          case (Cons z Zr)
          have zhd: "fst z \<le> u"
          proof -
            from h5 show ?thesis
            proof
              assume "Zs = []"
              then show ?thesis using Cons by simp
            next
              assume "fst (hd Zs) \<le> u"
              then show ?thesis using Cons by simp
            qed
          qed
          have Z2eq: "?Z2 = ?SZ"
            using True by simp
          have hdSZ:
            "hd ?SZ =
              (fst z - d0, snd z)"
            using Cons
            by (simp add: shiftl0_cons)
          have hdEq:
            "hd ?Z2 = hd ?SZ"
            by (rule arg_cong[OF Z2eq])
          have hd:
            "hd ?Z2 =
              (fst z - d0, snd z)"
            using hdEq hdSZ by simp
          show ?thesis
          proof (rule disjI2)
            have eqfst:
              "fst (hd ?Z2) =
                fst (fst z - d0, snd z)"
              by (rule arg_cong[OF hd])
            show "fst (hd ?Z2) \<le> u"
              using eqfst zhd by simp
          qed
        qed
      next
        case False
        have notgt:
          "\<not> u < fst (hd ?DW)"
          by (rule hd_dropWhile[OF False])
        have hd:
          "hd ?Z2 = hd ?DW"
          by (rule headI_append_left[OF False])
        show ?thesis
        proof (rule disjI2)
          have bound: "fst (hd ?DW) \<le> u"
          proof -
            have iff:
              "(\<not> u < fst (hd ?DW)) \<longleftrightarrow>
                fst (hd ?DW) \<le> u"
              by (rule linorder_not_less)
            show ?thesis
              by (rule iff[THEN iffD1, OF notgt])
          qed
          show "fst (hd ?Z2) \<le> u"
            using hd bound by simp
        qed
      qed
      have heq':
        "G @ copies d0 ?blk m =
          (X @
            (u, w) #
              (A1' @
                (u + (e - d0), w) #
                  (shiftl0 d0 B @ ?A2'))) @
            ?Z2"
        using hNm hA2Z hued by simp
      have hIHm:
        "ArgDomCoreOn
          (G @ copies d0 ?blk m)"
        by (rule hIH[rule_format,
              OF hm1])
           (use neq in presburger)
      have hA1'gt:
        "\<forall>x\<in>set A1'. u < fst x"
      proof (intro ballI)
        fix x
        assume "x \<in> set A1'"
        then have "x \<in> set A1"
          using hA1dec by simp
        then show "u < fst x"
          by (rule h1[rule_format])
      qed
      have hB'gt:
        "\<forall>x\<in>set (shiftl0 d0 B).
          u + (e - d0) < fst x"
      proof (intro ballI)
        fix x
        assume xb:
          "x \<in> set (shiftl0 d0 B)"
        obtain y where
            yB: "y \<in> set B"
          and yx:
            "(fst y - d0, snd y) = x"
          using xb mem_shiftl0[
            of x d0 B] by blast
        have ygt: "u + e < fst y"
          by (rule h2[rule_format, OF yB])
        have fx: "fst x = fst y - d0"
        proof -
          have eqfst:
            "fst (fst y - d0, snd y) = fst x"
            by (rule arg_cong[OF yx])
          show ?thesis using eqfst by simp
        qed
        show
          "u + (e - d0) < fst x"
          using ygt fx hde by presburger
      qed
      have hspine':
        "SpineOK A1'
          (u + (e - d0)) w"
        unfolding SpineOK_def
      proof (intro allI impI)
        fix U V x
        assume hdec: "A1' = U @ x # V"
          and hxlt:
            "fst x < u + (e - d0)"
          and hV:
            "\<forall>y\<in>set V.
              fst x < fst y"
        have hGSD:
          "((X @ [(u, w)]) @ U) @
              x # V =
            G @ shiftl0 d0 D"
          using hA1' hdec by simp
        have hDge:
          "\<forall>y\<in>set D. d0 \<le> fst y"
        proof (intro ballI)
          fix y
          assume yD: "y \<in> set D"
          show "d0 \<le> fst y"
            by (rule hmem_ge[rule_format])
               (use hD2 yD in simp)
        qed
        have hDshift:
          "shiftr0 d0 (shiftl0 d0 D) = D"
          by (rule shiftr0_shiftl0[
                OF hDge])
        show "w \<le> snd x"
        proof (cases
          "length ((X @ [(u, w)]) @ U) <
            length G")
          case True
          have hle2:
            "length
                (((X @ [(u, w)]) @ U) @ [x])
              \<le> length G"
            using True by simp
          have hGSD':
            "G @ shiftl0 d0 D =
              (((X @ [(u, w)]) @ U) @ [x]) @ V"
            using hGSD by simp
          obtain V3 where
              hV31:
                "G =
                  (((X @ [(u, w)]) @ U) @ [x]) @ V3"
            and hV32:
              "V = V3 @ shiftl0 d0 D"
            using split_append_left[
              OF hGSD' hle2]
            by blast
          have hCdec:
            "C =
              (U @ [x]) @
                (V3 @ ?blk)"
          proof -
            have common:
              "(X @ [(u, w)]) @
                  ((U @ [x]) @
                    (V3 @ ?blk)) =
                (X @ [(u, w)]) @ C"
              using hC1 hV31 by simp
            show ?thesis
              using common by simp
          qed
          have hhead:
            "hd (copies d0 ?blk m) =
              hd ?blk"
            by (rule copies_headI[
                  OF _ hm1])
               simp
          have hxv0: "fst x < v0"
          proof (cases "shiftl0 d0 D")
            case Nil
            have root:
              "v0 = u + e - d0"
              using hSeq hhead Nil by simp
            have val:
              "u + (e - d0) = v0"
              using hued root by presburger
            show ?thesis
              using hxlt val by presburger
          next
            case (Cons sd0 SD')
            have sdV: "sd0 \<in> set V"
              using hV32 Cons by simp
            have sd:
              "sd0 = (v0, w0)"
              using hSeq hhead Cons by simp
            have "fst x < fst sd0"
              by (rule hV[rule_format, OF sdV])
            then show ?thesis
              using sd by simp
          qed
          have A1full:
            "A1 =
              U @ x #
                ((V3 @ ?blk) @ D)"
            using hD1 hCdec by simp
          have suffix:
            "\<forall>y\<in>set ((V3 @ ?blk) @ D).
              fst x < fst y"
          proof (intro ballI)
            fix y
            assume ymem:
              "y \<in> set ((V3 @ ?blk) @ D)"
            show "fst x < fst y"
            proof (cases "y \<in> set V3")
              case True
              have "y \<in> set V"
                using hV32 True by simp
              then show ?thesis
                by (rule hV[rule_format])
            next
              case False
              note notV = False
              show ?thesis
              proof (cases "y \<in> set ?blk")
                case True
                then show ?thesis
                  using hxv0 hRgt by auto
              next
                case False
                have yD: "y \<in> set D"
                  using ymem notV False by auto
                have yt:
                  "y \<in> set ?tail"
                  using hD2 yD by simp
                obtain z where
                    zm:
                      "z \<in> set
                        (copies d0 ?blk m)"
                  and zy:
                    "(fst z + d0, snd z) = y"
                  using yt mem_shiftr0[
                    of y d0
                      "copies d0 ?blk m"]
                  by blast
                have base:
                  "\<forall>q\<in>set
                    (copies d0 ?blk m).
                      v0 \<le> fst q"
                  by (rule copies_v0_le)
                     (use hRgt in auto)
                have "v0 \<le> fst z"
                  by (rule base[rule_format, OF zm])
                moreover have
                  "fst y = fst z + d0"
                proof -
                  have eqfst:
                    "fst (fst z + d0, snd z) =
                      fst y"
                    by (rule arg_cong[OF zy])
                  show ?thesis using eqfst by simp
                qed
                ultimately show ?thesis
                  using hxv0 by presburger
              qed
            qed
          qed
          have xltBig: "fst x < u + e"
            using hxlt hde by presburger
          show ?thesis
            by (rule h6[
                  unfolded SpineOK_def,
                  rule_format,
                  OF A1full xltBig
                    suffix[rule_format]])
        next
          case False
          have hge:
            "length G \<le>
              length ((X @ [(u, w)]) @ U)"
            using False by simp
          obtain U2 where
              hU21:
                "(X @ [(u, w)]) @ U =
                  G @ U2"
            and hU22:
              "shiftl0 d0 D =
                U2 @ x # V"
            using split_append_left[
              OF hGSD hge]
            by blast
          have hDdec:
            "D =
              shiftr0 d0 U2 @
                (fst x + d0, snd x) #
                  shiftr0 d0 V"
            using hDshift hU22
            by (simp add: shiftr0_append
                shiftr0_cons)
          have A1full:
            "A1 =
              (C @ shiftr0 d0 U2) @
                (fst x + d0, snd x) #
                  shiftr0 d0 V"
            using hD1 hDdec by simp
          have rootlt:
            "fst (fst x + d0, snd x) <
              u + e"
            using hxlt hde by simp
          have suffix:
            "\<forall>y\<in>set (shiftr0 d0 V).
              fst (fst x + d0, snd x) <
                fst y"
          proof (intro ballI)
            fix y
            assume ym:
              "y \<in> set (shiftr0 d0 V)"
            obtain z where
                zV: "z \<in> set V"
              and zy:
                "(fst z + d0, snd z) = y"
              using ym mem_shiftr0[
                of y d0 V] by blast
            have xz: "fst x < fst z"
              by (rule hV[rule_format, OF zV])
            have fy: "fst y = fst z + d0"
            proof -
              have eqfst:
                "fst (fst z + d0, snd z) = fst y"
                by (rule arg_cong[OF zy])
              show ?thesis using eqfst by simp
            qed
            show
              "fst (fst x + d0, snd x) <
                fst y"
              using xz fy by simp
          qed
          have bound:
            "w \<le>
              snd (fst x + d0, snd x)"
            by (rule h6[
                  unfolded SpineOK_def,
                  rule_format,
                  OF A1full rootlt
                    suffix[rule_format]])
          then show ?thesis by simp
        qed
      qed
      have hcore:
        "sle (shiftl0 d0 B)
          (shiftr0 (e - d0)
            (A1' @
              (u + (e - d0), w) #
                (shiftl0 d0 B @ ?A2')))"
        by (rule hIHm[
              unfolded ArgDomCoreOn_def,
              rule_format,
              OF heq' _ hA1'gt[rule_format]
                hB'gt[rule_format]
                hA2'gt[rule_format]
                hA2'hd hZ2hd hspine'])
           (use hde in presburger)
      have hpre1:
        "prefix (shiftl0 d0 B @ ?A2')
          (Wtl @
            (u + e, w) #
              (B @ (A2 @ Zs)))"
      proof -
        have host:
          "Wtl @
              (u + e, w) #
                (B @ (A2 @ Zs)) =
            (shiftl0 d0 B @
              (?SA2 @ ?SZ)) @
              shiftr0 (m * d0) ?blk"
          by (rule hWtl[symmetric])
        have replace:
          "(shiftl0 d0 B @
              (?SA2 @ ?SZ)) @
              shiftr0 (m * d0) ?blk =
            (shiftl0 d0 B @ ?A2') @
              (?Z2 @
                shiftr0 (m * d0) ?blk)"
          using hA2Z by simp
        have eqHost:
          "Wtl @
              (u + e, w) #
                (B @ (A2 @ Zs)) =
            (shiftl0 d0 B @ ?A2') @
              (?Z2 @
                shiftr0 (m * d0) ?blk)"
          by (rule trans[OF host replace])
        show ?thesis
          unfolding prefix_def
          using eqHost by blast
      qed
      have hpre2:
        "prefix
          (Wtl @
            (u + e, w) #
              (B @ A2))
          (Wtl @
            (u + e, w) #
              (B @ (A2 @ Zs)))"
      proof (rule prefixI)
        show
          "Wtl @
              (u + e, w) #
                (B @ (A2 @ Zs)) =
            (Wtl @
              (u + e, w) #
                (B @ A2)) @ Zs"
          by simp
      qed
      have hlen:
        "length (shiftl0 d0 B @ ?A2') \<le>
          length
            (Wtl @
              (u + e, w) #
                (B @ A2))"
      proof -
        have ale:
          "length ?A2' \<le> length ?SA2"
          by (rule prefix_length_le[
                OF hA2'pre])
        show ?thesis
          using ale
          unfolding shiftl0_def by simp
      qed
      have hpreB:
        "prefix (shiftl0 d0 B @ ?A2')
          (Wtl @
            (u + e, w) #
              (B @ A2))"
        by (rule prefix_length_prefix[
              OF hpre1 hpre2 hlen])
      have hpre_final:
        "prefix
          (A1' @
            (u + (e - d0), w) #
              (shiftl0 d0 B @ ?A2'))
          (A1 @
            (u + e, w) #
              (B @ A2))"
        using prefix_cons_append[
          OF hpreB,
          of A1'
            "(u + (e - d0), w)"]
          hA1dec hued
        by simp
      have shiftedPre:
        "prefix
          (shiftr0 (e - d0)
            (A1' @
              (u + (e - d0), w) #
                (shiftl0 d0 B @ ?A2')))
          (shiftr0 (e - d0)
            (A1 @
              (u + e, w) #
                (B @ A2)))"
        by (rule shiftr0_prefix[
              OF hpre_final])
      obtain TT where hTT:
        "shiftr0 (e - d0)
            (A1 @
              (u + e, w) #
                (B @ A2)) =
          shiftr0 (e - d0)
            (A1' @
              (u + (e - d0), w) #
                (shiftl0 d0 B @ ?A2')) @ TT"
        using shiftedPre by (rule prefixE)
      have hstep:
        "sle (shiftl0 d0 B)
          (shiftr0 (e - d0)
            (A1 @
              (u + e, w) #
                (B @ A2)))"
      proof -
        have ext:
          "sle (shiftl0 d0 B)
            (shiftr0 (e - d0)
                (A1' @
                  (u + (e - d0), w) #
                    (shiftl0 d0 B @ ?A2')) @
              TT)"
          by (rule sle_append_mono[
                OF hcore])
        show ?thesis using ext hTT by simp
      qed
      have hBmem:
        "\<forall>x\<in>set B. d0 \<le> fst x"
      proof (intro ballI)
        fix x
        assume xB: "x \<in> set B"
        have "u + e < fst x"
          by (rule h2[rule_format, OF xB])
        then show "d0 \<le> fst x"
          using hd0le by presburger
      qed
      have lifted:
        "sle
          (shiftr0 d0 (shiftl0 d0 B))
          (shiftr0 d0
            (shiftr0 (e - d0)
              (A1 @
                (u + e, w) #
                  (B @ A2))))"
        using sle_shiftr0[
          of d0 "shiftl0 d0 B"
            "shiftr0 (e - d0)
              (A1 @
                (u + e, w) #
                  (B @ A2))"]
          hstep by simp
      have first:
        "shiftr0 d0 (shiftl0 d0 B) = B"
        by (rule shiftr0_shiftl0[
              OF hBmem])
      have total: "d0 + (e - d0) = e"
        using hde by presburger
      have second:
        "shiftr0 d0
            (shiftr0 (e - d0)
              (A1 @
                (u + e, w) #
                  (B @ A2))) =
          shiftr0 e
            (A1 @
              (u + e, w) #
                (B @ A2))"
        using shiftr0_add[
          of d0 "e - d0"
            "A1 @
              (u + e, w) #
                (B @ A2)"]
          total by simp
      show ?thesis
        using lifted first second by simp
    qed
  next
    case equal
    have hNm:
      "G @ copies d0 ?blk m =
        (G @ shiftl0 d0 D) @
          (u + e - d0, w) #
            (shiftl0 d0 B @
              (shiftl0 d0 A2 @
                shiftl0 d0 Zs))"
      using hSeq by simp
    have hback:
      "G @ copies d0 ?blk n =
        (G @ copies d0 ?blk m) @
          shiftr0 (m * d0) ?blk"
      using copies_succ_back[
        of d0 ?blk m] neq
      by simp
    have hkey:
      "(X @ [(u, w)]) @
          (A1 @
            (u + e, w) #
              (B @ (A2 @ Zs))) =
        (G @ shiftl0 d0 D) @
          ((u + e - d0, w) #
            ((shiftl0 d0 B @
              (shiftl0 d0 A2 @
                shiftl0 d0 Zs)) @
              shiftr0 (m * d0) ?blk))"
      using heq2 hexp hback hNm
      by simp
    have Gle:
      "length (G @ shiftl0 d0 D) \<le>
        length (X @ [(u, w)])"
      using equal
      unfolding shiftl0_def by simp
    obtain K where
        hK1:
          "X @ [(u, w)] =
            (G @ shiftl0 d0 D) @ K"
      and hK2:
        "(u + e - d0, w) #
            ((shiftl0 d0 B @
              (shiftl0 d0 A2 @
                shiftl0 d0 Zs)) @
              shiftr0 (m * d0) ?blk) =
          K @
            (A1 @
              (u + e, w) #
                (B @ (A2 @ Zs)))"
      using split_append_left[
        OF hkey Gle]
      by blast
    have hKlen: "length K = 1"
    proof -
      note len = arg_cong[OF hK1,
        where f=length]
      show ?thesis
        using len equal
        unfolding shiftl0_def by simp
    qed
    have Kex: "\<exists>k. K = [k]"
    proof (cases K)
      case Nil
      then show ?thesis
        using hKlen by simp
    next
      case (Cons k Kr)
      have "Kr = []"
        using hKlen Cons
        by (cases Kr) simp_all
      then show ?thesis
        using Cons by blast
    qed
    then obtain k where K: "K = [k]"
      by blast
    have lenEq:
      "length X =
        length (G @ shiftl0 d0 D)"
      using equal
      unfolding shiftl0_def by simp
    have splitX:
      "X = G @ shiftl0 d0 D \<and>
        [(u, w)] = [k]"
    proof -
      have iff:
        "(X @ [(u, w)] =
            (G @ shiftl0 d0 D) @ [k])
          \<longleftrightarrow>
         (X = G @ shiftl0 d0 D \<and>
          [(u, w)] = [k])"
        by (rule append_eq_append_conv)
           (use lenEq in simp)
      show ?thesis
        by (rule iff[THEN iffD1])
           (use hK1 K in simp)
    qed
    have hk1: "k = (u, w)"
      using splitX by simp
    have hk2:
      "k = (u + e - d0, w)"
      using hK2 K by simp
    have hed: "e = d0"
    proof -
      have pair:
        "(u, w) = (u + e - d0, w)"
        using hk1 hk2 by simp
      have fstEq:
        "u = u + e - d0"
      proof -
        have
          "fst (u, w) =
            fst (u + e - d0, w)"
          by (rule arg_cong[OF pair])
        then show ?thesis by simp
      qed
      show ?thesis
        using fstEq he hd0le by presburger
    qed
    have hRW:
      "(shiftl0 d0 B @
          (shiftl0 d0 A2 @
            shiftl0 d0 Zs)) @
          shiftr0 (m * d0) ?blk =
        A1 @
          (u + e, w) #
            (B @ (A2 @ Zs))"
      using hK2 K by simp
    have hpre1:
      "prefix (shiftl0 d0 B)
        (A1 @
          (u + e, w) #
            (B @ (A2 @ Zs)))"
    proof -
      have eqHost:
        "A1 @
            (u + e, w) #
              (B @ (A2 @ Zs)) =
          shiftl0 d0 B @
            ((shiftl0 d0 A2 @
                shiftl0 d0 Zs) @
              shiftr0 (m * d0) ?blk)"
        using hRW by simp
      show ?thesis
        unfolding prefix_def
        using eqHost by blast
    qed
    have hpre2:
      "prefix
        (A1 @
          (u + e, w) #
            (B @ A2))
        (A1 @
          (u + e, w) #
            (B @ (A2 @ Zs)))"
    proof (rule prefixI)
      show
        "A1 @
            (u + e, w) #
              (B @ (A2 @ Zs)) =
          (A1 @
            (u + e, w) #
              (B @ A2)) @ Zs"
        by simp
    qed
    have plen:
      "length (shiftl0 d0 B) \<le>
        length
          (A1 @
            (u + e, w) #
              (B @ A2))"
      unfolding shiftl0_def by simp
    have hpre3:
      "prefix (shiftl0 d0 B)
        (A1 @
          (u + e, w) #
            (B @ A2))"
      by (rule prefix_length_prefix[
            OF hpre1 hpre2 plen])
    have hBmem:
      "\<forall>x\<in>set B. d0 \<le> fst x"
    proof (intro ballI)
      fix x
      assume xB: "x \<in> set B"
      have "u + e < fst x"
        by (rule h2[rule_format, OF xB])
      then show "d0 \<le> fst x"
        using hd0le by presburger
    qed
    have hBshift:
      "shiftr0 e (shiftl0 d0 B) = B"
      using shiftr0_shiftl0[
        OF hBmem] hed by simp
    have hfin:
      "prefix B
        (shiftr0 e
          (A1 @
            (u + e, w) #
              (B @ A2)))"
      using shiftr0_prefix[
        OF hpre3, of e] hBshift
      by simp
    show ?thesis
      by (rule sle_of_prefix[OF hfin])
  next
    case greater
    have mex': "\<exists>m'. m = m' + 1"
      by (intro exI[of _ "m - 1"])
         (use hm1 in presburger)
    then obtain m' where meq: "m = m' + 1"
      by blast
    have GXle:
      "length G \<le>
        length (X @ [(u, w)])"
      using greater by simp
    obtain K where
        hK1:
          "X @ [(u, w)] = G @ K"
      and hK2:
        "?blk = K @ C"
      using split_append_left[
        OF hC1[symmetric] GXle]
      by blast
    have Kne: "K \<noteq> []"
    proof
      assume "K = []"
      then have eqX: "X @ [(u, w)] = G"
        using hK1 by simp
      have lenEq:
        "length (X @ [(u, w)]) = length G"
        by (rule arg_cong[OF eqX])
      have len:
        "length G = length X + 1"
        using lenEq by simp
      show False
        using len greater by presburger
    qed
    obtain k0 K1 where K:
      "K = k0 # K1"
      using Kne by (cases K) auto
    have hRK1: "R = K1 @ C"
      using hK2 K by simp
    have hK1':
      "X @ [(u, w)] =
        (G @ [k0]) @ K1"
      using hK1 K by simp
    have GKle:
      "length (G @ [k0]) \<le> length X"
      using greater by simp
    obtain T where
        hT1: "X = (G @ [k0]) @ T"
      and hT2: "K1 = T @ [(u, w)]"
      using split_append_left[
        OF hK1' GKle]
      by blast
    have hRdec:
      "R = T @ (u, w) # C"
      using hRK1 hT2 by simp
    have huv0: "v0 < u"
    proof -
      have mem: "(u, w) \<in> set R"
        using hRdec by simp
      have "v0 < fst (u, w)"
        by (rule hRgt[rule_format, OF mem])
      then show ?thesis by simp
    qed
    have hSC:
      "shiftr0 d0
          (copies d0 ?blk m) =
        (v0 + d0, w0) #
          shiftr0 d0
            (R @
              shiftr0 d0
                (copies d0 ?blk m'))"
      using copies_succ_cons[
        of d0 v0 w0 R m'] meq
      by (simp add: shiftr0_cons
          shiftr0_append)
    have hDcase:
      "u < v0 + d0 \<and> w \<le> w0"
    proof (cases D)
      case Nil
      have pair:
        "(v0 + d0, w0) =
          (u + e, w)"
        using hD2 hSC Nil by simp
      show ?thesis
        using pair he by simp
    next
      case (Cons d1 D')
      have hd1:
        "d1 = (v0 + d0, w0)"
        using hD2 hSC Cons by simp
      have hrest:
        "shiftr0 d0
            (R @
              shiftr0 d0
                (copies d0 ?blk m')) =
          D' @
            (u + e, w) #
              (B @ (A2 @ Zs))"
        using hD2 hSC Cons by simp
      have hA1dec:
        "A1 =
          C @
            (v0 + d0, w0) # D'"
        using hD1 Cons hd1 by simp
      have huv: "u < v0 + d0"
      proof -
        have mem:
          "(v0 + d0, w0) \<in> set A1"
          using hA1dec by simp
        have "u < fst (v0 + d0, w0)"
          by (rule h1[rule_format, OF mem])
        then show ?thesis by simp
      qed
      have hd0pos: "0 < d0"
        using huv0 huv by presburger
      have htl:
        "\<forall>x\<in>set
          (R @
            shiftr0 d0
              (copies d0 ?blk m')).
            v0 < fst x"
        using copies_tl_gt[
          OF hRgt hd0pos,
          of "m' + 1" w0]
        by simp
      have htl':
        "\<forall>x\<in>set
          (shiftr0 d0
            (R @
              shiftr0 d0
                (copies d0 ?blk m'))).
            v0 + d0 < fst x"
      proof (intro ballI)
        fix x
        assume xm:
          "x \<in> set
            (shiftr0 d0
              (R @
                shiftr0 d0
                  (copies d0 ?blk m')))"
        obtain z where
            zm:
              "z \<in> set
                (R @
                  shiftr0 d0
                    (copies d0 ?blk m'))"
          and zx:
            "(fst z + d0, snd z) = x"
          using xm mem_shiftr0[
            of x d0
              "R @
                shiftr0 d0
                  (copies d0 ?blk m')"]
          by blast
        have "v0 < fst z"
          by (rule htl[rule_format, OF zm])
        then show "v0 + d0 < fst x"
        proof -
          have eqfst:
            "fst (fst z + d0, snd z) =
              fst x"
            by (rule arg_cong[OF zx])
          show ?thesis
            using eqfst \<open>v0 < fst z\<close>
            by simp
        qed
      qed
      have rootlt:
        "v0 + d0 < u + e"
      proof -
        have mem:
          "(u + e, w) \<in> set
            (shiftr0 d0
              (R @
                shiftr0 d0
                  (copies d0 ?blk m')))"
          using hrest by simp
        have
          "v0 + d0 < fst (u + e, w)"
          by (rule htl'[rule_format, OF mem])
        then show ?thesis by simp
      qed
      have suffix:
        "\<forall>y\<in>set D'.
          v0 + d0 < fst y"
      proof (intro ballI)
        fix y
        assume yD: "y \<in> set D'"
        show "v0 + d0 < fst y"
          by (rule htl'[rule_format])
             (use hrest yD in simp)
      qed
      have rootlt0:
        "fst (v0 + d0, w0) < u + e"
        using rootlt by simp
      have suffix0:
        "\<forall>y\<in>set D'.
          fst (v0 + d0, w0) < fst y"
        using suffix by simp
      have bound0:
        "w \<le> snd (v0 + d0, w0)"
        by (rule h6[
              unfolded SpineOK_def,
              rule_format,
              of C "(v0 + d0, w0)" D',
              OF hA1dec rootlt0
                suffix0[rule_format]])
      have bound: "w \<le> w0"
        using bound0 by simp
      show ?thesis using huv bound by simp
    qed
    have huv: "u < v0 + d0"
      using hDcase by blast
    have hww0: "w \<le> w0"
      using hDcase by blast
    have hd0pos: "0 < d0"
      using huv0 huv by presburger
    show ?thesis
    proof -
      have posCase:
        "0 < d0 \<and> snd lp = w0 + 1 \<and>
          fst lp = v0 + d0 \<and>
          nextrel1 M (length G)
            (length M - 1)"
      proof -
        from hdisj show ?thesis
        proof
          assume "d0 = 0 \<and> snd lp = 0 \<and>
            fst lp = v0 + 1"
          then show ?thesis
            using hd0pos by simp
        next
          assume ?thesis
          then show ?thesis .
        qed
      qed
      have lpeq:
        "lp = (v0 + d0, w0 + 1)"
        using posCase
        by (cases lp) auto
      have hnr':
        "nextrel1
          ((G @ ?blk) @
            [(v0 + d0, w0 + 1)])
          (length G)
          (length (G @ ?blk))"
      proof -
        have hnr:
          "nextrel1 M (length G)
            (length M - 1)"
          using posCase by blast
        show ?thesis
          using hnr hMeq lpeq by simp
      qed
      have strong:
        "SpineOK R (v0 + d0) (w0 + 1)"
        by (rule spineOK_of_nextrel1_strict[
              OF hnr'])
      have Cgt:
        "\<forall>y\<in>set C. u < fst y"
      proof (intro ballI)
        fix y
        assume yC: "y \<in> set C"
        have "y \<in> set A1"
          using hD1 yC by simp
        then show "u < fst y"
          by (rule h1[rule_format])
      qed
      have huvPair:
        "fst (u, w) < v0 + d0"
        using huv by simp
      have CgtPair:
        "\<forall>y\<in>set C.
          fst (u, w) < fst y"
        using Cgt by simp
      have strict0:
        "w0 + 1 \<le> snd (u, w)"
        by (rule strong[
              unfolded SpineOK_def,
              rule_format,
              of T "(u, w)" C,
              OF hRdec huvPair
                CgtPair[rule_format]])
      have strict: "w0 + 1 \<le> w"
        using strict0 by simp
      have False
        using strict hww0 by presburger
      then show ?thesis by blast
    qed
  qed
qed

lemma argDomCoreOn_bad:
  assumes hM: "ST_PS M"
    and hMon: "ArgDomCoreOn M"
    and hMeq:
      "M = G @ ((v0, w0) # R) @ [lp]"
    and hRgt: "\<forall>x\<in>set R. v0 < fst x"
    and hlp: "v0 < fst lp"
    and hdisj:
      "(d0 = 0 \<and> snd lp = 0 \<and>
          fst lp = v0 + 1) \<or>
       (0 < d0 \<and> snd lp = w0 + 1 \<and>
          fst lp = v0 + d0 \<and>
          nextrel1 M (length G)
            (length M - 1))"
    and hSTn:
      "\<forall>m. 1 \<le> m \<longrightarrow>
        ST_PS
          (G @ copies d0
            ((v0, w0) # R) m)"
    and hn: "1 \<le> n"
  shows
    "ArgDomCoreOn
      (G @ copies d0
        ((v0, w0) # R) n)"
proof -
  let ?blk = "(v0, w0) # R"
  have all:
    "\<forall>k. 1 \<le> k \<longrightarrow>
      ArgDomCoreOn
        (G @ copies d0 ?blk k)"
  proof
    fix k
    show
      "1 \<le> k \<longrightarrow>
        ArgDomCoreOn
          (G @ copies d0 ?blk k)"
    proof (induction k rule: less_induct)
      case (less k)
      show ?case
      proof
        assume k1: "1 \<le> k"
        have hIH:
          "\<forall>m. 1 \<le> m \<longrightarrow>
            m < k \<longrightarrow>
            ArgDomCoreOn
              (G @ copies d0 ?blk m)"
        proof (intro allI impI)
          fix m
          assume m1: "1 \<le> m"
            and mk: "m < k"
          have imp:
            "1 \<le> m \<longrightarrow>
              ArgDomCoreOn
                (G @ copies d0 ?blk m)"
            by (rule less.IH[OF mk])
          show
            "ArgDomCoreOn
              (G @ copies d0 ?blk m)"
            by (rule imp[rule_format, OF m1])
        qed
        show
          "ArgDomCoreOn
            (G @ copies d0 ?blk k)"
          unfolding ArgDomCoreOn_def
        proof (intro allI impI)
          fix X A1 B A2 Zs u w e
          assume heq:
              "G @ copies d0 ?blk k =
                (X @
                  (u, w) #
                    (A1 @
                      (u + e, w) #
                        (B @ A2))) @ Zs"
            and he: "0 < e"
            and h1:
              "\<forall>x\<in>set A1. u < fst x"
            and h2:
              "\<forall>x\<in>set B.
                u + e < fst x"
            and h3:
              "\<forall>x\<in>set A2. u < fst x"
            and h4:
              "A2 = [] \<or>
                fst (hd A2) \<le> u + e"
            and h5:
              "Zs = [] \<or>
                fst (hd Zs) \<le> u"
            and h6:
              "SpineOK A1 (u + e) w"
          let ?p =
            "length G + (length R + 1)"
          show
            "sle B
              (shiftr0 e
                (A1 @
                  (u + e, w) #
                    (B @ A2)))"
          proof (cases
            "length X + (length A1 + 1) < ?p")
            case True
            show ?thesis
              apply (rule argDomCoreOn_bad_B[
                where M=M])
              apply (rule hM)
              apply (rule hMon)
              apply (rule hMeq)
              apply (rule hRgt)
              apply (rule hlp)
              apply (rule hdisj)
              apply (rule hSTn)
              apply (rule hIH)
              apply (rule k1)
              apply (rule heq)
              apply (rule he)
              apply (rule h1)
              apply (rule h2)
              apply (rule h3)
              apply (rule h4)
              apply (rule h5)
              apply (rule h6)
              apply (rule True)
              done
          next
            case notB: False
            show ?thesis
            proof (cases "length X < ?p")
              case True
              have right:
                "?p \<le>
                  length X +
                    (length A1 + 1)"
                using notB by simp
              have hMeqA2:
                "M =
                  (G @ ((v0, w0) # R)) @ [lp]"
                using hMeq by simp
              show ?thesis
                apply (rule argDomCoreOn_bad_A2[
                  where M=M])
                apply (rule hM)
                apply (rule hMon)
                apply (rule hMeqA2)
                apply (rule hRgt)
                apply (rule hlp)
                apply (rule hdisj)
                apply (rule hSTn)
                apply (rule hIH)
                apply (rule k1)
                apply (rule heq)
                apply (rule he)
                apply (rule h1)
                apply (rule h2)
                apply (rule h3)
                apply (rule h4)
                apply (rule h5)
                apply (rule h6)
                apply (rule True)
                apply (rule right)
                done
            next
              case False
              have left: "?p \<le> length X"
                using False by simp
              show ?thesis
                apply (rule argDomCoreOn_bad_A1[
                  where M=M])
                apply (rule hM)
                apply (rule hMon)
                apply (rule hMeq)
                apply (rule hRgt)
                apply (rule hlp)
                apply (rule hdisj)
                apply (rule hSTn)
                apply (rule hIH)
                apply (rule k1)
                apply (rule heq)
                apply (rule he)
                apply (rule h1)
                apply (rule h2)
                apply (rule h3)
                apply (rule h4)
                apply (rule h5)
                apply (rule h6)
                apply (rule left)
                done
            qed
          qed
        qed
      qed
    qed
  qed
  show ?thesis
    by (rule all[rule_format, OF hn])
qed

lemma argDomCoreOn_oper:
  assumes hM: "ST_PS M"
    and hMon: "ArgDomCoreOn M"
    and hn: "1 \<le> n"
  shows "ArgDomCoreOn (M\<lbrakk>n\<rbrakk>)"
proof (cases "length M - 1 = 0")
  case True
  have eq: "M\<lbrakk>n\<rbrakk> = M"
    by (rule oper_eq_self_of_short[OF True])
  show ?thesis using eq hMon by simp
next
  case short: False
  have L: "1 < length M"
    using short by presburger
  show ?thesis
  proof (cases
    "entry M 0 (length M - 1) = 0 \<and>
     entry M 1 (length M - 1) = 0")
    case zero: True
    have Mne: "M \<noteq> []"
    proof
      assume "M = []"
      then show False using L by simp
    qed
    have last:
      "nth_default (0, 0) M
          (length M - 1) =
        (0, 0)"
    proof (rule prod_eqI)
      show
        "fst
            (nth_default (0, 0) M
              (length M - 1)) =
          fst (0, 0)"
        using zero entry_zero[
          of M "length M - 1"]
        by simp
      show
        "snd
            (nth_default (0, 0) M
              (length M - 1)) =
          snd (0, 0)"
        using zero entry_one[
          of M "length M - 1"]
        by simp
    qed
    have split:
      "butlast M @ [(0, 0)] = M"
    proof -
      have raw:
        "butlast M @
          [nth_default (0, 0) M
            (length M - 1)] = M"
        by (rule dropLast_snoc_getD[OF Mne])
      show ?thesis using raw last by simp
    qed
    have snoc:
      "ArgDomCoreOn
        (butlast M @ [(0, 0)])"
      using split hMon by simp
    have core:
      "ArgDomCoreOn (butlast M)"
      by (rule argDomCoreOn_snoc_zero[
            OF _ snoc])
         simp
    have op:
      "M\<lbrakk>n\<rbrakk> = butlast M"
    proof -
      have pred:
        "M\<lbrakk>n\<rbrakk> = Pred M"
        by (rule oper_eq_pred_of_zero[
              OF short zero])
      show ?thesis
        using pred L
        unfolding Pred_def by simp
    qed
    show ?thesis using op core by simp
  next
    case nz: False
    have Mpos: "0 < length M"
      using L by presburger
    have hp:
      "hasParent M
        (idx1 M (length M - 1))
        (length M - 1)"
      by (rule hasParent_last_ST_PS[
            OF hM Mpos nz])
    have bo: "blockok 0 M"
      by (rule blockok_ST_PS[OF hM])
    have st: "steps1 M"
      using bo unfolding blockok_def by simp
    have r1: "r1ok M"
      by (rule r1ok_ST_PS[OF hM])
    obtain G v0 w0 R d0 lp where
        hMeq:
          "M = G @ ((v0, w0) # R) @ [lp]"
      and hMn:
        "\<forall>m. 1 \<le> m \<longrightarrow>
          M\<lbrakk>m\<rbrakk> =
            G @ copies d0
              ((v0, w0) # R) m"
      and hRgt:
        "\<forall>x\<in>set R. v0 < fst x"
      and hlp: "v0 < fst lp"
      and hdisj:
        "(d0 = 0 \<and> snd lp = 0 \<and>
            fst lp = v0 + 1) \<or>
         (0 < d0 \<and> snd lp = w0 + 1 \<and>
            fst lp = v0 + d0 \<and>
            nextrel1 M (length G)
              (length M - 1))"
      using oper_bad_blocks_all[
        OF L st r1 nz hp]
      by blast
    have hSTn:
      "\<forall>m. 1 \<le> m \<longrightarrow>
        ST_PS
          (G @ copies d0
            ((v0, w0) # R) m)"
    proof (intro allI impI)
      fix m :: nat
      assume m1: "1 \<le> m"
      have stOp: "ST_PS (M\<lbrakk>m\<rbrakk>)"
        by (rule ST_PS.oper[OF hM m1])
      have eq:
        "M\<lbrakk>m\<rbrakk> =
          G @ copies d0
            ((v0, w0) # R) m"
        by (rule hMn[rule_format, OF m1])
      show
        "ST_PS
          (G @ copies d0
            ((v0, w0) # R) m)"
        using stOp eq by simp
    qed
    have core:
      "ArgDomCoreOn
        (G @ copies d0
          ((v0, w0) # R) n)"
      apply (rule argDomCoreOn_bad)
      apply (rule hM)
      apply (rule hMon)
      apply (rule hMeq)
      apply (rule hRgt)
      apply (rule hlp)
      apply (rule hdisj)
      apply (rule hSTn)
      apply (rule hn)
      done
    have eq:
      "M\<lbrakk>n\<rbrakk> =
        G @ copies d0
          ((v0, w0) # R) n"
      by (rule hMn[rule_format, OF hn])
    show ?thesis using core eq by simp
  qed
qed

lemma argDomCoreOn_ST_PS:
  assumes hN: "ST_PS N"
  shows "ArgDomCoreOn N"
  using hN
proof induction
  case (diag v)
  show ?case by (rule argDomCoreOn_diag)
next
  case (oper M n)
  show ?case
    by (rule argDomCoreOn_oper[
          OF oper.hyps(1) oper.IH oper.hyps(2)])
qed

lemma argDomCore_holds:
  "ArgDomCore"
  by (rule argDomCore_of_on)
     (use argDomCoreOn_ST_PS in blast)

end
