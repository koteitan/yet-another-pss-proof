theory Cnf
  imports Reduction
begin

lemma getD_eq_getElem':
  "i < length l \<Longrightarrow> nth_default d l i = l ! i"
  by (rule nth_default_nth)

lemma oper_eq_dropLast_append:
  assumes L: "1 < length M" and n1: "1 \<le> n"
  shows "\<exists>R. M\<lbrakk>n\<rbrakk> = butlast M @ R \<and>
    sndSet R \<subseteq> sndSet (butlast M)"
proof -
  have Pred: "Pred M = butlast M"
    using L by (simp add: Pred_def)
  show ?thesis
  proof (cases "entry M 0 (length M - 1) = 0 \<and>
      entry M 1 (length M - 1) = 0")
    case True
    have hL: "length M - 1 \<noteq> 0" using L by simp
    have "M\<lbrakk>n\<rbrakk> = Pred M"
      unfolding oper_def Let_def
      by (simp only: if_not_P[OF hL] if_P[OF True])
    then show ?thesis using Pred by auto
  next
    case hz: False
    show ?thesis
    proof (cases "hasParent M (idx1 M (length M - 1)) (length M - 1)")
      case False
      have hL: "length M - 1 \<noteq> 0" using L by simp
      have "M\<lbrakk>n\<rbrakk> = Pred M"
        unfolding oper_def Let_def
        by (simp only: if_not_P[OF hL] if_not_P[OF hz] if_P[OF False])
      then show ?thesis using Pred by auto
    next
      case hp: True
      obtain G v0 w0 R0 d0 lp where
        M: "M = G @ ((v0, w0) # R0) @ [lp]"
        and Mn: "M\<lbrakk>n\<rbrakk> =
          G @ concat
            (map
              (\<lambda>k. map (\<lambda>p. (fst p + k * d0, snd p))
                ((v0, w0) # R0))
              [0..<n])"
        by (rule oper_bad_blocks[OF L hz hp n1])
      have drop: "butlast M = G @ ((v0, w0) # R0)"
      proof -
        show ?thesis
          apply (subst M)
          by (simp add: butlast_append)
      qed
      have range: "[0..<n] = 0 # [1..<n]"
        using n1 by (simp add: upt_conv_Cons)
      let ?R =
        "concat
          (map
            (\<lambda>k. map (\<lambda>p. (fst p + k * d0, snd p))
              ((v0, w0) # R0))
            [1..<n])"
      have eq: "M\<lbrakk>n\<rbrakk> = butlast M @ ?R"
        using Mn range drop by simp
      have sub: "sndSet ?R \<subseteq> sndSet (butlast M)"
      proof
        fix y
        assume "y \<in> sndSet ?R"
        then obtain x where x: "x \<in> set ?R" and y: "snd x = y"
          by (auto simp: sndSet_def)
        have ex:
          "\<exists>xs\<in>
            set
              (map
                (\<lambda>k. map (\<lambda>p. (fst p + k * d0, snd p))
                  ((v0, w0) # R0))
                [1..<n]).
            x \<in> set xs"
          using x by (auto simp: set_concat)
        then obtain xs where
          xs: "xs \<in>
            set
              (map
                (\<lambda>k. map (\<lambda>p. (fst p + k * d0, snd p))
                  ((v0, w0) # R0))
                [1..<n])"
          "x \<in> set xs"
          by blast
        from xs(1) obtain k where
          "k \<in> set [1..<n]"
          "xs =
            map (\<lambda>p. (fst p + k * d0, snd p)) ((v0, w0) # R0)"
          by auto
        with xs(2) obtain p where
          p: "p \<in> set ((v0, w0) # R0)"
          and xeq: "x = (fst p + k * d0, snd p)"
          by auto
        have "p \<in> set (butlast M)" using p drop by auto
        then show "y \<in> sndSet (butlast M)"
          using y xeq by (auto simp: sndSet_def)
      qed
      show ?thesis using eq sub by blast
    qed
  qed
qed

lemma diagSeq_cons:
  "u \<le> v \<Longrightarrow> diagSeq u v = (u, u) # diagSeq (Suc u) v"
  by (simp add: diagSeq_def upt_conv_Cons)

lemma fst_in_diagSeq:
  "q \<in> set (diagSeq a b) \<Longrightarrow> a \<le> fst q"
  by (auto simp: diagSeq_def)

lemma translate_diagSeq:
  assumes "u \<le> v"
  shows "translate (diagSeq u v) =
    P u (translate (diagSeq (Suc u) v)) Z"
proof -
  have R: "\<forall>x\<in>set (diagSeq (Suc u) v). u < fst x"
    using fst_in_diagSeq by fastforce
  have tw:
    "takeWhile (\<lambda>q. fst (u, u) < fst q) (diagSeq (Suc u) v) =
      diagSeq (Suc u) v"
    using R by (simp add: takeWhile_eq_all_conv)
  have dw:
    "dropWhile (\<lambda>q. fst (u, u) < fst q) (diagSeq (Suc u) v) = []"
    using R by (simp add: dropWhile_eq_Nil_conv)
  show ?thesis
  proof -
    show ?thesis
      apply (subst diagSeq_cons[OF assms])
      apply (subst translate.simps(2))
      apply (subst tw)
      apply (subst dw)
      by simp
  qed
qed

fun cnf :: "three \<Rightarrow> bool" where
  "cnf Z \<longleftrightarrow> True"
| "cnf (P a b Z) \<longleftrightarrow> cnf b"
| "cnf (P a b (P e f g)) \<longleftrightarrow>
    cnf b \<and> \<not> (P a b Z <o P e f Z) \<and> cnf (P e f g)"

lemma cnf_Z [simp]: "cnf Z"
  by simp

lemma cnf_P_Z [simp]: "cnf (P a b Z) \<longleftrightarrow> cnf b"
  by simp

lemma cnf_P_P [simp]:
  "cnf (P a b (P e f g)) \<longleftrightarrow>
    cnf b \<and> \<not> (P a b Z <o P e f Z) \<and> cnf (P e f g)"
  by simp

lemma cnf_translate_diagSeq_aux:
  "cnf (translate (diagSeq u (u + n)))"
proof (induction n arbitrary: u)
  case 0
  have e: "diagSeq (Suc u) u = []" by (simp add: diagSeq_def)
  show ?case using translate_diagSeq[of u u] e by simp
next
  case (Suc n)
  have e: "translate (diagSeq u (u + Suc n)) =
      P u (translate (diagSeq (Suc u) (u + Suc n))) Z"
    using translate_diagSeq[of u "u + Suc n"] by simp
  have shift:
    "diagSeq (Suc u) (u + Suc n) = diagSeq (Suc u) (Suc u + n)"
    by simp
  show ?case using e shift Suc.IH[of "Suc u"] by simp
qed

lemma cnf_diag:
  "cnf (translate (diagSeq 0 v))"
  using cnf_translate_diagSeq_aux[of 0 v] by simp

lemma cnf_snoc:
  assumes "cnf (translate (D @ [m]))"
  shows "cnf (translate D)"
  using assms
proof (induction D rule: translate.induct)
  case 1
  then show ?case by simp
next
  case (2 p rest)
  let ?Q = "\<lambda>q. fst p < fst q"
  let ?tw = "takeWhile ?Q rest"
  let ?dw = "dropWhile ?Q rest"
  show ?case
  proof (cases "\<forall>x\<in>set rest. ?Q x")
    case allp: True
    have tw: "?tw = rest"
      using allp by (simp add: takeWhile_eq_all_conv)
    have dw: "?dw = []"
      using allp by (simp add: dropWhile_eq_Nil_conv)
    have eq0: "translate (p # rest) = P (snd p) (translate rest) Z"
      by (simp only: translate.simps(2) tw dw translate.simps(1))
    show ?thesis
    proof (cases "?Q m")
      case True
      have "cnf (translate (rest @ [m]))"
        using "2.prems" allp True
        by (simp add: takeWhile_eq_all_conv dropWhile_eq_Nil_conv)
      then have "cnf (translate rest)"
        using "2.IH"(1) tw by simp
      then show ?thesis using eq0 by simp
    next
      case False
      have "translate ((p # rest) @ [m]) =
          P (snd p) (translate rest) (P (snd m) Z Z)"
        using allp False
        by (simp add: takeWhile_append2 dropWhile_append2)
      then have "cnf (translate rest)" using "2.prems" by simp
      then show ?thesis using eq0 by simp
    qed
  next
    case notall: False
    then obtain x where x: "x \<in> set rest" "\<not> ?Q x" by blast
    have tw': "takeWhile ?Q (rest @ [m]) = ?tw"
      using x by (simp add: takeWhile_append1)
    have dw': "dropWhile ?Q (rest @ [m]) = ?dw @ [m]"
      using x by (simp add: dropWhile_append1)
    have dwne: "?dw \<noteq> []"
      using x by (auto simp: dropWhile_eq_Nil_conv)
    have hyp:
      "cnf (P (snd p) (translate ?tw) (translate (?dw @ [m])))"
      using "2.prems" tw' dw' by simp
    from dwne obtain q rest2 where dwq: "?dw = q # rest2"
      by (cases ?dw) auto
    let ?R = "\<lambda>y. fst q < fst y"
    let ?f = "translate (takeWhile ?R rest2)"
    let ?f' = "translate (takeWhile ?R (rest2 @ [m]))"
    let ?g = "translate (dropWhile ?R rest2)"
    let ?g' = "translate (dropWhile ?R (rest2 @ [m]))"
    have td: "translate ?dw = P (snd q) ?f ?g"
      using dwq by simp
    have td': "translate (?dw @ [m]) = P (snd q) ?f' ?g'"
      using dwq by simp
    have fle: "?f \<le>o ?f'"
      using translate_takeWhile_snoc_le[of "fst q" rest2 m] by simp
    have H:
      "cnf (translate ?tw) \<and>
       \<not> (P (snd p) (translate ?tw) Z <o P (snd q) ?f' Z) \<and>
       cnf (P (snd q) ?f' ?g')"
      using hyp td' by simp
    have cb: "cnf (translate ?tw)" using H by simp
    have sib': "\<not> (P (snd p) (translate ?tw) Z <o P (snd q) ?f' Z)"
      using H by simp
    have cdw: "cnf (translate ?dw)"
      using "2.IH"(2) H td' by simp
    have leP: "P (snd q) ?f Z \<le>o P (snd q) ?f' Z"
      using fle unfolding ole_def by (auto intro: olt_P_b)
    have sib: "\<not> (P (snd p) (translate ?tw) Z <o P (snd q) ?f Z)"
    proof
      assume "P (snd p) (translate ?tw) Z <o P (snd q) ?f Z"
      from olt_ole_trans[OF this leP] show False using sib' by simp
    qed
    show ?thesis using td cb cdw sib by simp
  qed
qed

lemma cnf_dropLast:
  assumes "C \<noteq> []" "cnf (translate C)"
  shows "cnf (translate (butlast C))"
  using cnf_snoc[of "butlast C" "last C"] assms
  by (simp add: snoc_eq_iff_butlast)

lemma cnf_take:
  assumes "cnf (translate M)"
  shows "cnf (translate (take k M))"
proof (induction "length M - k" arbitrary: k)
  case 0
  then have "take k M = M" by simp
  then show ?case using assms by simp
next
  case (Suc d)
  have klt: "k < length M"
    using Suc.hyps(2) by (cases "k < length M") auto
  have d: "d = length M - Suc k" using Suc.hyps(2) by simp
  have ihk: "cnf (translate (take (Suc k) M))"
    using Suc.hyps(1)[OF d] .
  have ne: "take (Suc k) M \<noteq> []"
    using klt by (auto simp: take_eq_Nil)
  have e: "butlast (take (Suc k) M) = take k M"
  proof -
    have "length (take (Suc k) M) = Suc k" using klt by simp
    then show ?thesis by (simp add: butlast_conv_take take_take)
  qed
  show ?case using cnf_dropLast[OF ne ihk] e by simp
qed

lemma cnf_replicate_block:
  assumes R: "\<forall>x\<in>set R. v0 < fst x"
    and cR: "cnf (translate R)"
  shows "cnf (translate (concat (replicate n ((v0, w0) # R))))"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc m)
  let ?blk = "(v0, w0) # R"
  let ?T = "concat (replicate m ?blk)"
  have hd: "concat (replicate (Suc m) ?blk) = ?blk @ ?T" by simp
  have Tcond: "?T = [] \<or> \<not> v0 < fst (hd ?T)"
    by (cases m) auto
  have tb: "translate (?blk @ ?T) =
      P w0 (translate R) (translate ?T)"
    by (rule translate_block_append[OF R Tcond])
  show ?case
  proof (cases m)
    case 0
    then show ?thesis using hd tb cR by simp
  next
    case (Suc m')
    have tT: "translate ?T =
        P w0 (translate R) (translate (concat (replicate m' ?blk)))"
    proof -
      have e: "?T = ?blk @ concat (replicate m' ?blk)"
        using Suc by simp
      have c:
        "concat (replicate m' ?blk) = [] \<or>
          \<not> v0 < fst (hd (concat (replicate m' ?blk)))"
        by (cases m') auto
      show ?thesis using e translate_block_append[OF R c] by simp
    qed
    have cT: "cnf (translate ?T)" using Suc.IH .
    have irr: "\<not> (P w0 (translate R) Z <o P w0 (translate R) Z)"
      using olt_irrefl by blast
    have "cnf (P w0 (translate R) (translate ?T))"
      using cR cT tT irr by simp
    then show ?thesis using hd tb by simp
  qed
qed

lemma cnf_ctx_cong:
  assumes cZ1: "cnf (translate (z1 # T1))"
    and decr: "translate (z1 # T1) <o translate (z2 # T2)"
    and root: "fst z1 = fst z2"
    and leadle:
      "\<exists>a1 b1 c1 a2 b2 c2.
        translate (z1 # T1) = P a1 b1 c1 \<and>
        translate (z2 # T2) = P a2 b2 c2 \<and>
        P a1 b1 Z \<le>o P a2 b2 Z"
    and r1: "\<forall>x\<in>set T1. fst z1 \<le> fst x"
    and r2: "\<forall>x\<in>set T2. fst z2 \<le> fst x"
    and hG2: "cnf (translate (G @ z2 # T2))"
  shows "cnf (translate (G @ z1 # T1))"
  using hG2
proof (induction G rule: length_induct)
  case (1 G)
  from leadle obtain a1 b1 c1 a2 b2 c2 where
    lZ1: "translate (z1 # T1) = P a1 b1 c1"
    and lZ2: "translate (z2 # T2) = P a2 b2 c2"
    and lle: "P a1 b1 Z \<le>o P a2 b2 Z"
    by blast
  show ?case
  proof (cases G)
    case Nil
    then show ?thesis using cZ1 by simp
  next
    case (Cons g G')
    let ?Qg = "\<lambda>q. fst g < fst q"
    show ?thesis
    proof (cases "\<forall>x\<in>set G'. ?Qg x")
      case allG: True
      show ?thesis
      proof (cases "?Qg z1")
        case True
        have aZ1: "\<forall>x\<in>set (z1 # T1). ?Qg x"
          using True r1 by auto
        have aZ2: "\<forall>x\<in>set (z2 # T2). ?Qg x"
          using True root r2 by auto
        have all1: "\<forall>x\<in>set (G' @ z1 # T1). ?Qg x"
          using allG aZ1 by auto
        have all2: "\<forall>x\<in>set (G' @ z2 # T2). ?Qg x"
          using allG aZ2 by auto
        have tw1: "takeWhile ?Qg (G' @ z1 # T1) = G' @ z1 # T1"
          using all1 by (simp add: takeWhile_eq_all_conv)
        have dw1: "dropWhile ?Qg (G' @ z1 # T1) = []"
          using all1 by (simp add: dropWhile_eq_Nil_conv)
        have tw2: "takeWhile ?Qg (G' @ z2 # T2) = G' @ z2 # T2"
          using all2 by (simp add: takeWhile_eq_all_conv)
        have dw2: "dropWhile ?Qg (G' @ z2 # T2) = []"
          using all2 by (simp add: dropWhile_eq_Nil_conv)
        have e1: "translate (G @ z1 # T1) =
            P (snd g) (translate (G' @ z1 # T1)) Z"
          by (simp only: Cons append_Cons translate.simps(2) tw1 dw1
              translate.simps(1))
        have e2: "translate (G @ z2 # T2) =
            P (snd g) (translate (G' @ z2 # T2)) Z"
          by (simp only: Cons append_Cons translate.simps(2) tw2 dw2
              translate.simps(1))
        have c2: "cnf (translate (G' @ z2 # T2))"
          using "1.prems" e2 by simp
        have len: "length G' < length G" using Cons by simp
        have c1: "cnf (translate (G' @ z1 # T1))"
          using "1.IH"[rule_format, of G'] len c2 by blast
        show ?thesis using e1 c1 by simp
      next
        case False
        have False2: "\<not> ?Qg z2" using False root by simp
        have tw1: "takeWhile ?Qg (G' @ z1 # T1) = G'"
          using allG False by (simp add: takeWhile_append2)
        have dw1: "dropWhile ?Qg (G' @ z1 # T1) = z1 # T1"
          using allG False by (simp add: dropWhile_append2)
        have tw2: "takeWhile ?Qg (G' @ z2 # T2) = G'"
          using allG False2 by (simp add: takeWhile_append2)
        have dw2: "dropWhile ?Qg (G' @ z2 # T2) = z2 # T2"
          using allG False2 by (simp add: dropWhile_append2)
        have e1: "translate (G @ z1 # T1) =
            P (snd g) (translate G') (P a1 b1 c1)"
          using lZ1
          by (simp only: Cons append_Cons translate.simps(2) tw1 dw1)
        have e2: "translate (G @ z2 # T2) =
            P (snd g) (translate G') (P a2 b2 c2)"
          using lZ2
          by (simp only: Cons append_Cons translate.simps(2) tw2 dw2)
        have ctg: "cnf (translate G')"
          and bnd2:
            "\<not> (P (snd g) (translate G') Z <o P a2 b2 Z)"
          using "1.prems" e2 by auto
        have bnd1:
          "\<not> (P (snd g) (translate G') Z <o P a1 b1 Z)"
        proof
          assume "P (snd g) (translate G') Z <o P a1 b1 Z"
          from olt_ole_trans[OF this lle] show False using bnd2 by simp
        qed
        have "cnf (P a1 b1 c1)" using cZ1 lZ1 by simp
        then show ?thesis using e1 ctg bnd1 by simp
      qed
    next
      case notall: False
      then obtain x where x: "x \<in> set G'" and nx: "\<not> ?Qg x"
        by blast
      have tw1: "takeWhile ?Qg (G' @ z1 # T1) = takeWhile ?Qg G'"
        using x nx by (simp add: takeWhile_append1)
      have dw1: "dropWhile ?Qg (G' @ z1 # T1) =
          dropWhile ?Qg G' @ z1 # T1"
        using x nx by (simp add: dropWhile_append1)
      have tw2: "takeWhile ?Qg (G' @ z2 # T2) = takeWhile ?Qg G'"
        using x nx by (simp add: takeWhile_append1)
      have dw2: "dropWhile ?Qg (G' @ z2 # T2) =
          dropWhile ?Qg G' @ z2 # T2"
        using x nx by (simp add: dropWhile_append1)
      let ?D = "dropWhile ?Qg G'"
      have e1: "translate (G @ z1 # T1) =
          P (snd g) (translate (takeWhile ?Qg G'))
            (translate (?D @ z1 # T1))"
        by (simp only: Cons append_Cons translate.simps(2) tw1 dw1)
      have e2: "translate (G @ z2 # T2) =
          P (snd g) (translate (takeWhile ?Qg G'))
            (translate (?D @ z2 # T2))"
        by (simp only: Cons append_Cons translate.simps(2) tw2 dw2)
      have Dne: "?D \<noteq> []"
        using x nx by (auto simp: dropWhile_eq_Nil_conv)
      from Dne obtain d D' where D: "?D = d # D'"
        by (cases ?D) auto
      have p1: "translate (?D @ z1 # T1) =
          P (snd d)
            (translate (takeWhile (\<lambda>y. fst d < fst y)
              (D' @ z1 # T1)))
            (translate (dropWhile (\<lambda>y. fst d < fst y)
              (D' @ z1 # T1)))"
        using D by simp
      have p2: "translate (?D @ z2 # T2) =
          P (snd d)
            (translate (takeWhile (\<lambda>y. fst d < fst y)
              (D' @ z2 # T2)))
            (translate (dropWhile (\<lambda>y. fst d < fst y)
              (D' @ z2 # T2)))"
        using D by simp
      have decrD:
        "translate (?D @ z1 # T1) <o translate (?D @ z2 # T2)"
        by (rule translate_ctx_cong[OF decr root r1 r2])
      have argle:
        "translate (takeWhile (\<lambda>y. fst d < fst y)
            (D' @ z1 # T1)) <o
          translate (takeWhile (\<lambda>y. fst d < fst y)
            (D' @ z2 # T2)) \<or>
         translate (takeWhile (\<lambda>y. fst d < fst y)
            (D' @ z1 # T1)) =
          translate (takeWhile (\<lambda>y. fst d < fst y)
            (D' @ z2 # T2))"
        using decrD p1 p2 by auto
      have ctw: "cnf (translate (takeWhile ?Qg G'))"
        and bnd2:
          "\<not> (P (snd g) (translate (takeWhile ?Qg G')) Z <o
            P (snd d)
              (translate (takeWhile (\<lambda>y. fst d < fst y)
                (D' @ z2 # T2))) Z)"
        and cD2: "cnf (translate (?D @ z2 # T2))"
        using "1.prems" e2 p2 by auto
      have lenD: "length ?D < length G"
        using Cons by (simp add: le_imp_less_Suc length_dropWhile_le)
      have cD1: "cnf (translate (?D @ z1 # T1))"
        using "1.IH"[rule_format, of ?D] lenD cD2 by blast
      have bnd1:
        "\<not> (P (snd g) (translate (takeWhile ?Qg G')) Z <o
          P (snd d)
            (translate (takeWhile (\<lambda>y. fst d < fst y)
              (D' @ z1 # T1))) Z)"
        using argle bnd2 unfolding ole_def
        by (auto intro: olt_trans)
      show ?thesis using e1 p1 ctw bnd1 cD1 by simp
    qed
  qed
qed

lemma cnf_tail:
  assumes rT: "\<forall>x\<in>set T'. fst t \<le> fst x"
    and hGT: "cnf (translate (G @ t # T'))"
  shows "cnf (translate (t # T'))"
  using hGT
proof (induction G rule: length_induct)
  case (1 G)
  show ?case
  proof (cases G)
    case Nil
    then show ?thesis using "1.prems" by simp
  next
    case (Cons g G')
    let ?Qg = "\<lambda>q. fst g < fst q"
    show ?thesis
    proof (cases "\<forall>x\<in>set G'. ?Qg x")
      case allG: True
      show ?thesis
      proof (cases "?Qg t")
        case True
        have aT: "\<forall>x\<in>set (t # T'). ?Qg x"
          using True rT by auto
        have all: "\<forall>x\<in>set (G' @ t # T'). ?Qg x"
          using allG aT by auto
        have tw: "takeWhile ?Qg (G' @ t # T') = G' @ t # T'"
          using all by (simp add: takeWhile_eq_all_conv)
        have dw: "dropWhile ?Qg (G' @ t # T') = []"
          using all by (simp add: dropWhile_eq_Nil_conv)
        have e: "translate (G @ t # T') =
            P (snd g) (translate (G' @ t # T')) Z"
          by (simp only: Cons append_Cons translate.simps(2) tw dw
              translate.simps(1))
        have c: "cnf (translate (G' @ t # T'))"
          using "1.prems" e by simp
        have len: "length G' < length G" using Cons by simp
        show ?thesis
          using "1.IH"[rule_format, of G'] len c by blast
      next
        case False
        have tw: "takeWhile ?Qg (G' @ t # T') = G'"
          using allG False by (simp add: takeWhile_append2)
        have dw: "dropWhile ?Qg (G' @ t # T') = t # T'"
          using allG False by (simp add: dropWhile_append2)
        have e: "translate (G @ t # T') =
            P (snd g) (translate G') (translate (t # T'))"
          by (simp only: Cons append_Cons translate.simps(2) tw dw)
        have nz: "translate (t # T') \<noteq> Z" by simp
        show ?thesis using "1.prems" e nz
          by (cases "translate (t # T')") auto
      qed
    next
      case notall: False
      then obtain x where x: "x \<in> set G'" and nx: "\<not> ?Qg x"
        by blast
      have tw: "takeWhile ?Qg (G' @ t # T') = takeWhile ?Qg G'"
        using x nx by (simp add: takeWhile_append1)
      have dw: "dropWhile ?Qg (G' @ t # T') =
          dropWhile ?Qg G' @ t # T'"
        using x nx by (simp add: dropWhile_append1)
      let ?D = "dropWhile ?Qg G'"
      have e: "translate (G @ t # T') =
          P (snd g) (translate (takeWhile ?Qg G'))
            (translate (?D @ t # T'))"
        by (simp only: Cons append_Cons translate.simps(2) tw dw)
      have Dne: "?D \<noteq> []"
        using x nx by (auto simp: dropWhile_eq_Nil_conv)
      have nz: "translate (?D @ t # T') \<noteq> Z"
        using Dne by (cases "?D @ t # T'") auto
      have cD: "cnf (translate (?D @ t # T'))"
        using "1.prems" e nz
        by (cases "translate (?D @ t # T')") auto
      have len: "length ?D < length G"
        using Cons by (simp add: le_imp_less_Suc length_dropWhile_le)
      show ?thesis
        using "1.IH"[rule_format, of ?D] len cD by blast
    qed
  qed
qed

lemma cnf_oper_i1eq0:
  assumes R: "\<forall>x\<in>set R. v0 < fst x"
    and lpv: "v0 < fst lp"
    and n1: "1 \<le> n"
    and cM:
      "cnf (translate (G @ ((v0, w0) # R) @ [lp]))"
  shows
    "cnf (translate (G @ concat (replicate n ((v0, w0) # R))))"
proof -
  let ?blk = "(v0, w0) # R"
  obtain m where n: "n = Suc m" using n1 by (cases n) auto
  have Rlp: "\<forall>x\<in>set (R @ [lp]). v0 < fst x"
    using R lpv by auto
  have z2:
    "translate ((v0, w0) # (R @ [lp])) =
      P w0 (translate (R @ [lp])) Z"
  proof -
    have tw:
      "takeWhile (\<lambda>q. v0 < fst q) (R @ [lp]) = R @ [lp]"
      using Rlp by (simp add: takeWhile_eq_all_conv)
    have dw:
      "dropWhile (\<lambda>q. v0 < fst q) (R @ [lp]) = []"
      using Rlp by (simp add: dropWhile_eq_Nil_conv)
    show ?thesis
      by (simp only: translate.simps(2) fst_conv snd_conv tw dw
          translate.simps(1))
  qed
  have Tcond:
    "concat (replicate m ?blk) = [] \<or>
      \<not> v0 < fst (hd (concat (replicate m ?blk)))"
    by (cases m) auto
  have e1:
    "concat (replicate n ?blk) =
      (v0, w0) # (R @ concat (replicate m ?blk))"
    using n by simp
  have z1:
    "translate ((v0, w0) # (R @ concat (replicate m ?blk))) =
      P w0 (translate R) (translate (concat (replicate m ?blk)))"
  proof -
    have "translate (?blk @ concat (replicate m ?blk)) =
        P w0 (translate R) (translate (concat (replicate m ?blk)))"
      by (rule translate_block_append[OF R Tcond])
    then show ?thesis by simp
  qed

  have r2: "\<forall>x\<in>set (R @ [lp]). v0 \<le> fst x"
    using Rlp by auto
  have cM':
    "cnf (translate (G @ (v0, w0) # (R @ [lp])))"
    using cM by simp
  have cblk: "cnf (translate ((v0, w0) # (R @ [lp])))"
  proof (rule cnf_tail[where G=G and t="(v0, w0)" and T'="R @ [lp]"])
    show "\<forall>x\<in>set (R @ [lp]). fst (v0, w0) \<le> fst x"
      using r2 by simp
    show "cnf (translate (G @ (v0, w0) # (R @ [lp])))"
      using cM' .
  qed
  have cRlp: "cnf (translate (R @ [lp]))"
    using cblk z2 by simp
  have cR: "cnf (translate R)"
    by (rule cnf_snoc[OF cRlp])
  have cCopies:
    "cnf (translate (concat (replicate n ?blk)))"
    by (rule cnf_replicate_block[OF R cR])
  have cZ1:
    "cnf (translate ((v0, w0) #
      (R @ concat (replicate m ?blk))))"
    using cCopies e1 by simp

  have arglt: "translate R <o translate (R @ [lp])"
    by (rule translate_snoc_increase)
  have decr:
    "translate ((v0, w0) # (R @ concat (replicate m ?blk))) <o
      translate ((v0, w0) # (R @ [lp]))"
    using z1 z2 arglt by (simp add: olt_P_b)
  have lead:
    "\<exists>a1 b1 c1 a2 b2 c2.
      translate ((v0, w0) # (R @ concat (replicate m ?blk))) =
        P a1 b1 c1 \<and>
      translate ((v0, w0) # (R @ [lp])) = P a2 b2 c2 \<and>
      P a1 b1 Z \<le>o P a2 b2 Z"
    using z1 z2 arglt unfolding ole_def by (auto intro: olt_P_b)
  have sub:
    "\<forall>x\<in>set (concat (replicate m ?blk)). x \<in> set ?blk"
  proof (induction m)
    case 0
    then show ?case by simp
  next
    case (Suc m)
    then show ?case by auto
  qed
  have r1:
    "\<forall>x\<in>set (R @ concat (replicate m ?blk)). v0 \<le> fst x"
    using R sub by auto
  have key:
    "cnf (translate (G @ (v0, w0) #
      (R @ concat (replicate m ?blk))))"
  proof (rule cnf_ctx_cong)
    show "cnf (translate ((v0, w0) #
        (R @ concat (replicate m ?blk))))"
      using cZ1 .
    show "translate ((v0, w0) #
        (R @ concat (replicate m ?blk))) <o
        translate ((v0, w0) # (R @ [lp]))"
      using decr .
    show "fst (v0, w0) = fst (v0, w0)" by simp
    show "\<exists>a1 b1 c1 a2 b2 c2.
        translate ((v0, w0) #
          (R @ concat (replicate m ?blk))) = P a1 b1 c1 \<and>
        translate ((v0, w0) # (R @ [lp])) = P a2 b2 c2 \<and>
        P a1 b1 Z \<le>o P a2 b2 Z"
      using lead .
    show "\<forall>x\<in>set (R @ concat (replicate m ?blk)).
        fst (v0, w0) \<le> fst x"
      using r1 by simp
    show "\<forall>x\<in>set (R @ [lp]). fst (v0, w0) \<le> fst x"
      using r2 by simp
    show "cnf (translate (G @ (v0, w0) # (R @ [lp])))"
      using cM' .
  qed
  show ?thesis using key e1 by simp
qed

definition shiftr0 :: "nat \<Rightarrow> pairseq \<Rightarrow> pairseq" where
  "shiftr0 d M = map (\<lambda>p. (fst p + d, snd p)) M"

definition copies :: "nat \<Rightarrow> pairseq \<Rightarrow> nat \<Rightarrow> pairseq" where
  "copies d blk n =
    concat (map (\<lambda>k. shiftr0 (k * d) blk) [0..<n])"

lemma shiftr0_zero [simp]:
  "shiftr0 0 M = M"
  by (simp add: shiftr0_def)

lemma shiftr0_nil [simp]:
  "shiftr0 d [] = []"
  by (simp add: shiftr0_def)

lemma shiftr0_eq_nil [simp]:
  "shiftr0 d M = [] \<longleftrightarrow> M = []"
  by (simp add: shiftr0_def)

lemma translate_shiftr0 [simp]:
  "translate (shiftr0 d M) = translate M"
  by (simp add: shiftr0_def translate_shift)

lemma shiftr0_cons:
  "shiftr0 d (p # M) = (fst p + d, snd p) # shiftr0 d M"
  by (simp add: shiftr0_def)

lemma mem_shiftr0:
  "x \<in> set (shiftr0 d M) \<longleftrightarrow>
    (\<exists>p\<in>set M. (fst p + d, snd p) = x)"
  by (auto simp: shiftr0_def)

lemma copies_zero [simp]:
  "copies d blk 0 = []"
  by (simp add: copies_def)

lemma copies_succ_front:
  "copies d blk (n + 1) = blk @ shiftr0 d (copies d blk n)"
proof -
  have shift_comp:
    "\<And>e M. shiftr0 d (shiftr0 e M) = shiftr0 (d + e) M"
    by (simp add: shiftr0_def comp_def add.commute add.left_commute)
  have shift_concat:
    "\<And>L. shiftr0 d (concat L) = concat (map (shiftr0 d) L)"
  proof -
    fix L
    have f: "shiftr0 d = map (\<lambda>p. (fst p + d, snd p))"
      by (rule ext) (simp add: shiftr0_def)
    show "shiftr0 d (concat L) = concat (map (shiftr0 d) L)"
      using f by (simp add: shiftr0_def map_concat)
  qed
  have tail:
    "shiftr0 d (copies d blk n) =
      concat (map (\<lambda>k. shiftr0 (k * d) blk) [1..<Suc n])"
  proof -
    have "shiftr0 d (copies d blk n) =
        concat (map (\<lambda>k. shiftr0 (d + k * d) blk) [0..<n])"
      by (simp add: copies_def shift_concat shift_comp o_def)
    also have "\<dots> =
        concat (map (\<lambda>k. shiftr0 (k * d) blk) (map Suc [0..<n]))"
      by (simp add: o_def mult_Suc)
    also have "\<dots> =
        concat (map (\<lambda>k. shiftr0 (k * d) blk) [1..<Suc n])"
      by (simp add: map_Suc_upt)
    finally show ?thesis .
  qed
  have range: "[0..<Suc n] = 0 # [1..<Suc n]"
    by (simp add: upt_conv_Cons)
  have "copies d blk (n + 1) =
      blk @ concat (map (\<lambda>k. shiftr0 (k * d) blk) [1..<Suc n])"
    using range by (simp add: copies_def)
  then show ?thesis using tail by simp
qed

lemma copies_one [simp]:
  "copies d blk 1 = blk"
  using copies_succ_front[of d blk 0] by simp

lemma copies_succ_cons:
  "copies d ((v0, w0) # R) (n + 1) =
    (v0, w0) # (R @ shiftr0 d (copies d ((v0, w0) # R) n))"
  using copies_succ_front[of d "(v0, w0) # R" n] by simp

lemma copies_v0_le:
  assumes Rle: "\<forall>x\<in>set R. v0 \<le> fst x"
  shows "\<forall>x\<in>set (copies d ((v0, w0) # R) n). v0 \<le> fst x"
proof
  fix x
  assume x: "x \<in> set (copies d ((v0, w0) # R) n)"
  have ex:
    "\<exists>xs\<in>
      set (map (\<lambda>k. shiftr0 (k * d) ((v0, w0) # R)) [0..<n]).
      x \<in> set xs"
    using x by (auto simp: copies_def set_concat)
  then obtain xs where
    xs: "xs \<in>
      set (map (\<lambda>k. shiftr0 (k * d) ((v0, w0) # R)) [0..<n])"
    "x \<in> set xs"
    by blast
  from xs(1) obtain k where
    "k \<in> set [0..<n]"
    "xs = shiftr0 (k * d) ((v0, w0) # R)"
    by auto
  with xs(2) obtain p where
    p: "p \<in> set ((v0, w0) # R)"
    and xeq: "(fst p + k * d, snd p) = x"
    by (auto simp: mem_shiftr0)
  have "v0 \<le> fst p" using p Rle by auto
  moreover have fx0:
    "fst (fst p + k * d, snd p) = fst x"
    by (rule arg_cong[OF xeq])
  ultimately show "v0 \<le> fst x" using fx0 by simp
qed

lemma copies_tl_gt:
  assumes R: "\<forall>x\<in>set R. v0 < fst x"
    and d: "0 < d" and n1: "1 \<le> n"
  shows "\<forall>x\<in>set
      (R @ shiftr0 d (copies d ((v0, w0) # R) (n - 1))).
    v0 < fst x"
proof
  fix x
  assume "x \<in> set
    (R @ shiftr0 d (copies d ((v0, w0) # R) (n - 1)))"
  then consider
    (inR) "x \<in> set R"
  | (inCopies)
      "x \<in> set (shiftr0 d
        (copies d ((v0, w0) # R) (n - 1)))"
    by auto
  then show "v0 < fst x"
  proof cases
    case inR
    then show ?thesis using R by blast
  next
    case inCopies
    then obtain p where
      p: "p \<in> set (copies d ((v0, w0) # R) (n - 1))"
      and xeq: "(fst p + d, snd p) = x"
      by (auto simp: mem_shiftr0)
    have Rle: "\<forall>x\<in>set R. v0 \<le> fst x"
      using R by auto
    have all: "\<forall>x\<in>set
        (copies d ((v0, w0) # R) (n - 1)). v0 \<le> fst x"
      by (rule copies_v0_le[OF Rle])
    have "v0 \<le> fst p" using all p by blast
    moreover have fx0: "fst (fst p + d, snd p) = fst x"
      by (rule arg_cong[OF xeq])
    ultimately show ?thesis using d fx0 by simp
  qed
qed

lemma cnf_copies:
  assumes R: "\<forall>x\<in>set R. v0 < fst x"
    and d0pos: "0 < d0"
    and w0lt: "w0 < snd lp"
    and lphd: "fst lp = v0 + d0"
    and cBlp: "cnf (translate (((v0, w0) # R) @ [lp]))"
  shows "cnf (translate (copies d0 ((v0, w0) # R) n))"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  let ?blk = "(v0, w0) # R"
  show ?case
  proof (cases n)
    case 0
    have cblk: "cnf (translate ?blk)"
    proof -
      have "cnf (translate (butlast (?blk @ [lp])))"
        by (rule cnf_dropLast[OF _ cBlp]) simp
      then show ?thesis by simp
    qed
    have eq: "copies d0 ?blk (Suc n) = ?blk"
      using 0 copies_one[of d0 ?blk] by simp
    show ?thesis using eq cblk by simp
  next
    case (Suc m)
    have n1: "1 \<le> m + 1" by simp
    have cpcons:
      "copies d0 ?blk (m + 1) =
        (v0, w0) #
          (R @ shiftr0 d0 (copies d0 ?blk m))"
      by (rule copies_succ_cons)
    have z1cons:
      "shiftr0 d0 (copies d0 ?blk (m + 1)) =
        (v0 + d0, w0) #
          shiftr0 d0
            (R @ shiftr0 d0 (copies d0 ?blk m))"
      using cpcons by (simp add: shiftr0_cons)
    have tlgt:
      "\<forall>x\<in>set (R @ shiftr0 d0 (copies d0 ?blk m)).
        v0 < fst x"
      using copies_tl_gt[OF R d0pos n1] by simp
    have st1:
      "translate (copies d0 ?blk (m + 1)) =
        P w0
          (translate
            (R @ shiftr0 d0 (copies d0 ?blk m))) Z"
    proof -
      have "translate
          ((v0, w0) #
            (R @ shiftr0 d0 (copies d0 ?blk m))) =
          P w0
            (translate
              (R @ shiftr0 d0 (copies d0 ?blk m))) Z"
        using translate_single_tree[
          of "R @ shiftr0 d0 (copies d0 ?blk m)" "(v0, w0)"]
          tlgt
        by simp
      then show ?thesis using cpcons by simp
    qed
    have tZ1:
      "translate
          ((v0 + d0, w0) #
            shiftr0 d0
              (R @ shiftr0 d0 (copies d0 ?blk m))) =
        P w0
          (translate
            (R @ shiftr0 d0 (copies d0 ?blk m))) Z"
    proof -
      have "translate
          ((v0 + d0, w0) #
            shiftr0 d0
              (R @ shiftr0 d0 (copies d0 ?blk m))) =
          translate (shiftr0 d0 (copies d0 ?blk (m + 1)))"
        by (simp only: z1cons)
      also have "\<dots> = translate (copies d0 ?blk (m + 1))"
        by (rule translate_shiftr0)
      also have "\<dots> =
          P w0
            (translate
              (R @ shiftr0 d0 (copies d0 ?blk m))) Z"
        by (rule st1)
      finally show ?thesis .
    qed
    have tlp: "translate [lp] = P (snd lp) Z Z"
      by simp
    have decr:
      "translate
          ((v0 + d0, w0) #
            shiftr0 d0
              (R @ shiftr0 d0 (copies d0 ?blk m))) <o
        translate [lp]"
      using tZ1 tlp w0lt by (simp add: olt_P_P)
    have cZ1:
      "cnf
        (translate
          ((v0 + d0, w0) #
            shiftr0 d0
              (R @ shiftr0 d0 (copies d0 ?blk m))))"
    proof -
      have cp:
        "cnf (translate (copies d0 ?blk (m + 1)))"
        using Suc.IH Suc by simp
      have "cnf
          (translate (shiftr0 d0 (copies d0 ?blk (m + 1))))"
        using cp by simp
      then show ?thesis by (simp only: z1cons)
    qed
    have r1:
      "\<forall>x\<in>set
          (shiftr0 d0
            (R @ shiftr0 d0 (copies d0 ?blk m))).
        fst (v0 + d0, w0) \<le> fst x"
    proof
      fix x
      assume x:
        "x \<in> set
          (shiftr0 d0
            (R @ shiftr0 d0 (copies d0 ?blk m)))"
      then obtain p where
        p: "p \<in> set
          (R @ shiftr0 d0 (copies d0 ?blk m))"
        and xeq: "(fst p + d0, snd p) = x"
        by (auto simp: mem_shiftr0)
      have vplt: "v0 < fst p" using tlgt p by blast
      have vp: "v0 \<le> fst p" using vplt by simp
      have fx: "fst (fst p + d0, snd p) = fst x"
        by (rule arg_cong[OF xeq])
      show "fst (v0 + d0, w0) \<le> fst x"
        using vp fx by simp
    qed
    have root: "fst (v0 + d0, w0) = fst lp"
      using lphd by simp
    have leadle:
      "\<exists>a1 b1 c1 a2 b2 c2.
        translate
            ((v0 + d0, w0) #
              shiftr0 d0
                (R @ shiftr0 d0 (copies d0 ?blk m))) =
          P a1 b1 c1 \<and>
        translate [lp] = P a2 b2 c2 \<and>
        P a1 b1 Z \<le>o P a2 b2 Z"
      using tZ1 tlp w0lt unfolding ole_def
      by (auto intro: olt_P_P)
    have key:
      "cnf
        (translate
          (?blk @
            (v0 + d0, w0) #
              shiftr0 d0
                (R @ shiftr0 d0 (copies d0 ?blk m))))"
    proof (rule cnf_ctx_cong)
      show "cnf
          (translate
            ((v0 + d0, w0) #
              shiftr0 d0
                (R @ shiftr0 d0 (copies d0 ?blk m))))"
        using cZ1 .
      show "translate
            ((v0 + d0, w0) #
              shiftr0 d0
                (R @ shiftr0 d0 (copies d0 ?blk m))) <o
          translate (lp # [])"
        using decr by simp
      show "fst (v0 + d0, w0) = fst lp"
        using root .
      show "\<exists>a1 b1 c1 a2 b2 c2.
          translate
              ((v0 + d0, w0) #
                shiftr0 d0
                  (R @ shiftr0 d0 (copies d0 ?blk m))) =
            P a1 b1 c1 \<and>
          translate (lp # []) = P a2 b2 c2 \<and>
          P a1 b1 Z \<le>o P a2 b2 Z"
        using leadle by simp
      show "\<forall>x\<in>set
          (shiftr0 d0
            (R @ shiftr0 d0 (copies d0 ?blk m))).
          fst (v0 + d0, w0) \<le> fst x"
        using r1 .
      show "\<forall>x\<in>set []. fst lp \<le> fst x" by simp
      show "cnf (translate (?blk @ lp # []))"
        using cBlp by simp
    qed
    have target:
      "copies d0 ?blk (Suc (Suc m)) =
        ?blk @
          (v0 + d0, w0) #
            shiftr0 d0
              (R @ shiftr0 d0 (copies d0 ?blk m))"
      using z1cons
        copies_succ_front[of d0 ?blk "m + 1"]
      by simp
    show ?thesis using Suc target key by simp
  qed
qed

lemma cnf_oper_i1eq1:
  assumes R: "\<forall>x\<in>set R. v0 < fst x"
    and d0pos: "0 < d0"
    and w0lt: "w0 < snd lp"
    and lphd: "fst lp = v0 + d0"
    and n1: "1 \<le> n"
    and cM:
      "cnf (translate (G @ ((v0, w0) # R) @ [lp]))"
  shows
    "cnf
      (translate
        (G @ copies d0 ((v0, w0) # R) n))"
proof -
  let ?blk = "(v0, w0) # R"
  obtain m where n: "n = m + 1"
    using n1 by (cases n) auto
  have lpv: "v0 < fst lp"
    using d0pos lphd by simp
  have Rlp_gt: "\<forall>x\<in>set (R @ [lp]). v0 < fst x"
    using R lpv by auto
  have decr:
    "translate (copies d0 ?blk (m + 1)) <o
      translate (?blk @ [lp])"
  proof (cases m)
    case 0
    have eq: "copies d0 ?blk (m + 1) = ?blk"
      using 0 copies_one[of d0 ?blk] by simp
    show ?thesis
      by (subst eq; rule translate_snoc_increase)
  next
    case (Suc m')
    have cpcons:
      "copies d0 ?blk (m' + 1) =
        (v0, w0) #
          (R @ shiftr0 d0 (copies d0 ?blk m'))"
      by (rule copies_succ_cons)
    have z1cons:
      "shiftr0 d0 (copies d0 ?blk (m' + 1)) =
        (v0 + d0, w0) #
          shiftr0 d0
            (R @ shiftr0 d0 (copies d0 ?blk m'))"
      using cpcons by (simp add: shiftr0_cons)
    have tlgt:
      "\<forall>x\<in>set
          (R @ shiftr0 d0 (copies d0 ?blk m')).
        v0 < fst x"
      using copies_tl_gt[
        OF R d0pos, of "m' + 1" w0]
      by simp
    have Cge:
      "\<forall>x\<in>set
          (shiftr0 d0
            (R @ shiftr0 d0 (copies d0 ?blk m'))).
        fst (v0 + d0, w0) \<le> fst x"
    proof
      fix x
      assume x:
        "x \<in> set
          (shiftr0 d0
            (R @ shiftr0 d0 (copies d0 ?blk m')))"
      then obtain p where
        p: "p \<in> set
          (R @ shiftr0 d0 (copies d0 ?blk m'))"
        and xeq: "(fst p + d0, snd p) = x"
        by (auto simp: mem_shiftr0)
      have vplt: "v0 < fst p" using tlgt p by blast
      have fx: "fst (fst p + d0, snd p) = fst x"
        by (rule arg_cong[OF xeq])
      show "fst (v0 + d0, w0) \<le> fst x"
        using vplt fx by simp
    qed
    have Croot: "fst (v0 + d0, w0) = fst lp"
      using lphd by simp
    have core:
      "translate
          (?blk @
            (v0 + d0, w0) #
              shiftr0 d0
                (R @ shiftr0 d0 (copies d0 ?blk m'))) <o
        translate (?blk @ [lp])"
      by (rule core_i1[OF R Cge Croot lpv]) (use w0lt in simp)
    have eq:
      "copies d0 ?blk (m' + 1 + 1) =
        ?blk @
          (v0 + d0, w0) #
            shiftr0 d0
              (R @ shiftr0 d0 (copies d0 ?blk m'))"
      using z1cons
        copies_succ_front[of d0 ?blk "m' + 1"]
      by simp
    show ?thesis using Suc eq core by simp
  qed

  have cpcons:
    "copies d0 ?blk (m + 1) =
      (v0, w0) #
        (R @ shiftr0 d0 (copies d0 ?blk m))"
    by (rule copies_succ_cons)
  have tlgt:
    "\<forall>x\<in>set
        (R @ shiftr0 d0 (copies d0 ?blk m)).
      v0 < fst x"
    using copies_tl_gt[OF R d0pos, of "m + 1" w0]
    by simp
  have st1:
    "translate (copies d0 ?blk (m + 1)) =
      P w0
        (translate
          (R @ shiftr0 d0 (copies d0 ?blk m))) Z"
  proof -
    have "translate
        ((v0, w0) #
          (R @ shiftr0 d0 (copies d0 ?blk m))) =
        P w0
          (translate
            (R @ shiftr0 d0 (copies d0 ?blk m))) Z"
      using translate_single_tree[
        of "R @ shiftr0 d0 (copies d0 ?blk m)" "(v0, w0)"]
        tlgt
      by simp
    then show ?thesis using cpcons by simp
  qed
  have st2:
    "translate (?blk @ [lp]) =
      P w0 (translate (R @ [lp])) Z"
    using translate_single_tree[
      of "R @ [lp]" "(v0, w0)"] Rlp_gt
    by simp
  have rT:
    "\<forall>x\<in>set (R @ [lp]).
      fst (v0, w0) \<le> fst x"
    using Rlp_gt by auto
  have cM':
    "cnf (translate (G @ (v0, w0) # (R @ [lp])))"
    using cM by simp
  have cBlp:
    "cnf (translate (?blk @ [lp]))"
  proof -
    have "cnf (translate ((v0, w0) # (R @ [lp])))"
    proof (rule cnf_tail)
      show "\<forall>x\<in>set (R @ [lp]).
          fst (v0, w0) \<le> fst x"
        using rT .
      show "cnf
          (translate (G @ (v0, w0) # (R @ [lp])))"
        using cM' .
    qed
    then show ?thesis by simp
  qed
  have cCopies:
    "cnf (translate (copies d0 ?blk (m + 1)))"
    by (rule cnf_copies[
      OF R d0pos w0lt lphd cBlp])
  have argA:
    "translate
        (R @ shiftr0 d0 (copies d0 ?blk m)) <o
      translate (R @ [lp])"
  proof -
    have "P w0
          (translate
            (R @ shiftr0 d0 (copies d0 ?blk m))) Z <o
        P w0 (translate (R @ [lp])) Z"
      using decr st1 st2 by simp
    then show ?thesis
      by (simp add: olt_P_P)
  qed
  have leadle:
    "\<exists>a1 b1 c1 a2 b2 c2.
      translate
          ((v0, w0) #
            (R @ shiftr0 d0 (copies d0 ?blk m))) =
        P a1 b1 c1 \<and>
      translate ((v0, w0) # (R @ [lp])) =
        P a2 b2 c2 \<and>
      P a1 b1 Z \<le>o P a2 b2 Z"
  proof -
    have e1:
      "translate
          ((v0, w0) #
            (R @ shiftr0 d0 (copies d0 ?blk m))) =
        P w0
          (translate
            (R @ shiftr0 d0 (copies d0 ?blk m))) Z"
      using cpcons st1 by simp
    have e2:
      "translate ((v0, w0) # (R @ [lp])) =
        P w0 (translate (R @ [lp])) Z"
      using st2 by simp
    have "P w0
          (translate
            (R @ shiftr0 d0 (copies d0 ?blk m))) Z
        \<le>o P w0 (translate (R @ [lp])) Z"
      unfolding ole_def using argA
      by (auto intro: olt_P_b)
    then show ?thesis using e1 e2 by blast
  qed
  have decr':
    "translate
        ((v0, w0) #
          (R @ shiftr0 d0 (copies d0 ?blk m))) <o
      translate ((v0, w0) # (R @ [lp]))"
    using decr cpcons by simp
  have cCopies':
    "cnf
      (translate
        ((v0, w0) #
          (R @ shiftr0 d0 (copies d0 ?blk m))))"
    using cCopies cpcons by simp
  have r1:
    "\<forall>x\<in>set
        (R @ shiftr0 d0 (copies d0 ?blk m)).
      fst (v0, w0) \<le> fst x"
  proof
    fix x
    assume x:
      "x \<in> set
        (R @ shiftr0 d0 (copies d0 ?blk m))"
    have "v0 < fst x" using tlgt x by blast
    then show "fst (v0, w0) \<le> fst x" by simp
  qed
  have key:
    "cnf
      (translate
        (G @ (v0, w0) #
          (R @ shiftr0 d0 (copies d0 ?blk m))))"
  proof (rule cnf_ctx_cong)
    show "cnf
        (translate
          ((v0, w0) #
            (R @ shiftr0 d0 (copies d0 ?blk m))))"
      using cCopies' .
    show "translate
          ((v0, w0) #
            (R @ shiftr0 d0 (copies d0 ?blk m))) <o
        translate ((v0, w0) # (R @ [lp]))"
      using decr' .
    show "fst (v0, w0) = fst (v0, w0)" by simp
    show "\<exists>a1 b1 c1 a2 b2 c2.
        translate
            ((v0, w0) #
              (R @ shiftr0 d0 (copies d0 ?blk m))) =
          P a1 b1 c1 \<and>
        translate ((v0, w0) # (R @ [lp])) =
          P a2 b2 c2 \<and>
        P a1 b1 Z \<le>o P a2 b2 Z"
      using leadle .
    show "\<forall>x\<in>set
        (R @ shiftr0 d0 (copies d0 ?blk m)).
        fst (v0, w0) \<le> fst x"
      using r1 .
    show "\<forall>x\<in>set (R @ [lp]).
        fst (v0, w0) \<le> fst x"
      using rT .
    show "cnf (translate (G @ (v0, w0) # (R @ [lp])))"
      using cM' .
  qed
  show ?thesis using n cpcons key by simp
qed

lemma copies_replicate:
  "copies 0 blk n = concat (replicate n blk)"
proof -
  have "copies 0 blk n =
      concat (map (\<lambda>k. blk) [0..<n])"
    by (simp add: copies_def)
  also have "map (\<lambda>k. blk) [0..<n] =
      replicate n blk"
    by (simp add: map_replicate_const)
  finally show ?thesis .
qed

lemma cnf_oper:
  assumes n: "1 \<le> n"
    and cM: "cnf (translate M)"
  shows "cnf (translate (M\<lbrakk>n\<rbrakk>))"
proof (cases "length M - 1 = 0")
  case True
  have eq: "M\<lbrakk>n\<rbrakk> = M"
    by (rule oper_eq_self_of_short[OF True])
  show ?thesis using cM eq by simp
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
    have "cnf (translate (butlast M))"
      by (rule cnf_dropLast[OF Mne cM])
    then show ?thesis using eq hPred by simp
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
      have "cnf (translate (butlast M))"
        by (rule cnf_dropLast[OF Mne cM])
      then show ?thesis using eq hPred by simp
    next
      case hp: True
      obtain G v0 w0 R d0 lp where
        Meq: "M = G @ ((v0, w0) # R) @ [lp]"
        and Mneq:
          "M\<lbrakk>n\<rbrakk> =
            G @ concat
              (map
                (\<lambda>k.
                  map
                    (\<lambda>p.
                      (fst p + k * d0, snd p))
                    ((v0, w0) # R))
                [0..<n])"
        and R: "\<forall>x\<in>set R. v0 < fst x"
        and lpv: "v0 < fst lp"
        and disj:
          "(d0 = 0 \<and>
              idx1 M (length M - 1) = 0) \<or>
           (0 < d0 \<and> w0 < snd lp \<and>
              fst lp = v0 + d0 \<and>
              nextrel1 M (length G)
                (length M - 1))"
        and np:
          "nextR M (idx1 M (length M - 1))
            (length G) (length M - 1)"
        by (rule oper_bad_blocks[OF L1 nz hp n])
      have raweq:
        "concat
            (map
              (\<lambda>k.
                map
                  (\<lambda>p. (fst p + k * d0, snd p))
                  ((v0, w0) # R))
              [0..<n]) =
          copies d0 ((v0, w0) # R) n"
        by (simp add: copies_def shiftr0_def)
      have cM':
        "cnf
          (translate
            (G @ ((v0, w0) # R) @ [lp]))"
        using cM Meq by simp
      consider
        (z) "d0 = 0"
      | (pos) "0 < d0" "w0 < snd lp"
          "fst lp = v0 + d0"
        using disj by blast
      then show ?thesis
      proof cases
        case z
        have eq:
          "M\<lbrakk>n\<rbrakk> =
            G @ copies 0 ((v0, w0) # R) n"
          using Mneq raweq z by simp
        have c:
          "cnf
            (translate
              (G @
                concat
                  (replicate n ((v0, w0) # R))))"
          by (rule cnf_oper_i1eq0[OF R lpv n cM'])
        show ?thesis
          using c eq copies_replicate[
            of "(v0, w0) # R" n]
          by simp
      next
        case pos
        have eq:
          "M\<lbrakk>n\<rbrakk> =
            G @ copies d0 ((v0, w0) # R) n"
          using Mneq raweq by simp
        have c:
          "cnf
            (translate
              (G @ copies d0 ((v0, w0) # R) n))"
          by (rule cnf_oper_i1eq1[
            OF R pos(1) pos(2) pos(3) n cM'])
        show ?thesis using c eq by simp
      qed
    qed
  qed
qed

lemma cnf_ST_PS:
  assumes "ST_PS M"
  shows "cnf (translate M)"
  using assms
proof (induction rule: ST_PS.induct)
  case (diag v)
  then show ?case by (rule cnf_diag)
next
  case (oper M n)
  show ?case by (rule cnf_oper[OF oper.hyps(2) oper.IH])
qed

end
