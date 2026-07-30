theory Decrease
  imports Term
begin

lemma oper_eq_self_of_short:
  "length M - 1 = 0 \<Longrightarrow> M\<lbrakk>n\<rbrakk> = M"
  unfolding oper_def Let_def by simp

lemma oper_eq_pred_of_zero:
  assumes "length M - 1 \<noteq> 0"
    and "entry M 0 (length M - 1) = 0 \<and>
      entry M 1 (length M - 1) = 0"
  shows "M\<lbrakk>n\<rbrakk> = Pred M"
  unfolding oper_def Let_def using assms by simp

lemma oper_eq_pred_of_noParent:
  assumes "length M - 1 \<noteq> 0"
    and "\<not> (entry M 0 (length M - 1) = 0 \<and>
      entry M 1 (length M - 1) = 0)"
    and "\<not> hasParent M (idx1 M (length M - 1)) (length M - 1)"
  shows "M\<lbrakk>n\<rbrakk> = Pred M"
proof -
  show ?thesis
    unfolding oper_def Let_def
    by (simp only: if_not_P[OF assms(1)] if_not_P[OF assms(2)]
        if_P[OF assms(3)])
qed

lemma oper_bad_unfold:
  assumes hL: "length M - 1 \<noteq> 0"
    and hz: "\<not> (entry M 0 (length M - 1) = 0 \<and>
      entry M 1 (length M - 1) = 0)"
    and hp: "hasParent M (idx1 M (length M - 1)) (length M - 1)"
  shows "M\<lbrakk>n\<rbrakk> =
    take (parent M (idx1 M (length M - 1)) (length M - 1)) M @
    concat
      (map
        (\<lambda>k. map
          (\<lambda>j.
            (entry M 0 j +
              k * (if 0 < idx1 M (length M - 1)
                then entry M 0 (length M - 1) -
                  entry M 0
                    (parent M (idx1 M (length M - 1)) (length M - 1))
                else 0),
             entry M 1 j))
          [parent M (idx1 M (length M - 1)) (length M - 1)
            ..< length M - 1])
        [0..<n])"
proof -
  have d1z: "\<not> 1 < idx1 M (length M - 1)"
    using idx1_le1[of M "length M - 1"] by simp
  have nhp:
    "\<not> (\<not> hasParent M (idx1 M (length M - 1)) (length M - 1))"
    using hp by simp
  show ?thesis
    unfolding oper_def Let_def
    by (simp only: if_not_P[OF hL] if_not_P[OF hz]
        if_not_P[OF nhp] if_not_P[OF d1z];
        simp)
qed

lemma oper_eq_self_short:
  "length M \<le> 1 \<Longrightarrow> M\<lbrakk>n\<rbrakk> = M"
  by (rule oper_eq_self_of_short) simp

lemma translate_snoc_increase:
  "translate C <o translate (C @ [m])"
proof (induction C rule: translate.induct)
  case 1
  then show ?case by simp
next
  case (2 p rest)
  let ?Q = "\<lambda>q. fst p < fst q"
  show ?case
  proof (cases "\<forall>x\<in>set rest. ?Q x")
    case allp: True
    have tw: "takeWhile ?Q rest = rest"
      using allp by (simp add: takeWhile_eq_all_conv)
    have dw: "dropWhile ?Q rest = []"
      using allp by (simp add: dropWhile_eq_Nil_conv)
    show ?thesis
    proof (cases "?Q m")
      case True
      have tw': "takeWhile ?Q (rest @ [m]) = rest @ [m]"
        using allp True by (simp add: takeWhile_eq_all_conv)
      have dw': "dropWhile ?Q (rest @ [m]) = []"
        using allp True by (simp add: dropWhile_eq_Nil_conv)
      have key: "translate rest <o translate (rest @ [m])"
        using "2.IH"(1) tw by simp
      show ?thesis using key by (simp add: tw dw tw' dw')
    next
      case False
      have tw': "takeWhile ?Q (rest @ [m]) = rest"
        using allp False by (simp add: takeWhile_append2)
      have dw': "dropWhile ?Q (rest @ [m]) = [m]"
        using allp False by (simp add: dropWhile_append2)
      show ?thesis by (simp add: tw dw tw' dw')
    qed
  next
    case False
    then obtain x where x: "x \<in> set rest" and nx: "\<not> ?Q x"
      by blast
    have tw': "takeWhile ?Q (rest @ [m]) = takeWhile ?Q rest"
      using x nx by (simp add: takeWhile_append1)
    have dw': "dropWhile ?Q (rest @ [m]) = dropWhile ?Q rest @ [m]"
      using x nx by (simp add: dropWhile_append1)
    have key:
      "translate (dropWhile ?Q rest) <o
        translate (dropWhile ?Q rest @ [m])"
      using "2.IH"(2) by simp
    show ?thesis using key by (simp add: tw' dw')
  qed
qed

lemma translate_dropLast_decrease:
  "C \<noteq> [] \<Longrightarrow> translate (butlast C) <o translate C"
  using translate_snoc_increase[of "butlast C" "last C"]
  by (simp add: snoc_eq_iff_butlast)

lemma translate_takeWhile_snoc_le:
  "translate (takeWhile (\<lambda>x. a < fst x) C) \<le>o
    translate (takeWhile (\<lambda>x. a < fst x) (C @ [m]))"
proof (cases "\<forall>x\<in>set C. a < fst x")
  case True
  then have twC: "takeWhile (\<lambda>x. a < fst x) C = C"
    by (simp add: takeWhile_eq_all_conv)
  show ?thesis
  proof (cases "a < fst m")
    case True
    then have e:
      "takeWhile (\<lambda>x. a < fst x) (C @ [m]) = C @ [m]"
      using \<open>\<forall>x\<in>set C. a < fst x\<close>
      by (simp add: takeWhile_eq_all_conv)
    show ?thesis
      unfolding ole_def twC e using translate_snoc_increase by blast
  next
    case False
    then have e:
      "takeWhile (\<lambda>x. a < fst x) (C @ [m]) = C"
      using \<open>\<forall>x\<in>set C. a < fst x\<close>
      by (simp add: takeWhile_append2)
    show ?thesis unfolding ole_def twC e by simp
  qed
next
  case False
  then obtain x where "x \<in> set C" "\<not> a < fst x" by blast
  then have
    "takeWhile (\<lambda>x. a < fst x) (C @ [m]) =
      takeWhile (\<lambda>x. a < fst x) C"
    by (simp add: takeWhile_append1)
  then show ?thesis unfolding ole_def by simp
qed

lemma core_i0:
  assumes R: "\<forall>x\<in>set R. v0 < fst x"
    and vl: "v0 < fst lp"
    and T: "T = [] \<or> \<not> v0 < fst (hd T)"
  shows "translate (((v0, w0) # R) @ T) <o
    translate (((v0, w0) # R) @ [lp])"
proof -
  have lhs:
    "translate (((v0, w0) # R) @ T) =
      P w0 (translate R) (translate T)"
    by (rule translate_block_append[OF R T])
  have rhs:
    "translate (((v0, w0) # R) @ [lp]) =
      P w0 (translate (R @ [lp])) Z"
  proof -
    have all: "\<forall>x\<in>set (R @ [lp]). fst (v0, w0) < fst x"
      using R vl by auto
    have "translate ((v0, w0) # (R @ [lp])) =
        P (snd (v0, w0)) (translate (R @ [lp])) Z"
      by (rule translate_single_tree[OF all])
    then show ?thesis by simp
  qed
  show ?thesis
    using lhs rhs translate_snoc_increase[of R lp] by (simp add: olt_P_b)
qed

lemma core_i1:
  assumes R: "\<forall>x\<in>set R. v0 < fst x"
    and Cge: "\<forall>x\<in>set C'. fst c \<le> fst x"
    and Croot: "fst c = fst lp"
    and lpv: "v0 < fst lp"
    and lead_lt: "snd c < snd lp"
  shows "translate (((v0, w0) # R) @ (c # C')) <o
    translate (((v0, w0) # R) @ [lp])"
proof -
  have hCdom: "translate (c # C') <o translate [lp]"
  proof -
    have leadC: "lead (translate (c # C')) = snd c"
      by (simp add: lead_translate)
    have "translate (c # C') <o P (snd lp) Z Z"
      by (rule olt_P_of_lead_lt) (use leadC lead_lt in auto)
    then show ?thesis by simp
  qed
  have inner:
    "translate (R @ c # C') <o translate (R @ lp # [])"
    by (rule translate_ctx_cong[OF hCdom Croot Cge]) simp
  have allRC: "\<forall>x\<in>set (R @ c # C'). fst (v0, w0) < fst x"
    using R Cge Croot lpv by auto
  have allRlp: "\<forall>x\<in>set (R @ [lp]). fst (v0, w0) < fst x"
    using R lpv by auto
  have lhs:
    "translate (((v0, w0) # R) @ (c # C')) =
      P w0 (translate (R @ c # C')) Z"
    using translate_single_tree[OF allRC] by simp
  have rhs:
    "translate (((v0, w0) # R) @ [lp]) =
      P w0 (translate (R @ [lp])) Z"
    using translate_single_tree[OF allRlp] by simp
  show ?thesis using inner lhs rhs by (simp add: olt_P_b)
qed

lemma translate_oper_pred:
  assumes L: "1 < length M"
    and br:
      "(entry M 0 (length M - 1) = 0 \<and>
          entry M 1 (length M - 1) = 0) \<or>
       \<not> hasParent M (idx1 M (length M - 1)) (length M - 1)"
  shows "translate (M\<lbrakk>n\<rbrakk>) <o translate M"
proof -
  from L have j1: "length M - 1 \<noteq> 0" by simp
  have "M\<lbrakk>n\<rbrakk> = Pred M"
    using br
  proof
    assume "entry M 0 (length M - 1) = 0 \<and>
      entry M 1 (length M - 1) = 0"
    then show ?thesis by (rule oper_eq_pred_of_zero[OF j1])
  next
    assume np:
      "\<not> hasParent M (idx1 M (length M - 1)) (length M - 1)"
    show ?thesis
    proof (cases "entry M 0 (length M - 1) = 0 \<and>
        entry M 1 (length M - 1) = 0")
      case True
      then show ?thesis by (rule oper_eq_pred_of_zero[OF j1])
    next
      case False
      then show ?thesis by (rule oper_eq_pred_of_noParent[OF j1 _ np])
    qed
  qed
  moreover have "Pred M = butlast M"
    using L by (simp add: Pred_def)
  moreover have "M \<noteq> []" using L by auto
  ultimately show ?thesis using translate_dropLast_decrease by simp
qed

lemma parent_nextR:
  assumes hp: "hasParent M i j1"
  shows "nextR M i (parent M i j1) j1"
proof -
  have "\<exists>j0. nextR M i j0 j1"
    using hp unfolding hasParent_def by blast
  then show ?thesis unfolding parent_def by (rule someI_ex)
qed

lemma nextR_index_lt:
  "nextR M i j0 j1 \<Longrightarrow> j0 < j1"
  by (auto simp: nextR_def nextrel0_def nextrel1_def split: if_splits)

lemma nextR_chain0:
  assumes "nextR M i j0 j1"
  shows "(nextrel0 M)\<^sup>*\<^sup>* j0 j1"
proof (cases "i = 0")
  case True
  with assms have "nextrel0 M j0 j1" by (simp add: nextR_def)
  then show ?thesis by (rule r_into_rtranclp)
next
  case False
  with assms have "nextrel1 M j0 j1" by (simp add: nextR_def)
  then show ?thesis by (simp add: nextrel1_def le0_def)
qed

lemma oper_bad_blocks:
  assumes L: "1 < length M"
    and hz: "\<not> (entry M 0 (length M - 1) = 0 \<and>
      entry M 1 (length M - 1) = 0)"
    and hp: "hasParent M (idx1 M (length M - 1)) (length M - 1)"
    and hn: "1 \<le> n"
  obtains G v0 w0 R d0 lp where
    "M = G @ ((v0, w0) # R) @ [lp]"
    "M\<lbrakk>n\<rbrakk> =
      G @ concat
        (map
          (\<lambda>k. map (\<lambda>p. (fst p + k * d0, snd p))
            ((v0, w0) # R))
          [0..<n])"
    "\<forall>x\<in>set R. v0 < fst x"
    "v0 < fst lp"
    "(d0 = 0 \<and> idx1 M (length M - 1) = 0) \<or>
      (0 < d0 \<and> w0 < snd lp \<and> fst lp = v0 + d0 \<and>
        nextrel1 M (length G) (length M - 1))"
    "nextR M (idx1 M (length M - 1)) (length G) (length M - 1)"
proof -
  let ?j1 = "length M - 1"
  let ?i1 = "idx1 M ?j1"
  let ?j0 = "parent M ?i1 ?j1"
  let ?d0 =
    "if 0 < ?i1 then entry M 0 ?j1 - entry M 0 ?j0 else (0::nat)"
  let ?sh = "\<lambda>k j. (entry M 0 j + k * ?d0, entry M 1 j)"
  let ?B = "map (?sh 0) [?j0..<?j1]"
  let ?R = "map (?sh 0) [Suc ?j0..<?j1]"
  let ?cps = "concat (map (\<lambda>k. map (?sh k) [?j0..<?j1]) [0..<n])"
  let ?lp = "M ! ?j1"
  let ?v0 = "entry M 0 ?j0"
  let ?w0 = "entry M 1 ?j0"

  have np: "nextR M ?i1 ?j0 ?j1"
    by (rule parent_nextR[OF hp])
  have j0lt: "?j0 < ?j1"
    by (rule nextR_index_lt[OF np])
  have chain: "(nextrel0 M)\<^sup>*\<^sup>* ?j0 ?j1"
    by (rule nextR_chain0[OF np])
  have iv: "\<And>k. ?j0 < k \<Longrightarrow> k \<le> ?j1 \<Longrightarrow>
      ?v0 < entry M 0 k"
    using le0_interval_gt[OF chain] by blast
  have lenM: "length M = Suc ?j1" using L by simp
  have j1len: "?j1 < length M" using lenM by simp
  have j0len: "?j0 < length M" using j0lt j1len by simp

  have B_eq: "?B = (?v0, ?w0) # ?R"
  proof -
    have "[?j0..<?j1] = ?j0 # [Suc ?j0..<?j1]"
      using j0lt by (simp add: upt_conv_Cons)
    then show ?thesis by simp
  qed
  have R_gt: "\<forall>x\<in>set ?R. ?v0 < fst x"
  proof
    fix x
    assume "x \<in> set ?R"
    then obtain j where j: "j \<in> set [Suc ?j0..<?j1]"
      and x: "x = ?sh 0 j" by auto
    from j have "?j0 < j" "j \<le> ?j1" by auto
    then have "?v0 < entry M 0 j" by (rule iv)
    then show "?v0 < fst x" using x by simp
  qed
  have lp0: "fst ?lp = entry M 0 ?j1"
    using j1len by (simp add: entry_def)
  have lp1: "snd ?lp = entry M 1 ?j1"
    using j1len by (simp add: entry_def)
  have lp_gt: "?v0 < fst ?lp"
    using iv[OF j0lt order_refl] lp0 by simp

  have drop_nth:
    "drop ?j0 M = map ((!) M) [?j0..<length M]"
  proof (rule nth_equalityI)
    show "length (drop ?j0 M) =
        length (map ((!) M) [?j0..<length M])"
      using j0len by simp
  next
    fix i
    assume "i < length (drop ?j0 M)"
    then show "drop ?j0 M ! i =
        map ((!) M) [?j0..<length M] ! i"
      by (simp add: nth_drop)
  qed
  have range_split:
    "[?j0..<length M] = [?j0..<?j1] @ [?j1]"
  proof -
    have "?j0 \<le> ?j1" using j0lt by simp
    then show ?thesis by (metis lenM upt_Suc_append)
  qed
  have nth_B:
    "map ((!) M) [?j0..<?j1] = ?B"
  proof (rule map_cong)
    show "[?j0..<?j1] = [?j0..<?j1]" by simp
  next
    fix j
    assume "j \<in> set [?j0..<?j1]"
    then have "j < length M" using j1len by auto
    then show "M ! j = ?sh 0 j"
      by (simp add: entry_def prod_eq_iff)
  qed
  have dropM: "drop ?j0 M = ?B @ [?lp]"
    using drop_nth range_split nth_B by simp

  have Mn: "M\<lbrakk>n\<rbrakk> = take ?j0 M @ ?cps"
    using oper_bad_unfold[OF _ hz hp, of n] L by simp
  have listeq: "take ?j0 M @ (?B @ [?lp]) = M"
    using dropM by (metis append_take_drop_id)
  have c1: "M = take ?j0 M @ ((?v0, ?w0) # ?R) @ [?lp]"
    using listeq B_eq by simp

  have cpsrw:
    "?cps =
      concat
        (map
          (\<lambda>k. map (\<lambda>p. (fst p + k * ?d0, snd p))
            ((?v0, ?w0) # ?R))
          [0..<n])"
  proof -
    have "(\<lambda>k. map (?sh k) [?j0..<?j1]) =
        (\<lambda>k. map (\<lambda>p. (fst p + k * ?d0, snd p))
          ((?v0, ?w0) # ?R))"
    proof
      fix k
      have "map (\<lambda>p. (fst p + k * ?d0, snd p))
          ((?v0, ?w0) # ?R) =
        map (\<lambda>p. (fst p + k * ?d0, snd p)) ?B"
        using B_eq by simp
      also have "\<dots> = map (?sh k) [?j0..<?j1]"
        by (simp add: o_def)
      finally show "map (?sh k) [?j0..<?j1] =
        map (\<lambda>p. (fst p + k * ?d0, snd p))
          ((?v0, ?w0) # ?R)" ..
    qed
    then show ?thesis by simp
  qed
  have c2:
    "M\<lbrakk>n\<rbrakk> =
      take ?j0 M @
        concat
          (map
            (\<lambda>k. map (\<lambda>p. (fst p + k * ?d0, snd p))
              ((?v0, ?w0) # ?R))
            [0..<n])"
    using Mn cpsrw by simp

  have len_take: "length (take ?j0 M) = ?j0"
    using j0len by simp
  have disj:
    "(?d0 = 0 \<and> ?i1 = 0) \<or>
      (0 < ?d0 \<and> ?w0 < snd ?lp \<and> fst ?lp = ?v0 + ?d0 \<and>
        nextrel1 M (length (take ?j0 M)) ?j1)"
  proof (cases "?i1 = 0")
    case True
    then show ?thesis by simp
  next
    case False
    with idx1_le1[of M ?j1] have i1: "?i1 = 1" by simp
    have nl1: "nextrel1 M ?j0 ?j1"
      using np i1 by (simp add: nextR_def)
    have v0lt: "?v0 < entry M 0 ?j1"
      by (rule iv[OF j0lt order_refl])
    have d0val: "?d0 = entry M 0 ?j1 - ?v0"
      using i1 by simp
    have d0pos: "0 < ?d0" using d0val v0lt by simp
    have fstv: "fst ?lp = ?v0 + ?d0"
      using lp0 d0val v0lt by simp
    have w0lt: "?w0 < snd ?lp"
      using nl1 lp1 by (simp add: nextrel1_def)
    show ?thesis
      using d0pos w0lt fstv nl1 len_take by simp
  qed
  have npG: "nextR M ?i1 (length (take ?j0 M)) ?j1"
    using np len_take by simp
  show ?thesis
    by (rule that[OF c1 c2 R_gt lp_gt disj npG])
qed

lemma translate_oper_bad:
  assumes L: "1 < length M"
    and hz: "\<not> (entry M 0 (length M - 1) = 0 \<and>
      entry M 1 (length M - 1) = 0)"
    and hp: "hasParent M (idx1 M (length M - 1)) (length M - 1)"
    and hn: "1 \<le> n"
  shows "translate (M\<lbrakk>n\<rbrakk>) <o translate M"
proof -
  obtain G v0 w0 R d0 lp where
    M: "M = G @ ((v0, w0) # R) @ [lp]"
    and Mn: "M\<lbrakk>n\<rbrakk> =
      G @ concat
        (map
          (\<lambda>k. map (\<lambda>p. (fst p + k * d0, snd p))
            ((v0, w0) # R))
          [0..<n])"
    and Rgt: "\<forall>x\<in>set R. v0 < fst x"
    and lpgt: "v0 < fst lp"
    and disj:
      "(d0 = 0 \<and> idx1 M (length M - 1) = 0) \<or>
       (0 < d0 \<and> w0 < snd lp \<and> fst lp = v0 + d0 \<and>
        nextrel1 M (length G) (length M - 1))"
    by (rule oper_bad_blocks[OF L hz hp hn])

  have range:
    "[0..<n] = 0 # [1..<n]"
    using hn by (simp add: upt_conv_Cons)
  let ?C =
    "concat
      (map
        (\<lambda>k. map (\<lambda>p. (fst p + k * d0, snd p))
          ((v0, w0) # R))
        [1..<n])"
  have copies:
    "concat
      (map
        (\<lambda>k. map (\<lambda>p. (fst p + k * d0, snd p))
          ((v0, w0) # R))
        [0..<n]) =
      ((v0, w0) # R) @ ?C"
    using range by simp

  have allC_v0: "\<forall>x\<in>set ?C. v0 \<le> fst x"
  proof
    fix x
    assume x: "x \<in> set ?C"
    have "\<exists>ys\<in>
        set
          (map
            (\<lambda>k. map (\<lambda>p. (fst p + k * d0, snd p))
              ((v0, w0) # R))
            [1..<n]).
        x \<in> set ys"
      using x by (auto simp: set_concat)
    then obtain ys where ys:
      "ys \<in>
        set
          (map
            (\<lambda>k. map (\<lambda>p. (fst p + k * d0, snd p))
              ((v0, w0) # R))
            [1..<n])"
      "x \<in> set ys"
      by blast
    from ys(1) obtain k where k: "k \<in> set [1..<n]"
      and yseq:
        "ys = map (\<lambda>p. (fst p + k * d0, snd p)) ((v0, w0) # R)"
      by auto
    have xk:
      "x \<in> set
        (map (\<lambda>p. (fst p + k * d0, snd p)) ((v0, w0) # R))"
      using ys(2) yseq by simp
    from xk obtain p where p: "p \<in> set ((v0, w0) # R)"
      and xeq: "x = (fst p + k * d0, snd p)"
      by auto
    have "v0 \<le> fst p" using p Rgt by auto
    then show "v0 \<le> fst x" using xeq by simp
  qed

  have core:
    "translate (((v0, w0) # R) @ ?C) <o
      translate (((v0, w0) # R) @ [lp])"
  proof (cases "n = 1")
    case True
    then have Cnil: "?C = []" by simp
    have Thd: "?C = [] \<or> \<not> v0 < fst (hd ?C)"
      using Cnil by simp
    show ?thesis by (rule core_i0[OF Rgt lpgt Thd])
  next
    case False
    with hn have n2: "2 \<le> n" by simp
    have split: "[1..<n] = 1 # [Suc 1..<n]"
      using n2 by (simp add: upt_conv_Cons)
    let ?C' =
      "map (\<lambda>p. (fst p + d0, snd p)) R @
        concat
          (map
            (\<lambda>k. map (\<lambda>p. (fst p + k * d0, snd p))
              ((v0, w0) # R))
            [Suc 1..<n])"
    have Ccons: "?C = (v0 + d0, w0) # ?C'"
      using split by simp
    from disj show ?thesis
    proof
      assume exact: "d0 = 0 \<and> idx1 M (length M - 1) = 0"
      then have d0: "d0 = 0" by simp
      have Thd: "?C = [] \<or> \<not> v0 < fst (hd ?C)"
        using Ccons d0 by simp
      show ?thesis by (rule core_i0[OF Rgt lpgt Thd])
    next
      assume ascending:
        "0 < d0 \<and> w0 < snd lp \<and> fst lp = v0 + d0 \<and>
          nextrel1 M (length G) (length M - 1)"
      then have d0pos: "0 < d0"
        and w0lt: "w0 < snd lp"
        and lp0: "fst lp = v0 + d0"
        by auto
      have Cge: "\<forall>x\<in>set ?C'. v0 + d0 \<le> fst x"
      proof
        fix x
        assume x: "x \<in> set ?C'"
        show "v0 + d0 \<le> fst x"
        proof (cases "x \<in> set (map (\<lambda>p. (fst p + d0, snd p)) R)")
          case True
          then obtain p where "p \<in> set R"
            and "x = (fst p + d0, snd p)" by auto
          then have "v0 < fst p" using Rgt by blast
          then show ?thesis using \<open>x = _\<close> by simp
        next
          case False
          with x have
            "x \<in>
              set
                (concat
                  (map
                    (\<lambda>k. map
                      (\<lambda>p. (fst p + k * d0, snd p))
                      ((v0, w0) # R))
                    [Suc 1..<n]))"
            by simp
          then have ex:
            "\<exists>ys\<in>
              set
                (map
                  (\<lambda>k. map
                    (\<lambda>p. (fst p + k * d0, snd p))
                    ((v0, w0) # R))
                  [Suc 1..<n]).
              x \<in> set ys"
            by (auto simp: set_concat)
          then obtain ys where ys:
            "ys \<in>
              set
                (map
                  (\<lambda>k. map
                    (\<lambda>p. (fst p + k * d0, snd p))
                    ((v0, w0) # R))
                  [Suc 1..<n])"
            "x \<in> set ys"
            by blast
          from ys(1) obtain k where
            k: "k \<in> set [Suc 1..<n]"
            and yseq:
              "ys =
                map (\<lambda>p. (fst p + k * d0, snd p))
                  ((v0, w0) # R)"
            by auto
          from ys(2) yseq obtain p where
            p: "p \<in> set ((v0, w0) # R)"
            and xeq: "x = (fst p + k * d0, snd p)"
            by auto
          have vp: "v0 \<le> fst p" using p Rgt by auto
          have k1: "1 \<le> k" using k by simp
          have dk: "d0 \<le> k * d0"
            using mult_le_mono1[OF k1, of d0] by simp
          have "v0 + d0 \<le> fst p + k * d0"
            using add_mono[OF vp dk] .
          then show ?thesis using xeq by simp
        qed
      qed
      have hcore:
        "translate (((v0, w0) # R) @ ((v0 + d0, w0) # ?C')) <o
          translate (((v0, w0) # R) @ [lp])"
        apply (rule core_i1)
        apply (rule Rgt)
        apply (simp only: fst_conv)
        apply (rule Cge)
        using lp0 lpgt w0lt by auto
      show ?thesis using Ccons hcore by simp
    qed
  qed

  have lifted:
    "translate (G @ (v0, w0) # (R @ ?C)) <o
      translate (G @ (v0, w0) # (R @ [lp]))"
  proof (rule translate_ctx_cong)
    show "translate ((v0, w0) # (R @ ?C)) <o
        translate ((v0, w0) # (R @ [lp]))"
      using core by simp
    show "fst (v0, w0) = fst (v0, w0)" by simp
    show "\<forall>x\<in>set (R @ ?C). fst (v0, w0) \<le> fst x"
      using Rgt allC_v0 by auto
    show "\<forall>x\<in>set (R @ [lp]). fst (v0, w0) \<le> fst x"
      using Rgt lpgt by auto
  qed
  show ?thesis using Mn M copies lifted by simp
qed

lemma m_step_decreases:
  assumes "1 < length M" "1 \<le> n"
  shows "translate (M\<lbrakk>n\<rbrakk>) <o translate M"
proof (cases "entry M 0 (length M - 1) = 0 \<and>
    entry M 1 (length M - 1) = 0")
  case True
  then show ?thesis using assms translate_oper_pred by blast
next
  case hz: False
  show ?thesis
  proof (cases "hasParent M (idx1 M (length M - 1)) (length M - 1)")
    case False
    then show ?thesis using assms translate_oper_pred by blast
  next
    case True
    then show ?thesis using assms hz translate_oper_bad by blast
  qed
qed

end
