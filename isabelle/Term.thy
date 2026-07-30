theory Term
  imports Pss "HOL-Library.More_List"
begin

datatype three = Z | P nat three three

fun olt :: "three \<Rightarrow> three \<Rightarrow> bool" (infix "<o" 50) where
  "Z <o Z \<longleftrightarrow> False"
| "Z <o P a b c \<longleftrightarrow> True"
| "P a b c <o Z \<longleftrightarrow> False"
| "P a b c <o P e f g \<longleftrightarrow>
    a < e \<or> (a = e \<and> b <o f) \<or> (a = e \<and> b = f \<and> c <o g)"

definition ole :: "three \<Rightarrow> three \<Rightarrow> bool" (infix "\<le>o" 50) where
  "x \<le>o y \<longleftrightarrow> x <o y \<or> x = y"

lemma olt_Z_Z [simp]: "\<not> Z <o Z"
  by simp

lemma olt_Z_P [simp]: "Z <o P a b c"
  by simp

lemma olt_P_Z [simp]: "\<not> P a b c <o Z"
  by simp

lemma olt_P_P [simp]:
  "P a b c <o P e f g \<longleftrightarrow>
    a < e \<or> (a = e \<and> b <o f) \<or> (a = e \<and> b = f \<and> c <o g)"
  by simp

fun lead :: "three \<Rightarrow> nat" where
  "lead Z = 0"
| "lead (P a b c) = a"

lemma lead_Z [simp]: "lead Z = 0"
  by simp

lemma lead_P [simp]: "lead (P a b c) = a"
  by simp

lemma olt_P_of_lead_lt:
  "t = Z \<or> lead t < w \<Longrightarrow> t <o P w b c"
  by (cases t) auto

lemma olt_irrefl: "\<not> x <o x"
  by (induction x) auto

lemma not_olt_Z [simp]: "\<not> x <o Z"
  by (cases x) auto

lemma olt_trans:
  assumes "x <o y" "y <o z"
  shows "x <o z"
  using assms
proof (induction z arbitrary: x y)
  case Z
  then show ?case using not_olt_Z by blast
next
  case (P c1 c2 c3)
  show ?case
  proof (cases x)
    case Z
    then show ?thesis by (cases y) auto
  next
    case (P a1 a2 a3)
    note xP = this
    from xP \<open>x <o y\<close> obtain e1 e2 e3 where yP: "y = P e1 e2 e3"
      using \<open>x <o y\<close> by (cases y) auto
    from \<open>x <o y\<close> xP yP
    have xy: "a1 < e1 \<or> (a1 = e1 \<and> a2 <o e2) \<or>
        (a1 = e1 \<and> a2 = e2 \<and> a3 <o e3)"
      by simp
    from \<open>y <o P c1 c2 c3\<close> yP
    have yz: "e1 < c1 \<or> (e1 = c1 \<and> e2 <o c2) \<or>
        (e1 = c1 \<and> e2 = c2 \<and> e3 <o c3)"
      by simp
    have "a1 < c1 \<or> (a1 = c1 \<and> a2 <o c2) \<or>
        (a1 = c1 \<and> a2 = c2 \<and> a3 <o c3)"
      using xy yz P.IH(1)[of a2 e2] P.IH(2)[of a3 e3]
      by (elim disjE) auto
    then show ?thesis using xP by simp
  qed
qed

lemma olt_ole_trans:
  "\<lbrakk>x <o y; y \<le>o z\<rbrakk> \<Longrightarrow> x <o z"
  unfolding ole_def using olt_trans by blast

lemma olt_P_b:
  "b1 <o b2 \<Longrightarrow> P a b1 c1 <o P a b2 c2"
  by simp

lemma olt_P_c:
  "c1 <o c2 \<Longrightarrow> P a b c1 <o P a b c2"
  by simp

function translate :: "pairseq \<Rightarrow> three" where
  "translate [] = Z"
| "translate (p # rest) =
    P (snd p)
      (translate (takeWhile (\<lambda>q. fst p < fst q) rest))
      (translate (dropWhile (\<lambda>q. fst p < fst q) rest))"
  by pat_completeness auto
termination
  by (relation "measure length")
    (auto simp: le_imp_less_Suc length_takeWhile_le
      intro: le_less_trans[OF length_dropWhile_le])

lemma lead_translate:
  "lead (translate M) = (case M of [] \<Rightarrow> 0 | p # _ \<Rightarrow> snd p)"
  by (cases M) auto

lemma takeWhile_append_all:
  "(\<And>x. x \<in> set xs \<Longrightarrow> p x) \<Longrightarrow>
    takeWhile p (xs @ ys) = xs @ takeWhile p ys"
  by (rule takeWhile_append2)

lemma dropWhile_append_all:
  "(\<And>x. x \<in> set xs \<Longrightarrow> p x) \<Longrightarrow>
    dropWhile p (xs @ ys) = dropWhile p ys"
  by (rule dropWhile_append2)

lemma takeWhile_append_not:
  "\<lbrakk>x \<in> set xs; \<not> p x\<rbrakk> \<Longrightarrow>
    takeWhile p (xs @ ys) = takeWhile p xs"
  by (rule takeWhile_append1)

lemma dropWhile_append_not:
  "\<lbrakk>x \<in> set xs; \<not> p x\<rbrakk> \<Longrightarrow>
    dropWhile p (xs @ ys) = dropWhile p xs @ ys"
  by (rule dropWhile_append1)

lemma drop_eq_map_getD:
  "drop a xs =
    map (nth_default d xs) [a..<a + (length xs - a)]"
proof (rule nth_equalityI)
  show "length (drop a xs) =
      length (map (nth_default d xs) [a..<a + (length xs - a)])"
    by simp
next
  fix i
  assume i: "i < length (drop a xs)"
  then have ai: "a + i < length xs" by simp
  show "drop a xs ! i =
      map (nth_default d xs) [a..<a + (length xs - a)] ! i"
    using i ai by (simp add: nth_drop nth_default_nth)
qed

lemma nextrel0_entry0_less:
  "nextrel0 M j0 j1 \<Longrightarrow> entry M 0 j0 < entry M 0 j1"
  by (simp add: nextrel0_def)

lemma le0_entry0_mono:
  assumes "le0 M j0 j1"
  shows "entry M 0 j0 \<le> entry M 0 j1"
proof -
  from assms have "(nextrel0 M)\<^sup>*\<^sup>* j0 j1"
    by (simp add: le0_def)
  then show ?thesis
  proof (induction rule: rtranclp_induct)
    case base
    then show ?case by simp
  next
    case (step y z)
    from step.hyps(2) have "entry M 0 y < entry M 0 z"
      by (rule nextrel0_entry0_less)
    with step.IH show ?case by simp
  qed
qed

lemma nextrel0_index_less:
  "nextrel0 M a b \<Longrightarrow> a < b"
  by (simp add: nextrel0_def)

lemma nextrel0_rtrancl_index_le:
  "(nextrel0 M)\<^sup>*\<^sup>* a b \<Longrightarrow> a \<le> b"
  by (induction rule: rtranclp_induct) (auto dest: nextrel0_index_less)

lemma le0_interval_gt:
  assumes "(nextrel0 M)\<^sup>*\<^sup>* j0 j1"
  shows "\<forall>k. j0 < k \<and> k \<le> j1 \<longrightarrow> entry M 0 j0 < entry M 0 k"
  using assms
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by simp
next
  case (step y z)
  have yz: "entry M 0 y < entry M 0 z"
    using step.hyps(2) by (simp add: nextrel0_def)
  have j0y: "j0 \<le> y"
    using step.hyps(1) by (rule nextrel0_rtrancl_index_le)
  have j0le: "entry M 0 j0 \<le> entry M 0 y"
  proof (cases "j0 < y")
    case True
    then show ?thesis using step.IH by auto
  next
    case False
    with j0y have "j0 = y" by simp
    then show ?thesis by simp
  qed
  show ?case
  proof (intro allI impI, elim conjE)
    fix k
    assume k1: "j0 < k" and k2: "k \<le> z"
    show "entry M 0 j0 < entry M 0 k"
    proof (cases "k \<le> y")
      case True
      then show ?thesis using k1 step.IH by blast
    next
      case False
      then have yk: "y < k" by simp
      show ?thesis
      proof (cases "k = z")
        case True
        then show ?thesis using j0le yz by simp
      next
        case False
        with k2 yk have "y < k \<and> k < z" by simp
        then have "entry M 0 z \<le> entry M 0 k"
          using step.hyps(2) by (simp add: nextrel0_def)
        then show ?thesis using j0le yz by simp
      qed
    qed
  qed
qed

lemma translate_single_tree:
  assumes "\<forall>x\<in>set R. fst p < fst x"
  shows "translate (p # R) = P (snd p) (translate R) Z"
proof -
  have tw: "takeWhile (\<lambda>q. fst p < fst q) R = R"
    using assms by (simp add: takeWhile_eq_all_conv)
  have dw: "dropWhile (\<lambda>q. fst p < fst q) R = []"
    using assms by (simp add: dropWhile_eq_Nil_conv)
  show ?thesis
    by (simp only: translate.simps(2) tw dw translate.simps(1))
qed

lemma translate_block_append:
  assumes R: "\<forall>x\<in>set R. v0 < fst x"
    and T: "T = [] \<or> \<not> v0 < fst (hd T)"
  shows "translate (((v0, w0) # R) @ T) =
    P w0 (translate R) (translate T)"
proof -
  let ?Q = "\<lambda>q. v0 < fst q"
  have twT: "takeWhile ?Q (R @ T) = R"
  proof (cases T)
    case Nil
    then show ?thesis using R by (simp add: takeWhile_eq_all_conv)
  next
    case (Cons t ts)
    with T have "\<not> ?Q t" by simp
    then show ?thesis using R Cons by (simp add: takeWhile_append2)
  qed
  have dwT: "dropWhile ?Q (R @ T) = T"
  proof (cases T)
    case Nil
    then show ?thesis using R by (simp add: dropWhile_eq_Nil_conv)
  next
    case (Cons t ts)
    with T have "\<not> ?Q t" by simp
    then show ?thesis using R Cons by (simp add: dropWhile_append2)
  qed
  show ?thesis
    by (simp only: append_Cons fst_conv snd_conv translate.simps(2) twT dwT)
qed

lemma translate_shift:
  "translate (map (\<lambda>p. (fst p + d, snd p)) M) = translate M"
proof (induction M rule: translate.induct)
  case 1
  then show ?case by simp
next
  case (2 p rest)
  let ?f = "\<lambda>p. (fst p + d, snd p)"
  let ?Q = "\<lambda>q. fst p < fst q"
  have tw:
    "takeWhile (\<lambda>q. fst (?f p) < fst q) (map ?f rest) =
      map ?f (takeWhile ?Q rest)"
    by (simp add: takeWhile_map o_def)
  have dw:
    "dropWhile (\<lambda>q. fst (?f p) < fst q) (map ?f rest) =
      map ?f (dropWhile ?Q rest)"
    by (simp add: dropWhile_map o_def)
  have "translate (map ?f (p # rest)) =
      P (snd p)
        (translate (map ?f (takeWhile ?Q rest)))
        (translate (map ?f (dropWhile ?Q rest)))"
    using tw dw
    by (simp only: list.map translate.simps(2) fst_conv snd_conv)
  also have "\<dots> =
      P (snd p) (translate (takeWhile ?Q rest))
        (translate (dropWhile ?Q rest))"
    using "2.IH"(1) "2.IH"(2) by simp
  also have "\<dots> = translate (p # rest)" by simp
  finally show ?case .
qed

lemma translate_ctx_cong:
  assumes base: "translate (z1 # T1) <o translate (z2 # T2)"
    and root: "fst z1 = fst z2"
    and r1: "\<forall>x\<in>set T1. fst z1 \<le> fst x"
    and r2: "\<forall>x\<in>set T2. fst z2 \<le> fst x"
  shows "translate (G @ z1 # T1) <o translate (G @ z2 # T2)"
proof (induction G rule: length_induct)
  case (1 G)
  show ?case
  proof (cases G)
    case Nil
    then show ?thesis using base by simp
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
        have "translate (G' @ z1 # T1) <o translate (G' @ z2 # T2)"
          using "1.IH" Cons by simp
        then show ?thesis using e1 e2 by (simp add: olt_P_b)
      next
        case False
        then have False2: "\<not> ?Qg z2" using root by simp
        have tw1: "takeWhile ?Qg (G' @ z1 # T1) = G'"
          using allG False by (simp add: takeWhile_append2)
        have dw1: "dropWhile ?Qg (G' @ z1 # T1) = z1 # T1"
          using allG False by (simp add: dropWhile_append2)
        have tw2: "takeWhile ?Qg (G' @ z2 # T2) = G'"
          using allG False2 by (simp add: takeWhile_append2)
        have dw2: "dropWhile ?Qg (G' @ z2 # T2) = z2 # T2"
          using allG False2 by (simp add: dropWhile_append2)
        have e1: "translate (G @ z1 # T1) =
            P (snd g) (translate G') (translate (z1 # T1))"
          using Cons by (simp only: append_Cons translate.simps(2) tw1 dw1)
        have e2: "translate (G @ z2 # T2) =
            P (snd g) (translate G') (translate (z2 # T2))"
          using Cons by (simp only: append_Cons translate.simps(2) tw2 dw2)
        show ?thesis using e1 e2 base by (simp add: olt_P_c)
      qed
    next
      case False
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
      have e1: "translate (G @ z1 # T1) =
          P (snd g) (translate (takeWhile ?Qg G'))
            (translate (dropWhile ?Qg G' @ z1 # T1))"
        using Cons by (simp only: append_Cons translate.simps(2) tw1 dw1)
      have e2: "translate (G @ z2 # T2) =
          P (snd g) (translate (takeWhile ?Qg G'))
            (translate (dropWhile ?Qg G' @ z2 # T2))"
        using Cons by (simp only: append_Cons translate.simps(2) tw2 dw2)
      have "length (dropWhile ?Qg G') < length G"
        using Cons by (simp add: le_imp_less_Suc length_dropWhile_le)
      then have "translate (dropWhile ?Qg G' @ z1 # T1) <o
          translate (dropWhile ?Qg G' @ z2 # T2)"
        using "1.IH" by blast
      then show ?thesis using e1 e2 by (simp add: olt_P_c)
    qed
  qed
qed

definition sndSet :: "pairseq \<Rightarrow> nat set" where
  "sndSet M = snd ` set M"

lemma mem_sndSet [simp]:
  "y \<in> sndSet M \<longleftrightarrow> (\<exists>p\<in>set M. snd p = y)"
  by (auto simp: sndSet_def)

lemma sndSet_nil [simp]:
  "sndSet ([] :: pairseq) = {}"
  by (simp add: sndSet_def)

lemma idx1_le1:
  "idx1 M j \<le> 1"
  by (simp add: idx1_def)

end
