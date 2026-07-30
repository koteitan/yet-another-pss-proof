theory Column
  imports Seqlex
begin

lemma stps_len_pos:
  assumes "ST_PS M"
  shows "0 < length M"
  using assms
proof (induction rule: ST_PS.induct)
  case (diag v)
  show ?case using diagSeq_cons[of 0 v] by simp
next
  case (oper N n)
  show ?case
  proof (cases "1 < length N")
    case True
    obtain R where
      eq: "N\<lbrakk>n\<rbrakk> = butlast N @ R"
      by (meson oper_eq_dropLast_append[
        OF True oper.hyps(2)])
    have "0 < length (butlast N)"
      using True by simp
    then show ?thesis using eq by simp
  next
    case False
    have eq: "N\<lbrakk>n\<rbrakk> = N"
      by (rule oper_eq_self_short) (use False in simp)
    show ?thesis using oper.IH eq by simp
  qed
qed

lemma stps_head:
  assumes "ST_PS M"
  shows "hd M = (0, 0)"
  using assms
proof (induction rule: ST_PS.induct)
  case (diag v)
  show ?case using diagSeq_cons[of 0 v] by simp
next
  case (oper N n)
  show ?case
  proof (cases "1 < length N")
    case True
    obtain R where
      eq: "N\<lbrakk>n\<rbrakk> = butlast N @ R"
      by (meson oper_eq_dropLast_append[
        OF True oper.hyps(2)])
    have "\<exists>a b u. N = a # b # u"
    proof (cases N)
      case Nil
      then show ?thesis using True by simp
    next
      case Nc: (Cons a xs)
      then show ?thesis
      proof (cases xs)
        case Nil
        then show ?thesis using True Nc by simp
      next
        case Xc: (Cons b u)
        then show ?thesis using Nc by blast
      qed
    qed
    then obtain a b u where N: "N = a # b # u"
      by blast
    show ?thesis using eq N oper.IH by simp
  next
    case False
    have eq: "N\<lbrakk>n\<rbrakk> = N"
      by (rule oper_eq_self_short) (use False in simp)
    show ?thesis using oper.IH eq by simp
  qed
qed

lemma getD_app_right:
  assumes h: "length A \<le> i"
  shows "nth_default (0, 0) (A @ T) i =
    nth_default (0, 0) T (i - length A)"
proof (cases "i < length (A @ T)")
  case True
  have it: "i - length A < length T"
    using True h by simp
  show ?thesis
    using True it h
    by (simp add: nth_default_nth nth_append)
next
  case False
  have it: "\<not> i - length A < length T"
    using False h by simp
  show ?thesis
    using False it
    by (simp add: nth_default_def)
qed

lemma entry_append_right:
  "entry (A @ T) i (length A + j) = entry T i j"
proof -
  have get:
    "nth_default (0, 0) (A @ T) (length A + j) =
      nth_default (0, 0) T j"
    using getD_app_right[of A "length A + j" T]
    by simp
  show ?thesis
  proof (cases "j < length T")
    case True
    have at: "length A + j < length (A @ T)"
      using True by simp
    show ?thesis
      using True at get
      by (simp add: entry_def nth_default_nth)
  next
    case False
    have at: "\<not> length A + j < length (A @ T)"
      using False by simp
    show ?thesis
      using False at by (simp add: entry_def)
  qed
qed

lemma nextrel0_append_right:
  "nextrel0 (A @ T) (length A + j0) (length A + j1)
    \<longleftrightarrow> nextrel0 T j0 j1"
  unfolding nextrel0_def
proof
  assume h:
    "length A + j0 < length (A @ T) \<and>
     length A + j1 < length (A @ T) \<and>
     length A + j0 < length A + j1 \<and>
     entry (A @ T) 0 (length A + j0) <
       entry (A @ T) 0 (length A + j1) \<and>
     (\<forall>j. length A + j0 < j \<and>
        j < length A + j1 \<longrightarrow>
        entry (A @ T) 0 (length A + j1) \<le>
          entry (A @ T) 0 j)"
  from h show "j0 < length T \<and> j1 < length T \<and>
      j0 < j1 \<and> entry T 0 j0 < entry T 0 j1 \<and>
      (\<forall>j. j0 < j \<and> j < j1 \<longrightarrow>
        entry T 0 j1 \<le> entry T 0 j)"
  proof (intro conjI allI impI)
    show "j0 < length T" using h by simp
    show "j1 < length T" using h by simp
    show "j0 < j1" using h by simp
    show "entry T 0 j0 < entry T 0 j1"
      using h by (simp add: entry_append_right)
    fix j
    assume jj: "j0 < j \<and> j < j1"
    have valley:
      "\<forall>x. length A + j0 < x \<and>
        x < length A + j1 \<longrightarrow>
        entry (A @ T) 0 (length A + j1) \<le>
          entry (A @ T) 0 x"
      using h by auto
    have shifted:
      "length A + j0 < length A + j \<and>
       length A + j < length A + j1"
      using jj by simp
    have "entry (A @ T) 0 (length A + j1) \<le>
        entry (A @ T) 0 (length A + j)"
      by (rule valley[rule_format, OF shifted])
    then show "entry T 0 j1 \<le> entry T 0 j"
      by (simp add: entry_append_right)
  qed
next
  assume h:
    "j0 < length T \<and> j1 < length T \<and>
     j0 < j1 \<and> entry T 0 j0 < entry T 0 j1 \<and>
     (\<forall>j. j0 < j \<and> j < j1 \<longrightarrow>
        entry T 0 j1 \<le> entry T 0 j)"
  show "length A + j0 < length (A @ T) \<and>
      length A + j1 < length (A @ T) \<and>
      length A + j0 < length A + j1 \<and>
      entry (A @ T) 0 (length A + j0) <
        entry (A @ T) 0 (length A + j1) \<and>
      (\<forall>j. length A + j0 < j \<and>
        j < length A + j1 \<longrightarrow>
        entry (A @ T) 0 (length A + j1) \<le>
          entry (A @ T) 0 j)"
  proof (intro conjI allI impI)
    show "length A + j0 < length (A @ T)"
      using h by simp
    show "length A + j1 < length (A @ T)"
      using h by simp
    show "length A + j0 < length A + j1"
      using h by simp
    show "entry (A @ T) 0 (length A + j0) <
        entry (A @ T) 0 (length A + j1)"
      using h by (simp add: entry_append_right)
    fix j
    assume jj:
      "length A + j0 < j \<and> j < length A + j1"
    let ?j' = "j - length A"
    have j: "j = length A + ?j'"
      using jj by presburger
    have jj': "j0 < ?j' \<and> ?j' < j1"
      using jj j by presburger
    have valley:
      "\<forall>x. j0 < x \<and> x < j1 \<longrightarrow>
        entry T 0 j1 \<le> entry T 0 x"
      using h by auto
    have "entry T 0 j1 \<le> entry T 0 ?j'"
      by (rule valley[rule_format, OF jj'])
    moreover have
      "entry (A @ T) 0 (length A + j1) =
        entry T 0 j1"
      by (rule entry_append_right)
    moreover have
      "entry (A @ T) 0 j = entry T 0 ?j'"
      using j entry_append_right[of A T 0 ?j']
      by simp
    ultimately show "entry (A @ T) 0 (length A + j1)
        \<le> entry (A @ T) 0 j"
      by simp
  qed
qed

lemma rtg_nextrel0_lift:
  assumes "(nextrel0 T)\<^sup>*\<^sup>* j0 c"
  shows "(nextrel0 (A @ T))\<^sup>*\<^sup>*
    (length A + j0) (length A + c)"
  using assms
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by simp
next
  case (step y z)
  have edge: "nextrel0 (A @ T)
      (length A + y) (length A + z)"
    using step.hyps(2)
    by (simp add: nextrel0_append_right)
  show ?case
    by (rule rtranclp.rtrancl_into_rtrancl[
      OF step.IH edge])
qed

lemma le0_append_right_of:
  assumes "le0 T j0 j1"
  shows "le0 (A @ T) (length A + j0) (length A + j1)"
  using assms unfolding le0_def
  by (auto intro: rtg_nextrel0_lift)

lemma nextrel0_lt:
  "nextrel0 M a b \<Longrightarrow> a < b"
  by (simp add: nextrel0_def)

lemma rtg_nextrel0_unlift:
  assumes "(nextrel0 (A @ T))\<^sup>*\<^sup>* (length A + a) c"
  shows "\<exists>c'. c = length A + c' \<and>
    (nextrel0 T)\<^sup>*\<^sup>* a c'"
  using assms
proof (induction rule: rtranclp_induct)
  case base
  show ?case by simp
next
  case (step d e)
  from step.IH obtain d' where
    d: "d = length A + d'"
    and rt: "(nextrel0 T)\<^sup>*\<^sup>* a d'"
    by blast
  have ge: "length A \<le> e"
    using nextrel0_lt[OF step.hyps(2)] d by simp
  let ?e' = "e - length A"
  have e: "e = length A + ?e'"
    using ge by simp
  have relshift:
    "nextrel0 (A @ T)
      (length A + d') (length A + ?e')"
    using step.hyps(2) d e by simp
  have edge: "nextrel0 T d' ?e'"
    using nextrel0_append_right[
      of A T d' ?e'] relshift by blast
  have "(nextrel0 T)\<^sup>*\<^sup>* a ?e'"
    by (rule rtranclp.rtrancl_into_rtrancl[OF rt edge])
  then show ?case using e by blast
qed

lemma le0_append_right:
  "le0 (A @ T) (length A + j0) (length A + j1)
    \<longleftrightarrow> le0 T j0 j1"
proof
  assume h:
    "le0 (A @ T) (length A + j0) (length A + j1)"
  from h obtain b0 b1 rt where
    b0: "length A + j0 < length (A @ T)"
    and b1: "length A + j1 < length (A @ T)"
    and rt:
      "(nextrel0 (A @ T))\<^sup>*\<^sup>*
        (length A + j0) (length A + j1)"
    unfolding le0_def by blast
  obtain c' where
    c: "length A + j1 = length A + c'"
    and rtT: "(nextrel0 T)\<^sup>*\<^sup>* j0 c'"
    using rtg_nextrel0_unlift[OF rt] by blast
  have "j1 = c'" using c by simp
  then show "le0 T j0 j1"
    using b0 b1 rtT unfolding le0_def by simp
next
  assume "le0 T j0 j1"
  then show "le0 (A @ T)
      (length A + j0) (length A + j1)"
    by (rule le0_append_right_of)
qed

lemma nextrel0_no_cross:
  assumes root: "entry T 0 0 = 0"
    and ka: "k < length A"
    and aj: "length A \<le> j"
    and pos: "0 < entry (A @ T) 0 j"
    and rel: "nextrel0 (A @ T) k j"
  shows False
proof -
  from rel have valley:
    "\<forall>x. k < x \<and> x < j \<longrightarrow>
      entry (A @ T) 0 j \<le> entry (A @ T) 0 x"
    unfolding nextrel0_def by blast
  have alen:
    "entry (A @ T) 0 (length A) = 0"
    using entry_append_right[of A T 0 0] root by simp
  have "length A < j"
  proof (rule ccontr)
    assume "\<not> length A < j"
    then have "j = length A" using aj by simp
    then show False using pos alen by simp
  qed
  then have "entry (A @ T) 0 j \<le>
      entry (A @ T) 0 (length A)"
    using valley ka by blast
  then show False using pos alen by simp
qed

lemma nextrel0_no_pred_zero:
  assumes "entry M 0 b = 0"
    and "nextrel0 M a b"
  shows False
  using assms unfolding nextrel0_def by simp

lemma rtg_to_root:
  assumes root: "entry M 0 b = 0"
    and rt: "(nextrel0 M)\<^sup>*\<^sup>* k b"
  shows "k = b"
  using rt
proof (cases rule: rtranclp.cases)
  case rtrancl_refl
  then show ?thesis by simp
next
  case rtrancl_into_rtrancl
  then show ?thesis
    using nextrel0_no_pred_zero[OF root] by blast
qed

lemma le0_no_cross:
  assumes root: "entry T 0 0 = 0"
    and ka: "k < length A"
    and pos:
      "0 < entry (A @ T) 0 (length A + j1)"
    and chain:
      "le0 (A @ T) k (length A + j1)"
  shows False
proof -
  from chain have rt:
    "(nextrel0 (A @ T))\<^sup>*\<^sup>*
      k (length A + j1)"
    unfolding le0_def by blast
  have main:
    "\<And>e. (nextrel0 (A @ T))\<^sup>*\<^sup>* k e \<Longrightarrow>
      length A \<le> e \<Longrightarrow>
      0 < entry (A @ T) 0 e \<Longrightarrow>
      length A \<le> k"
  proof -
    fix e
    assume r: "(nextrel0 (A @ T))\<^sup>*\<^sup>* k e"
    then show "length A \<le> e \<Longrightarrow>
        0 < entry (A @ T) 0 e \<Longrightarrow>
        length A \<le> k"
    proof (induction rule: rtranclp_induct)
      case base
      then show ?case by simp
    next
      case (step c d)
      assume da: "length A \<le> d"
        and dpos: "0 < entry (A @ T) 0 d"
      have ca: "length A \<le> c"
      proof (rule ccontr)
        assume "\<not> length A \<le> c"
        then have "c < length A" by simp
        then show False
          using nextrel0_no_cross[
            OF root _ da dpos step.hyps(2)]
          by simp
      qed
      show "length A \<le> k"
      proof (cases "0 < entry (A @ T) 0 c")
        case True
        show ?thesis by (rule step.IH[OF ca True])
      next
        case False
        have cz: "entry (A @ T) 0 c = 0"
          using False by simp
        have "k = c"
          by (rule rtg_to_root[OF cz step.hyps(1)])
        then show ?thesis using ca by simp
      qed
    qed
  qed
  have "length A \<le> k"
    by (rule main[OF rt]) (use pos in simp_all)
  then show False using ka by simp
qed

lemma nextrel1_append_right:
  "nextrel1 (A @ T) (length A + j0) (length A + j1)
    \<longleftrightarrow> nextrel1 T j0 j1"
  unfolding nextrel1_def
proof
  assume h:
    "length A + j0 < length (A @ T) \<and>
     length A + j1 < length (A @ T) \<and>
     length A + j0 < length A + j1 \<and>
     entry (A @ T) 1 (length A + j0) <
       entry (A @ T) 1 (length A + j1) \<and>
     le0 (A @ T) (length A + j0) (length A + j1) \<and>
     (\<forall>j. length A + j0 < j \<and>
        le0 (A @ T) j (length A + j1) \<longrightarrow>
        entry (A @ T) 1 (length A + j1) \<le>
          entry (A @ T) 1 j)"
  have bounds: "j0 < length T" "j1 < length T"
    using h by simp_all
  have ij: "j0 < j1" using h by simp
  have val: "entry T 1 j0 < entry T 1 j1"
    using h by (simp add: entry_append_right)
  have l: "le0 T j0 j1"
    using h by (simp add: le0_append_right)
  have valleyM:
    "\<forall>j. length A + j0 < j \<and>
      le0 (A @ T) j (length A + j1) \<longrightarrow>
      entry (A @ T) 1 (length A + j1) \<le>
        entry (A @ T) 1 j"
    using h by auto
  have valley:
    "\<forall>j. j0 < j \<and> le0 T j j1 \<longrightarrow>
      entry T 1 j1 \<le> entry T 1 j"
  proof (intro allI impI)
    fix j
    assume jj: "j0 < j \<and> le0 T j j1"
    have shifted:
      "length A + j0 < length A + j \<and>
       le0 (A @ T) (length A + j)
        (length A + j1)"
      using jj by (simp add: le0_append_right)
    have "entry (A @ T) 1 (length A + j1) \<le>
        entry (A @ T) 1 (length A + j)"
      by (rule valleyM[rule_format, OF shifted])
    then show "entry T 1 j1 \<le> entry T 1 j"
      by (simp add: entry_append_right)
  qed
  show "j0 < length T \<and> j1 < length T \<and>
      j0 < j1 \<and> entry T 1 j0 < entry T 1 j1 \<and>
      le0 T j0 j1 \<and>
      (\<forall>j. j0 < j \<and> le0 T j j1 \<longrightarrow>
        entry T 1 j1 \<le> entry T 1 j)"
    using bounds ij val l valley by blast
next
  assume h:
    "j0 < length T \<and> j1 < length T \<and>
     j0 < j1 \<and> entry T 1 j0 < entry T 1 j1 \<and>
     le0 T j0 j1 \<and>
     (\<forall>j. j0 < j \<and> le0 T j j1 \<longrightarrow>
        entry T 1 j1 \<le> entry T 1 j)"
  have valleyT:
    "\<forall>j. j0 < j \<and> le0 T j j1 \<longrightarrow>
      entry T 1 j1 \<le> entry T 1 j"
    using h by auto
  have valley:
    "\<forall>j. length A + j0 < j \<and>
      le0 (A @ T) j (length A + j1) \<longrightarrow>
      entry (A @ T) 1 (length A + j1) \<le>
        entry (A @ T) 1 j"
  proof (intro allI impI)
    fix j
    assume jj:
      "length A + j0 < j \<and>
       le0 (A @ T) j (length A + j1)"
    have ge: "length A \<le> j" using jj by simp
    let ?j' = "j - length A"
    have jeq: "j = length A + ?j'"
      using ge by simp
    have lt: "j0 < ?j'"
      using jj by (simp add: less_diff_conv add.commute)
    have leshift:
      "le0 (A @ T) (length A + ?j')
        (length A + j1)"
      using jj jeq by simp
    have le: "le0 T ?j' j1"
      using le0_append_right[
        of A T ?j' j1] leshift by blast
    have "entry T 1 j1 \<le> entry T 1 ?j'"
      by (rule valleyT[rule_format]) (use lt le in simp)
    moreover have
      "entry (A @ T) 1 (length A + j1) =
        entry T 1 j1"
      by (rule entry_append_right)
    moreover have "entry (A @ T) 1 j = entry T 1 ?j'"
      using jeq entry_append_right[of A T 1 ?j']
      by simp
    ultimately show "entry (A @ T) 1 (length A + j1)
        \<le> entry (A @ T) 1 j"
      by simp
  qed
  show "length A + j0 < length (A @ T) \<and>
      length A + j1 < length (A @ T) \<and>
      length A + j0 < length A + j1 \<and>
      entry (A @ T) 1 (length A + j0) <
        entry (A @ T) 1 (length A + j1) \<and>
      le0 (A @ T) (length A + j0) (length A + j1) \<and>
      (\<forall>j. length A + j0 < j \<and>
        le0 (A @ T) j (length A + j1) \<longrightarrow>
        entry (A @ T) 1 (length A + j1) \<le>
          entry (A @ T) 1 j)"
    using h valley
    by (simp add: entry_append_right le0_append_right)
qed

lemma nextR_append_right:
  "nextR (A @ T) i (length A + j0) (length A + j1)
    \<longleftrightarrow> nextR T i j0 j1"
  unfolding nextR_def
  by (cases "i = 0")
    (simp_all add: nextrel0_append_right
      nextrel1_append_right)

lemma idx1_append_right:
  "idx1 (A @ T) (length A + j) = idx1 T j"
  by (simp add: idx1_def entry_append_right)

lemma nextR_le0:
  assumes "nextR M i k b"
  shows "le0 M k b"
proof (cases "i = 0")
  case True
  from assms have rel: "nextrel0 M k b"
    using True by (simp add: nextR_def)
  have kl: "k < length M" and bl: "b < length M"
    using rel unfolding nextrel0_def by blast+
  have rt: "(nextrel0 M)\<^sup>*\<^sup>* k b"
  proof (rule r_into_rtranclp)
    show "nextrel0 M k b" using rel .
  qed
  show ?thesis
    unfolding le0_def using kl bl rt by blast
next
  case False
  then show ?thesis
    using assms by (simp add: nextR_def nextrel1_def)
qed

lemma nextR_src_in_T:
  assumes root: "entry T 0 0 = 0"
    and pos:
      "0 < entry (A @ T) 0 (length A + j1)"
    and rel:
      "nextR (A @ T) i k (length A + j1)"
  shows "length A \<le> k"
proof (rule ccontr)
  assume "\<not> length A \<le> k"
  then have "k < length A" by simp
  then show False
    by (rule le0_no_cross[
      OF root _ pos nextR_le0[OF rel]])
qed

lemma hasParent_append_right:
  assumes root: "entry T 0 0 = 0"
    and pos:
      "0 < entry (A @ T) 0 (length A + j1)"
  shows
    "hasParent (A @ T) i (length A + j1)
      \<longleftrightarrow> hasParent T i j1"
  unfolding hasParent_def
proof
  assume "\<exists>!j0. nextR (A @ T) i j0
      (length A + j1)"
  then obtain j0 where
    rel: "nextR (A @ T) i j0 (length A + j1)"
    and uniq:
      "\<forall>y. nextR (A @ T) i y
        (length A + j1) \<longrightarrow> y = j0"
    by blast
  have ge: "length A \<le> j0"
    by (rule nextR_src_in_T[OF root pos rel])
  let ?j0 = "j0 - length A"
  have jeq: "j0 = length A + ?j0"
    using ge by simp
  have relshift:
    "nextR (A @ T) i
      (length A + ?j0) (length A + j1)"
    using rel jeq by simp
  have relT: "nextR T i ?j0 j1"
    using nextR_append_right[
      of A T i ?j0 j1] relshift by blast
  have uniqueT:
    "\<forall>y. nextR T i y j1 \<longrightarrow> y = ?j0"
  proof (intro allI impI)
    fix y
    assume y: "nextR T i y j1"
    have shifted:
      "nextR (A @ T) i (length A + y)
        (length A + j1)"
      using y by (simp add: nextR_append_right)
    have "length A + y = j0"
      by (rule uniq[rule_format, OF shifted])
    then show "y = ?j0" using jeq by simp
  qed
  show "\<exists>!j0. nextR T i j0 j1"
    using relT uniqueT by blast
next
  assume "\<exists>!j0. nextR T i j0 j1"
  then obtain j0 where
    relT: "nextR T i j0 j1"
    and uniqT:
      "\<forall>y. nextR T i y j1 \<longrightarrow> y = j0"
    by blast
  have rel:
    "nextR (A @ T) i (length A + j0)
      (length A + j1)"
    using relT by (simp add: nextR_append_right)
  have unique:
    "\<forall>y. nextR (A @ T) i y
      (length A + j1) \<longrightarrow>
      y = length A + j0"
  proof (intro allI impI)
    fix y
    assume yrel:
      "nextR (A @ T) i y (length A + j1)"
    have ge: "length A \<le> y"
      by (rule nextR_src_in_T[OF root pos yrel])
    let ?y = "y - length A"
    have yeq: "y = length A + ?y" using ge by simp
    have yshift:
      "nextR (A @ T) i (length A + ?y)
        (length A + j1)"
      using yrel yeq by simp
    have "nextR T i ?y j1"
      using nextR_append_right[
        of A T i ?y j1] yshift by blast
    then have "?y = j0"
      by (rule uniqT[rule_format])
    then show "y = length A + j0" using yeq by simp
  qed
  show "\<exists>!j0. nextR (A @ T) i j0
      (length A + j1)"
    using rel unique by blast
qed

lemma parent_append_right:
  assumes root: "entry T 0 0 = 0"
    and pos:
      "0 < entry (A @ T) 0 (length A + j1)"
    and hpT: "hasParent T i j1"
  shows "parent (A @ T) i (length A + j1) =
    length A + parent T i j1"
proof -
  have hpM: "hasParent (A @ T) i (length A + j1)"
    using hasParent_append_right[OF root pos] hpT
    by blast
  have pM:
    "nextR (A @ T) i
      (parent (A @ T) i (length A + j1))
      (length A + j1)"
    by (rule parent_nextR[OF hpM])
  have pT: "nextR T i (parent T i j1) j1"
    by (rule parent_nextR[OF hpT])
  have pTs:
    "nextR (A @ T) i
      (length A + parent T i j1)
      (length A + j1)"
    using pT by (simp add: nextR_append_right)
  from hpM obtain x where
    x: "nextR (A @ T) i x (length A + j1)"
    and uniq:
      "\<forall>y. nextR (A @ T) i y
        (length A + j1) \<longrightarrow> y = x"
    unfolding hasParent_def by blast
  have "parent (A @ T) i (length A + j1) = x"
    by (rule uniq[rule_format, OF pM])
  moreover have "length A + parent T i j1 = x"
    by (rule uniq[rule_format, OF pTs])
  ultimately show ?thesis by simp
qed

lemma take_append_right:
  "take (length A + j) (A @ T) = A @ take j T"
  by (simp add: take_append)

lemma copyblock_append:
  "map
      (\<lambda>j.
        (entry (A @ T) 0 j + k * d0,
         entry (A @ T) 1 j + k * d1))
      [length A + a..<length A + a + m] =
    map
      (\<lambda>j.
        (entry T 0 j + k * d0,
         entry T 1 j + k * d1))
      [a..<a + m]"
proof (rule nth_equalityI)
  show "length
      (map
        (\<lambda>j.
          (entry (A @ T) 0 j + k * d0,
           entry (A @ T) 1 j + k * d1))
        [length A + a..<length A + a + m]) =
    length
      (map
        (\<lambda>j.
          (entry T 0 j + k * d0,
           entry T 1 j + k * d1))
        [a..<a + m])"
    by simp
next
  fix i
  assume ilt:
    "i < length
      (map
        (\<lambda>j.
          (entry (A @ T) 0 j + k * d0,
           entry (A @ T) 1 j + k * d1))
        [length A + a..<length A + a + m])"
  have im: "i < m" using ilt by simp
  show "map
        (\<lambda>j.
          (entry (A @ T) 0 j + k * d0,
           entry (A @ T) 1 j + k * d1))
        [length A + a..<length A + a + m] ! i =
      map
        (\<lambda>j.
          (entry T 0 j + k * d0,
           entry T 1 j + k * d1))
        [a..<a + m] ! i"
    using im
    by (simp add: add.assoc entry_append_right)
qed

lemma Pred_append_right:
  assumes "2 \<le> length T"
  shows "Pred (A @ T) = A @ Pred T"
proof -
  have ne: "T \<noteq> []" using assms by auto
  show ?thesis
    using assms ne
    by (simp add: Pred_def butlast_append)
qed

lemma no_hasParent_of_row0_zero:
  assumes root: "entry M 0 j1 = 0"
    and hp: "hasParent M i j1"
  shows False
proof -
  from hp obtain j0 where
    rel: "nextR M i j0 j1"
    unfolding hasParent_def by blast
  have l: "le0 M j0 j1" by (rule nextR_le0[OF rel])
  from l have rt: "(nextrel0 M)\<^sup>*\<^sup>* j0 j1"
    unfolding le0_def by blast
  have "j0 = j1" by (rule rtg_to_root[OF root rt])
  moreover have "j0 < j1"
    by (rule nextR_index_lt[OF rel])
  ultimately show False by simp
qed

lemma oper_append_right:
  assumes hT: "2 \<le> length T"
    and root: "entry T 0 0 = 0"
  shows "(A @ T)\<lbrakk>n\<rbrakk> = A @ T\<lbrakk>n\<rbrakk>"
proof -
  let ?j1 = "length T - 1"
  have shortT: "length T - 1 \<noteq> 0"
    using hT by simp
  have shortAT: "length (A @ T) - 1 \<noteq> 0"
    using hT by simp
  have lenlast:
    "length (A @ T) - 1 = length A + ?j1"
    using hT by simp
  have e0:
    "entry (A @ T) 0 (length A + ?j1) =
      entry T 0 ?j1"
    by (rule entry_append_right)
  have e1:
    "entry (A @ T) 1 (length A + ?j1) =
      entry T 1 ?j1"
    by (rule entry_append_right)
  show ?thesis
  proof (cases
      "entry T 0 ?j1 = 0 \<and> entry T 1 ?j1 = 0")
    case zero: True
    have zeroAT:
      "entry (A @ T) 0 (length (A @ T) - 1) = 0 \<and>
       entry (A @ T) 1 (length (A @ T) - 1) = 0"
      using zero e0 e1 lenlast by simp
    have eqAT: "(A @ T)\<lbrakk>n\<rbrakk> = Pred (A @ T)"
      by (rule oper_eq_pred_of_zero[OF shortAT zeroAT])
    have eqT: "T\<lbrakk>n\<rbrakk> = Pred T"
      by (rule oper_eq_pred_of_zero[OF shortT zero])
    show ?thesis
      using eqAT eqT Pred_append_right[OF hT] by simp
  next
    case nz: False
    have nzAT:
      "\<not> (entry (A @ T) 0 (length (A @ T) - 1) = 0 \<and>
        entry (A @ T) 1 (length (A @ T) - 1) = 0)"
      using nz e0 e1 lenlast by simp
    let ?i = "idx1 T ?j1"
    have idx:
      "idx1 (A @ T) (length (A @ T) - 1) = ?i"
      using idx1_append_right[of A T ?j1] lenlast
      by simp
    show ?thesis
    proof (cases "hasParent T ?i ?j1")
      case hp: True
      have posT: "0 < entry T 0 ?j1"
      proof (rule ccontr)
        assume "\<not> 0 < entry T 0 ?j1"
        then have "entry T 0 ?j1 = 0" by simp
        then show False
          by (rule no_hasParent_of_row0_zero[OF _ hp])
      qed
      have posAT:
        "0 < entry (A @ T) 0 (length A + ?j1)"
        using posT e0 by simp
      have hpAT0:
        "hasParent (A @ T) ?i (length A + ?j1)"
        using hasParent_append_right[OF root posAT] hp
        by blast
      have hpAT:
        "hasParent (A @ T)
          (idx1 (A @ T) (length (A @ T) - 1))
          (length (A @ T) - 1)"
        using hpAT0 idx lenlast by simp
      let ?j0 = "parent T ?i ?j1"
      have par:
        "parent (A @ T) ?i (length A + ?j1) =
          length A + ?j0"
        by (rule parent_append_right[OF root posAT hp])
      have par':
        "parent (A @ T)
          (idx1 (A @ T) (length (A @ T) - 1))
          (length (A @ T) - 1) =
          length A + ?j0"
        using par idx lenlast by simp
      have relT: "nextR T ?i ?j0 ?j1"
        by (rule parent_nextR[OF hp])
      have j0lt: "?j0 < ?j1"
        by (rule nextR_index_lt[OF relT])
      let ?d =
        "if 0 < ?i
         then entry T 0 ?j1 - entry T 0 ?j0
         else 0"
      have dAT:
        "(if 0 <
            idx1 (A @ T) (length (A @ T) - 1)
          then
            entry (A @ T) 0 (length (A @ T) - 1) -
              entry (A @ T) 0
                (parent (A @ T)
                  (idx1 (A @ T)
                    (length (A @ T) - 1))
                  (length (A @ T) - 1))
          else 0) = ?d"
        using idx lenlast par'
          entry_append_right[of A T 0 ?j0] e0
        by simp
      have eqAT:
        "(A @ T)\<lbrakk>n\<rbrakk> =
          take (length A + ?j0) (A @ T) @
          concat
            (map
              (\<lambda>k.
                map
                  (\<lambda>j.
                    (entry (A @ T) 0 j + k * ?d,
                     entry (A @ T) 1 j))
                  [length A + ?j0..<length A + ?j1])
              [0..<n])"
      proof -
        note raw = oper_bad_unfold[
          OF shortAT nzAT hpAT, of n]
        show ?thesis
          using raw lenlast par' dAT by simp
      qed
      have eqT:
        "T\<lbrakk>n\<rbrakk> =
          take ?j0 T @
          concat
            (map
              (\<lambda>k.
                map
                  (\<lambda>j.
                    (entry T 0 j + k * ?d,
                     entry T 1 j))
                  [?j0..<?j1])
              [0..<n])"
      proof -
        note raw = oper_bad_unfold[
          OF shortT nz hp, of n]
        show ?thesis using raw by simp
      qed
      have blocks:
        "\<forall>k.
          map
              (\<lambda>j.
                (entry (A @ T) 0 j + k * ?d,
                 entry (A @ T) 1 j))
              [length A + ?j0..<length A + ?j1] =
            map
              (\<lambda>j.
                (entry T 0 j + k * ?d,
                 entry T 1 j))
              [?j0..<?j1]"
      proof
        fix k
        show "map
              (\<lambda>j.
                (entry (A @ T) 0 j + k * ?d,
                 entry (A @ T) 1 j))
              [length A + ?j0..<length A + ?j1] =
            map
              (\<lambda>j.
                (entry T 0 j + k * ?d,
                 entry T 1 j))
              [?j0..<?j1]"
        proof (rule nth_equalityI)
          show "length
              (map
                (\<lambda>j.
                  (entry (A @ T) 0 j + k * ?d,
                   entry (A @ T) 1 j))
                [length A + ?j0..<length A + ?j1]) =
            length
              (map
                (\<lambda>j.
                  (entry T 0 j + k * ?d,
                   entry T 1 j))
                [?j0..<?j1])"
            using j0lt by simp
        next
          fix q
          assume q:
            "q < length
              (map
                (\<lambda>j.
                  (entry (A @ T) 0 j + k * ?d,
                   entry (A @ T) 1 j))
                [length A + ?j0..<length A + ?j1])"
          show "map
                (\<lambda>j.
                  (entry (A @ T) 0 j + k * ?d,
                   entry (A @ T) 1 j))
                [length A + ?j0..<length A + ?j1] ! q =
              map
                (\<lambda>j.
                  (entry T 0 j + k * ?d,
                   entry T 1 j))
                [?j0..<?j1] ! q"
            using q j0lt
            by (simp add: add.assoc entry_append_right)
        qed
      qed
      have fans:
        "concat
            (map
              (\<lambda>k.
                map
                  (\<lambda>j.
                    (entry (A @ T) 0 j + k * ?d,
                     entry (A @ T) 1 j))
                  [length A + ?j0..<length A + ?j1])
              [0..<n]) =
          concat
            (map
              (\<lambda>k.
                map
                  (\<lambda>j.
                    (entry T 0 j + k * ?d,
                     entry T 1 j))
                  [?j0..<?j1])
              [0..<n])"
        using blocks by (auto intro: map_cong)
      have take:
        "take (length A + ?j0) (A @ T) =
          A @ take ?j0 T"
        by (rule take_append_right)
      show ?thesis
        using eqAT eqT fans take by simp
    next
      case nhp: False
      have nhpAT0:
        "\<not> hasParent (A @ T) ?i (length A + ?j1)"
      proof
        assume hpAT:
          "hasParent (A @ T) ?i (length A + ?j1)"
        show False
        proof (cases
            "0 < entry (A @ T) 0 (length A + ?j1)")
          case True
          have "hasParent T ?i ?j1"
            using hasParent_append_right[
              OF root True] hpAT by blast
          then show False using nhp by simp
        next
          case False
          have "entry (A @ T) 0 (length A + ?j1) = 0"
            using False by simp
          then show False
            by (rule no_hasParent_of_row0_zero[OF _ hpAT])
        qed
      qed
      have nhpAT:
        "\<not> hasParent (A @ T)
          (idx1 (A @ T) (length (A @ T) - 1))
          (length (A @ T) - 1)"
        using nhpAT0 idx lenlast by simp
      have eqAT: "(A @ T)\<lbrakk>n\<rbrakk> = Pred (A @ T)"
        by (rule oper_eq_pred_of_noParent[
          OF shortAT nzAT nhpAT])
      have eqT: "T\<lbrakk>n\<rbrakk> = Pred T"
        by (rule oper_eq_pred_of_noParent[
          OF shortT nz nhp])
      show ?thesis
        using eqAT eqT Pred_append_right[OF hT] by simp
    qed
  qed
qed

lemma map_range_entry_eq_take:
  assumes "j1 \<le> length N"
  shows
    "map (\<lambda>j. (entry N 0 j, entry N 1 j))
      [0..<j1] = take j1 N"
proof (rule nth_equalityI)
  show "length
      (map (\<lambda>j. (entry N 0 j, entry N 1 j))
        [0..<j1]) =
    length (take j1 N)"
    using assms by simp
next
  fix i
  assume ilt:
    "i < length
      (map (\<lambda>j. (entry N 0 j, entry N 1 j))
        [0..<j1])"
  have iN: "i < length N" using ilt assms by simp
  show "map (\<lambda>j. (entry N 0 j, entry N 1 j))
        [0..<j1] ! i =
      take j1 N ! i"
    using ilt iN
    by (simp add: entry_def nth_take prod_eq_iff)
qed

lemma oper_headD:
  assumes L: "1 < length N"
    and n1: "1 \<le> n"
  shows "hd (N\<lbrakk>n\<rbrakk>) = hd N"
proof -
  obtain R where eq:
    "N\<lbrakk>n\<rbrakk> = butlast N @ R"
    by (meson oper_eq_dropLast_append[OF L n1])
  obtain a b u where N: "N = a # b # u"
  proof -
    have "\<exists>a b u. N = a # b # u"
    proof (cases N)
      case Nil
      then show ?thesis using L by simp
    next
      case Nc: (Cons a xs)
      show ?thesis
      proof (cases xs)
        case Nil
        then show ?thesis using L Nc by simp
      next
        case Xc: (Cons b u)
        then show ?thesis using Nc by blast
      qed
    qed
    then show ?thesis using that by blast
  qed
  show ?thesis using eq N by simp
qed

lemma translate_nil [simp]:
  "translate [] = Z"
  by simp

fun maxr1 :: "pairseq \<Rightarrow> nat" where
  "maxr1 [] = 0"
| "maxr1 (c # S) = max (snd c) (maxr1 S)"

lemma maxr1_cons:
  "maxr1 (c # S) = max (snd c) (maxr1 S)"
  by simp

definition r1ok :: "pairseq \<Rightarrow> bool" where
  "r1ok M \<longleftrightarrow>
    (\<forall>j. j < length M \<longrightarrow>
      0 < fst (nth_default (0, 0) M j) \<longrightarrow>
      (\<exists>k. k < j \<and>
        fst (nth_default (0, 0) M k) + 1 =
          fst (nth_default (0, 0) M j) \<and>
        (\<forall>l. k < l \<longrightarrow> l < j \<longrightarrow>
          fst (nth_default (0, 0) M j) \<le>
            fst (nth_default (0, 0) M l)) \<and>
        snd (nth_default (0, 0) M j) \<le>
          snd (nth_default (0, 0) M k) + 1))"

lemma diagSeq0_length:
  "length (diagSeq 0 v) = v + 1"
  by (simp add: diagSeq_def)

lemma diagSeq0_getD:
  assumes "i < v + 1"
  shows "nth_default (0, 0) (diagSeq 0 v) i = (i, i)"
proof -
  have iu: "i < length [0..<Suc v]"
    using assms by simp
  have im:
    "i < length (map (\<lambda>j. (j, j)) [0..<Suc v])"
    using iu by simp
  have "nth_default (0, 0)
      (map (\<lambda>j. (j, j)) [0..<Suc v]) i =
      map (\<lambda>j. (j, j)) [0..<Suc v] ! i"
    by (rule nth_default_nth[OF im])
  also have "\<dots> = ([0..<Suc v] ! i, [0..<Suc v] ! i)"
    by (simp only: nth_map[OF iu])
  also have "\<dots> = (i, i)"
  proof -
    have "[0..<Suc v] ! i = 0 + i"
      by (rule nth_upt) (use iu in simp)
    then show ?thesis by simp
  qed
  finally show ?thesis
    by (simp only: diagSeq_def)
qed

lemma r1ok_diagSeq:
  "r1ok (diagSeq 0 v)"
  unfolding r1ok_def
proof (intro allI impI)
  fix j
  assume jl: "j < length (diagSeq 0 v)"
    and pos:
      "0 < fst (nth_default (0, 0)
        (diagSeq 0 v) j)"
  have jv: "j < v + 1"
    using jl by (simp add: diagSeq0_length)
  have jpos: "0 < j"
    using pos diagSeq0_getD[OF jv] by simp
  let ?k = "j - 1"
  have kv: "?k < v + 1" using jv jpos by simp
  show "\<exists>k. k < j \<and>
      fst (nth_default (0, 0) (diagSeq 0 v) k) + 1 =
        fst (nth_default (0, 0) (diagSeq 0 v) j) \<and>
      (\<forall>l. k < l \<longrightarrow> l < j \<longrightarrow>
        fst (nth_default (0, 0) (diagSeq 0 v) j) \<le>
          fst (nth_default (0, 0) (diagSeq 0 v) l)) \<and>
      snd (nth_default (0, 0) (diagSeq 0 v) j) \<le>
        snd (nth_default (0, 0) (diagSeq 0 v) k) + 1"
  proof (intro exI[of _ ?k] conjI)
    show "?k < j" using jpos by simp
    show "fst (nth_default (0, 0) (diagSeq 0 v) ?k) + 1 =
        fst (nth_default (0, 0) (diagSeq 0 v) j)"
      using diagSeq0_getD[OF kv]
        diagSeq0_getD[OF jv] jpos by simp
    show "\<forall>l. ?k < l \<longrightarrow> l < j \<longrightarrow>
        fst (nth_default (0, 0) (diagSeq 0 v) j) \<le>
          fst (nth_default (0, 0) (diagSeq 0 v) l)"
      using jpos by presburger
    show "snd (nth_default (0, 0) (diagSeq 0 v) j) \<le>
        snd (nth_default (0, 0) (diagSeq 0 v) ?k) + 1"
      using diagSeq0_getD[OF kv]
        diagSeq0_getD[OF jv] jpos by simp
  qed
qed

lemma getD_take:
  assumes "j < m"
  shows "nth_default (0, 0) (take m M) j =
    nth_default (0, 0) M j"
proof (cases "j < length M")
  case True
  have jt: "j < length (take m M)"
    using assms True by simp
  show ?thesis
    using assms True jt
    by (simp add: nth_default_nth nth_take)
next
  case False
  have "\<not> j < length (take m M)"
    using False by simp
  then show ?thesis
    using False by (simp add: nth_default_def)
qed

lemma r1ok_take:
  assumes h: "r1ok M"
  shows "r1ok (take m M)"
  unfolding r1ok_def
proof (intro allI impI)
  fix j
  assume jt: "j < length (take m M)"
    and pos:
      "0 < fst (nth_default (0, 0) (take m M) j)"
  have jm: "j < m" using jt by simp
  have jM: "j < length M" using jt by simp
  have takeeq:
    "nth_default (0, 0) (take m M) j =
      nth_default (0, 0) M j"
    by (rule getD_take[OF jm])
  have posM:
    "0 < fst (nth_default (0, 0) M j)"
    using pos takeeq by simp
  from h jM posM obtain k where
    kj: "k < j"
    and lev:
      "fst (nth_default (0, 0) M k) + 1 =
        fst (nth_default (0, 0) M j)"
    and between:
      "\<forall>l. k < l \<longrightarrow> l < j \<longrightarrow>
        fst (nth_default (0, 0) M j) \<le>
          fst (nth_default (0, 0) M l)"
    and snd:
      "snd (nth_default (0, 0) M j) \<le>
        snd (nth_default (0, 0) M k) + 1"
    unfolding r1ok_def by blast
  have km: "k < m" using kj jm by simp
  show "\<exists>k. k < j \<and>
      fst (nth_default (0, 0) (take m M) k) + 1 =
        fst (nth_default (0, 0) (take m M) j) \<and>
      (\<forall>l. k < l \<longrightarrow> l < j \<longrightarrow>
        fst (nth_default (0, 0) (take m M) j) \<le>
          fst (nth_default (0, 0) (take m M) l)) \<and>
      snd (nth_default (0, 0) (take m M) j) \<le>
        snd (nth_default (0, 0) (take m M) k) + 1"
  proof (intro exI[of _ k] conjI)
    show "k < j" using kj .
    have eqk:
      "nth_default (0, 0) (take m M) k =
        nth_default (0, 0) M k"
      by (rule getD_take[OF km])
    have eqj:
      "nth_default (0, 0) (take m M) j =
        nth_default (0, 0) M j"
      by (rule getD_take[OF jm])
    show "fst (nth_default (0, 0) (take m M) k) + 1 =
        fst (nth_default (0, 0) (take m M) j)"
      using lev eqk eqj by simp
    show "\<forall>l. k < l \<longrightarrow> l < j \<longrightarrow>
        fst (nth_default (0, 0) (take m M) j) \<le>
          fst (nth_default (0, 0) (take m M) l)"
    proof (intro allI impI)
      fix l
      assume kl: "k < l" and lj: "l < j"
      have lm: "l < m" using lj jm by simp
      have eql:
        "nth_default (0, 0) (take m M) l =
          nth_default (0, 0) M l"
        by (rule getD_take[OF lm])
      show "fst (nth_default (0, 0) (take m M) j) \<le>
          fst (nth_default (0, 0) (take m M) l)"
        using between[rule_format, OF kl lj] eqj eql
        by simp
    qed
    show "snd (nth_default (0, 0) (take m M) j) \<le>
        snd (nth_default (0, 0) (take m M) k) + 1"
      using snd eqj eqk by simp
  qed
qed

lemma r1ok_dropLast:
  assumes "r1ok M"
  shows "r1ok (butlast M)"
  using r1ok_take[OF assms, of "length M - 1"]
  by (simp add: butlast_conv_take)

lemma getD_append_left:
  assumes "i < length G"
  shows "nth_default (0, 0) (G @ X) i =
    nth_default (0, 0) G i"
  using assms
  by (simp add: nth_default_nth nth_append)

lemma getD_append_right:
  assumes "length G \<le> i"
  shows "nth_default (0, 0) (G @ X) i =
    nth_default (0, 0) X (i - length G)"
  using getD_app_right[OF assms, of X] .

lemma index_decomp:
  assumes L: "0 < (L::nat)"
    and i: "i < n * L"
  shows "\<exists>k q. k < n \<and> q < L \<and>
    i = k * L + q"
proof -
  have k: "i div L < n"
    using i L by (simp add: div_less_iff_less_mult)
  have q: "i mod L < L"
    by (rule mod_less_divisor[OF L])
  have eq: "i = i div L * L + i mod L"
    using div_mult_mod_eq[of i L] by simp
  show ?thesis using k q eq by blast
qed

lemma copies_map_length:
  "length (concat
    (map (\<lambda>k. map (f k) B) [0..<n])) =
    n * length B"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have dec:
    "concat
      (map (\<lambda>k. map (f k) B) [0..<Suc n]) =
      concat
        (map (\<lambda>k. map (f k) B) [0..<n]) @
      map (f n) B"
    by simp
  show ?case using Suc.IH dec
    by (simp add: algebra_simps)
qed

lemma copies_map_getD:
  assumes kn: "k < n"
    and qB: "q < length B"
  shows
    "nth_default (0, 0)
      (concat (map (\<lambda>k. map (f k) B) [0..<n]))
      (k * length B + q) =
      f k (nth_default (0, 0) B q)"
  using kn
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  let ?C =
    "concat (map (\<lambda>k. map (f k) B) [0..<n])"
  have dec:
    "concat
      (map (\<lambda>k. map (f k) B) [0..<Suc n]) =
      ?C @ map (f n) B"
    by simp
  show ?case
  proof (cases "k < n")
    case True
    have ix: "k * length B + q < length ?C"
    proof -
      have "k * length B + q <
          (k + 1) * length B"
        using qB by (simp add: algebra_simps)
      also have "\<dots> \<le> n * length B"
      proof -
        have "k + 1 \<le> n" using True by simp
        then have "(k + 1) * length B \<le>
            n * length B"
          by (rule mult_le_mono1)
        then show ?thesis .
      qed
      also have "\<dots> = length ?C"
        using copies_map_length[
          of f B n] by simp
      finally show ?thesis .
    qed
    have left:
      "nth_default (0, 0)
        (?C @ map (f n) B)
        (k * length B + q) =
        nth_default (0, 0) ?C
          (k * length B + q)"
      by (rule getD_append_left[OF ix])
    show ?thesis
      using dec left Suc.IH[OF True] by simp
  next
    case False
    have keq: "k = n" using Suc.prems False by simp
    have clen: "length ?C = n * length B"
      by (rule copies_map_length)
    have right:
      "nth_default (0, 0)
        (?C @ map (f n) B)
        (n * length B + q) =
        nth_default (0, 0) (map (f n) B) q"
      using getD_append_right[
        of ?C "n * length B + q" "map (f n) B"]
        clen by simp
    have mapped:
      "nth_default (0, 0) (map (f n) B) q =
        f n (nth_default (0, 0) B q)"
      using qB
      by (simp add: nth_default_nth)
    show ?thesis using dec keq right mapped by simp
  qed
qed

definition copyExp ::
  "pairseq \<Rightarrow> pairseq \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> pairseq"
  where
  "copyExp G B d0 n =
    G @ concat
      (map
        (\<lambda>k.
          map (\<lambda>p. (fst p + k * d0, snd p)) B)
        [0..<n])"

lemma copyExp_length:
  "length (copyExp G B d0 n) =
    length G + n * length B"
  by (simp add: copyExp_def copies_map_length)

lemma copyExp_getD_pre:
  assumes "i < length G"
  shows "nth_default (0, 0) (copyExp G B d0 n) i =
    nth_default (0, 0) G i"
  unfolding copyExp_def
  by (rule getD_append_left[OF assms])

lemma copyExp_getD_copy:
  assumes "k < n" "q < length B"
  shows
    "nth_default (0, 0) (copyExp G B d0 n)
      (length G + (k * length B + q)) =
      (fst (nth_default (0, 0) B q) + k * d0,
       snd (nth_default (0, 0) B q))"
proof -
  have right:
    "nth_default (0, 0) (copyExp G B d0 n)
        (length G + (k * length B + q)) =
      nth_default (0, 0)
        (concat
          (map
            (\<lambda>k.
              map
                (\<lambda>p. (fst p + k * d0, snd p)) B)
            [0..<n]))
        (k * length B + q)"
  proof -
    let ?X =
      "concat
        (map
          (\<lambda>k.
            map
              (\<lambda>p. (fst p + k * d0, snd p)) B)
          [0..<n])"
    note r = getD_append_right[
      of G "length G + (k * length B + q)" ?X]
    show ?thesis unfolding copyExp_def
      using r by simp
  qed
  show ?thesis
    using right copies_map_getD[
      OF assms, of
        "\<lambda>k p. (fst p + k * d0, snd p)"]
    by simp
qed

lemma hostM_getD_pre:
  assumes "i < length G"
  shows "nth_default (0, 0) (G @ B @ [lp]) i =
    nth_default (0, 0) G i"
  using assms
  by (simp add: getD_append_left)

lemma hostM_getD_blk:
  assumes "q < length B"
  shows
    "nth_default (0, 0) (G @ B @ [lp])
      (length G + q) =
      nth_default (0, 0) B q"
proof -
  have left:
    "nth_default (0, 0) (G @ B @ [lp])
        (length G + q) =
      nth_default (0, 0) (G @ B) (length G + q)"
  proof -
    note l = getD_append_left[
      of "length G + q" "G @ B" "[lp]"]
    show ?thesis using l assms by simp
  qed
  have right:
    "nth_default (0, 0) (G @ B) (length G + q) =
      nth_default (0, 0) B q"
  proof -
    note r = getD_append_right[
      of G "length G + q" B]
    show ?thesis using r by simp
  qed
  show ?thesis using left right by simp
qed

lemma hostM_length:
  "length (G @ B @ [lp]) = length G + length B + 1"
  by simp

lemma r1ok_copyExp:
  assumes hr: "r1ok (G @ B @ [lp])"
    and hmin:
      "\<forall>k q. 0 < k \<longrightarrow> k < n \<longrightarrow>
        q < length B \<longrightarrow>
        (\<forall>r. r < q \<longrightarrow>
          fst (nth_default (0, 0) B q) \<le>
            fst (nth_default (0, 0) B r)) \<longrightarrow>
        0 < fst (nth_default (0, 0) B q) + k * d0
          \<longrightarrow>
        (\<exists>p.
          p < length G + (k * length B + q) \<and>
          fst (nth_default (0, 0)
              (copyExp G B d0 n) p) + 1 =
            fst (nth_default (0, 0) B q) + k * d0 \<and>
          (\<forall>l.
            p < l \<longrightarrow>
            l < length G + (k * length B + q)
              \<longrightarrow>
            fst (nth_default (0, 0) B q) + k * d0
              \<le> fst
                  (nth_default (0, 0)
                    (copyExp G B d0 n) l)) \<and>
          snd (nth_default (0, 0) B q) \<le>
            snd
              (nth_default (0, 0)
                (copyExp G B d0 n) p) + 1)"
  shows "r1ok (copyExp G B d0 n)"
  unfolding r1ok_def
proof (intro allI impI)
  fix j
  assume jl: "j < length (copyExp G B d0 n)"
    and jpos:
      "0 < fst
        (nth_default (0, 0)
          (copyExp G B d0 n) j)"
  have jbound: "j < length G + n * length B"
    using jl by (simp add: copyExp_length)
  show "\<exists>k. k < j \<and>
      fst (nth_default (0, 0)
          (copyExp G B d0 n) k) + 1 =
        fst (nth_default (0, 0)
          (copyExp G B d0 n) j) \<and>
      (\<forall>l. k < l \<longrightarrow> l < j \<longrightarrow>
        fst (nth_default (0, 0)
            (copyExp G B d0 n) j) \<le>
          fst (nth_default (0, 0)
            (copyExp G B d0 n) l)) \<and>
      snd (nth_default (0, 0)
          (copyExp G B d0 n) j) \<le>
        snd (nth_default (0, 0)
          (copyExp G B d0 n) k) + 1"
  proof (cases "j < length G + length B")
    case True
    have agree:
      "\<forall>i. i \<le> j \<longrightarrow>
        nth_default (0, 0) (copyExp G B d0 n) i =
          nth_default (0, 0) (G @ B @ [lp]) i"
    proof (intro allI impI)
      fix i
      assume ij: "i \<le> j"
      show "nth_default (0, 0) (copyExp G B d0 n) i =
          nth_default (0, 0) (G @ B @ [lp]) i"
      proof (cases "i < length G")
        case pre: True
        show ?thesis
          using copyExp_getD_pre[
              OF pre, of B d0 n]
            hostM_getD_pre[OF pre, of B lp]
          by simp
      next
        case pre: False
        have gi: "length G \<le> i" using pre by simp
        let ?q = "i - length G"
        have qB: "?q < length B"
          using True ij gi by presburger
        have npos: "0 < n"
        proof (rule ccontr)
          assume "\<not> 0 < n"
          then have "n = 0" by simp
          then show False using jbound gi ij by simp
        qed
        have ieq:
          "i = length G + (0 * length B + ?q)"
          using gi by simp
        have ex:
          "nth_default (0, 0)
              (copyExp G B d0 n) i =
            (fst (nth_default (0, 0) B ?q),
             snd (nth_default (0, 0) B ?q))"
        proof -
          have at:
            "nth_default (0, 0)
                (copyExp G B d0 n)
                (length G +
                  (0 * length B + ?q)) =
              (fst (nth_default (0, 0) B ?q) +
                  0 * d0,
               snd (nth_default (0, 0) B ?q))"
            by (rule copyExp_getD_copy[
              OF npos qB])
          show ?thesis using at ieq by simp
        qed
        have host:
          "nth_default (0, 0) (G @ B @ [lp]) i =
            nth_default (0, 0) B ?q"
        proof -
          have at:
            "nth_default (0, 0) (G @ B @ [lp])
                (length G + ?q) =
              nth_default (0, 0) B ?q"
            by (rule hostM_getD_blk[OF qB])
          show ?thesis using at gi by simp
        qed
        show ?thesis using ex host by simp
      qed
    qed
    have jhost: "j < length (G @ B @ [lp])"
      using True by simp
    have poshost:
      "0 < fst
        (nth_default (0, 0) (G @ B @ [lp]) j)"
      using jpos agree[rule_format, of j] by simp
    from hr jhost poshost obtain p where
      pj: "p < j"
      and lev:
        "fst (nth_default (0, 0)
            (G @ B @ [lp]) p) + 1 =
          fst (nth_default (0, 0)
            (G @ B @ [lp]) j)"
      and between:
        "\<forall>l. p < l \<longrightarrow> l < j \<longrightarrow>
          fst (nth_default (0, 0)
              (G @ B @ [lp]) j) \<le>
            fst (nth_default (0, 0)
              (G @ B @ [lp]) l)"
      and snd:
        "snd (nth_default (0, 0)
            (G @ B @ [lp]) j) \<le>
          snd (nth_default (0, 0)
            (G @ B @ [lp]) p) + 1"
      unfolding r1ok_def by blast
    have ap:
      "nth_default (0, 0) (copyExp G B d0 n) p =
        nth_default (0, 0) (G @ B @ [lp]) p"
      by (rule agree[rule_format]) (use pj in simp)
    have aj:
      "nth_default (0, 0) (copyExp G B d0 n) j =
        nth_default (0, 0) (G @ B @ [lp]) j"
      by (rule agree[rule_format]) simp
    show ?thesis
    proof (intro exI[of _ p] conjI)
      show "p < j" using pj .
      show "fst (nth_default (0, 0)
            (copyExp G B d0 n) p) + 1 =
          fst (nth_default (0, 0)
            (copyExp G B d0 n) j)"
        using lev ap aj by simp
      show "\<forall>l. p < l \<longrightarrow> l < j \<longrightarrow>
          fst (nth_default (0, 0)
              (copyExp G B d0 n) j) \<le>
            fst (nth_default (0, 0)
              (copyExp G B d0 n) l)"
      proof (intro allI impI)
        fix l
        assume pl: "p < l" and lj: "l < j"
        have al:
          "nth_default (0, 0) (copyExp G B d0 n) l =
            nth_default (0, 0) (G @ B @ [lp]) l"
          by (rule agree[rule_format]) (use lj in simp)
        show "fst (nth_default (0, 0)
              (copyExp G B d0 n) j) \<le>
            fst (nth_default (0, 0)
              (copyExp G B d0 n) l)"
          using between[rule_format, OF pl lj] aj al
          by simp
      qed
      show "snd (nth_default (0, 0)
            (copyExp G B d0 n) j) \<le>
          snd (nth_default (0, 0)
            (copyExp G B d0 n) p) + 1"
        using snd aj ap by simp
    qed
  next
    case False
    have lower: "length G + length B \<le> j"
      using False by simp
    have Bpos: "0 < length B"
    proof (rule ccontr)
      assume "\<not> 0 < length B"
      then have "length B = 0" by simp
      then show False using jbound lower by simp
    qed
    have diff: "j - length G < n * length B"
    proof -
      have "length G \<le> j" using lower by simp
      then show ?thesis
        using jbound
        by (simp add: less_diff_conv2 add.commute)
    qed
    obtain k q where
      kn: "k < n" and qB: "q < length B"
      and decomp:
        "j - length G = k * length B + q"
      by (meson index_decomp[OF Bpos diff])
    have kpos: "0 < k"
    proof (rule ccontr)
      assume "\<not> 0 < k"
      then have "k = 0" by simp
      then show False using lower decomp qB by simp
    qed
    have jeq:
      "j = length G + (k * length B + q)"
      using lower decomp by presburger
    have jcopy:
      "nth_default (0, 0)
          (copyExp G B d0 n) j =
        (fst (nth_default (0, 0) B q) + k * d0,
         snd (nth_default (0, 0) B q))"
    proof -
      have at:
        "nth_default (0, 0)
            (copyExp G B d0 n)
            (length G + (k * length B + q)) =
          (fst (nth_default (0, 0) B q) + k * d0,
           snd (nth_default (0, 0) B q))"
        by (rule copyExp_getD_copy[OF kn qB])
      show ?thesis using at jeq by simp
    qed
    have poscopy:
      "0 < fst (nth_default (0, 0) B q) + k * d0"
      using jpos jcopy by simp
    show ?thesis
    proof (cases
        "\<forall>r. r < q \<longrightarrow>
          fst (nth_default (0, 0) B q) \<le>
            fst (nth_default (0, 0) B r)")
      case minimal: True
      have ex:
        "\<exists>p.
          p < length G + (k * length B + q) \<and>
          fst (nth_default (0, 0)
              (copyExp G B d0 n) p) + 1 =
            fst (nth_default (0, 0) B q) + k * d0 \<and>
          (\<forall>l.
            p < l \<longrightarrow>
            l < length G + (k * length B + q)
              \<longrightarrow>
            fst (nth_default (0, 0) B q) + k * d0
              \<le> fst
                  (nth_default (0, 0)
                    (copyExp G B d0 n) l)) \<and>
          snd (nth_default (0, 0) B q) \<le>
            snd
              (nth_default (0, 0)
                (copyExp G B d0 n) p) + 1"
      proof (rule hmin[rule_format])
        show "0 < k" using kpos .
        show "k < n" using kn .
        show "q < length B" using qB .
        show "\<And>r. r < q \<Longrightarrow>
            fst (nth_default (0, 0) B q) \<le>
              fst (nth_default (0, 0) B r)"
          using minimal by blast
        show "0 < fst (nth_default (0, 0) B q) + k * d0"
          using poscopy .
      qed
      show ?thesis using ex jeq jcopy by simp
    next
      case not_minimal: False
      then obtain r where
        rq: "r < q"
        and dip:
          "fst (nth_default (0, 0) B r) <
            fst (nth_default (0, 0) B q)"
        by auto
      have qpos:
        "0 < fst (nth_default (0, 0) B q)"
        using dip by simp
      have hostq:
        "length G + q < length (G @ B @ [lp])"
        using qB by simp
      have hostqpos:
        "0 < fst
          (nth_default (0, 0)
            (G @ B @ [lp]) (length G + q))"
      proof -
        have eq:
          "nth_default (0, 0)
              (G @ B @ [lp]) (length G + q) =
            nth_default (0, 0) B q"
          by (rule hostM_getD_blk[OF qB])
        show ?thesis using qpos eq by simp
      qed
      from hr hostq hostqpos obtain p where
        phost: "p < length G + q"
        and lev:
          "fst (nth_default (0, 0)
              (G @ B @ [lp]) p) + 1 =
            fst (nth_default (0, 0)
              (G @ B @ [lp]) (length G + q))"
        and between:
          "\<forall>l. p < l \<longrightarrow>
            l < length G + q \<longrightarrow>
            fst (nth_default (0, 0)
                (G @ B @ [lp]) (length G + q)) \<le>
              fst (nth_default (0, 0)
                (G @ B @ [lp]) l)"
        and snd:
          "snd (nth_default (0, 0)
              (G @ B @ [lp]) (length G + q)) \<le>
            snd (nth_default (0, 0)
              (G @ B @ [lp]) p) + 1"
        unfolding r1ok_def by blast
      have gr_le_p: "length G + r \<le> p"
      proof (rule ccontr)
        assume "\<not> length G + r \<le> p"
        then have pp: "p < length G + r" by simp
        have br:
          "fst (nth_default (0, 0)
              (G @ B @ [lp]) (length G + q)) \<le>
            fst (nth_default (0, 0)
              (G @ B @ [lp]) (length G + r))"
          by (rule between[rule_format])
            (use pp rq in simp_all)
        have eqr:
          "nth_default (0, 0)
              (G @ B @ [lp]) (length G + r) =
            nth_default (0, 0) B r"
          by (rule hostM_getD_blk)
            (use rq qB in simp)
        have eqq:
          "nth_default (0, 0)
              (G @ B @ [lp]) (length G + q) =
            nth_default (0, 0) B q"
          by (rule hostM_getD_blk[OF qB])
        show False using br eqr eqq dip by simp
      qed
      let ?r' = "p - length G"
      have peq: "p = length G + ?r'"
        using gr_le_p by presburger
      have r'q: "?r' < q" using phost peq by simp
      have r'B: "?r' < length B"
        using r'q qB by simp
      have hostr:
        "nth_default (0, 0)
            (G @ B @ [lp]) p =
          nth_default (0, 0) B ?r'"
      proof -
        have at:
          "nth_default (0, 0)
              (G @ B @ [lp]) (length G + ?r') =
            nth_default (0, 0) B ?r'"
          by (rule hostM_getD_blk[OF r'B])
        show ?thesis using at peq by simp
      qed
      have hostqeq:
        "nth_default (0, 0)
            (G @ B @ [lp]) (length G + q) =
          nth_default (0, 0) B q"
        by (rule hostM_getD_blk[OF qB])
      let ?p' = "length G + (k * length B + ?r')"
      have p'j: "?p' < j" using r'q jeq by simp
      have p'copy:
        "nth_default (0, 0)
            (copyExp G B d0 n) ?p' =
          (fst (nth_default (0, 0) B ?r') + k * d0,
           snd (nth_default (0, 0) B ?r'))"
        by (rule copyExp_getD_copy[OF kn r'B])
      show ?thesis
      proof (intro exI[of _ ?p'] conjI)
        show "?p' < j" using p'j .
        show "fst (nth_default (0, 0)
              (copyExp G B d0 n) ?p') + 1 =
            fst (nth_default (0, 0)
              (copyExp G B d0 n) j)"
          using lev hostr hostqeq p'copy jcopy
          by simp
        show "\<forall>l. ?p' < l \<longrightarrow> l < j \<longrightarrow>
            fst (nth_default (0, 0)
                (copyExp G B d0 n) j) \<le>
              fst (nth_default (0, 0)
                (copyExp G B d0 n) l)"
        proof (intro allI impI)
          fix l
          assume pl: "?p' < l" and lj: "l < j"
          let ?base = "length G + k * length B"
          let ?rr = "l - ?base"
          have basele: "?base \<le> l" using pl by simp
          have rr1: "?r' < ?rr"
            using pl
            by (simp add: less_diff_conv add.commute
                add.assoc)
          have rr2: "?rr < q"
            using lj jeq basele
            by (simp add: less_diff_conv2 add.commute
                add.assoc)
          have leq:
            "l = length G + (k * length B + ?rr)"
            using basele by simp
          have rrB: "?rr < length B"
            using rr2 qB by simp
          have lcopy:
            "nth_default (0, 0)
                (copyExp G B d0 n) l =
              (fst (nth_default (0, 0) B ?rr) + k * d0,
               snd (nth_default (0, 0) B ?rr))"
          proof -
            have at:
              "nth_default (0, 0)
                  (copyExp G B d0 n)
                  (length G + (k * length B + ?rr)) =
                (fst (nth_default (0, 0) B ?rr) +
                    k * d0,
                 snd (nth_default (0, 0) B ?rr))"
              by (rule copyExp_getD_copy[OF kn rrB])
            show ?thesis using at leq by simp
          qed
          have host_between:
            "fst (nth_default (0, 0) B q) \<le>
              fst (nth_default (0, 0) B ?rr)"
          proof -
            have at:
              "fst (nth_default (0, 0)
                  (G @ B @ [lp]) (length G + q)) \<le>
                fst (nth_default (0, 0)
                  (G @ B @ [lp]) (length G + ?rr))"
              by (rule between[rule_format])
                (use rr1 rr2 peq in simp_all)
            have eqrr:
              "nth_default (0, 0)
                  (G @ B @ [lp]) (length G + ?rr) =
                nth_default (0, 0) B ?rr"
              by (rule hostM_getD_blk[OF rrB])
            show ?thesis using at hostqeq eqrr by simp
          qed
          show "fst (nth_default (0, 0)
                (copyExp G B d0 n) j) \<le>
              fst (nth_default (0, 0)
                (copyExp G B d0 n) l)"
            using jcopy lcopy host_between by simp
        qed
        show "snd (nth_default (0, 0)
              (copyExp G B d0 n) j) \<le>
            snd (nth_default (0, 0)
              (copyExp G B d0 n) ?p') + 1"
          using snd hostqeq hostr jcopy p'copy by simp
      qed
    qed
  qed
qed

lemma getD_mem:
  assumes "i < length l"
  shows "nth_default (0, 0) l i \<in> set l"
  using assms
  by (simp add: nth_default_nth nth_mem)

lemma dominated_PM_zero:
  fixes R :: pairseq
  assumes dom: "\<forall>x\<in>set R. v0 < fst x"
    and qB: "q < length ((v0, w0) # R)"
    and minimal:
      "\<forall>r. r < q \<longrightarrow>
        fst (nth_default (0, 0) ((v0, w0) # R) q)
          \<le> fst
              (nth_default (0, 0) ((v0, w0) # R) r)"
  shows "q = 0"
proof (rule ccontr)
  assume "q \<noteq> 0"
  then obtain q' where q: "q = Suc q'"
    by (cases q) auto
  have q'R: "q' < length R" using qB q by simp
  have mem:
    "nth_default (0, 0) R q' \<in> set R"
    by (rule getD_mem[OF q'R])
  have gt: "v0 < fst (nth_default (0, 0) R q')"
    using dom mem by blast
  have le:
    "fst (nth_default (0, 0) ((v0, w0) # R) q)
      \<le> fst
          (nth_default (0, 0) ((v0, w0) # R) 0)"
    by (rule minimal[rule_format]) (use q in simp)
  have le': "fst (nth_default (0, 0) R q') \<le> v0"
    using le q by simp
  have "v0 < v0"
  proof (rule less_le_trans)
    show "v0 < fst (nth_default (0, 0) R q')" by (rule gt)
    show "fst (nth_default (0, 0) R q') \<le> v0" by (rule le')
  qed
  then show False by simp
qed

lemma r1ok_min_d0zero:
  assumes B: "B = (v0, w0) # R"
    and dom: "\<forall>x\<in>set R. v0 < fst x"
    and hr: "r1ok (G @ B @ [lp])"
    and kpos: "0 < k"
    and kn: "k < n"
    and qB: "q < length B"
    and minimal:
      "\<forall>r. r < q \<longrightarrow>
        fst (nth_default (0, 0) B q) \<le>
          fst (nth_default (0, 0) B r)"
    and pos:
      "0 < fst (nth_default (0, 0) B q) + k * 0"
  shows
    "\<exists>p.
      p < length G + (k * length B + q) \<and>
      fst (nth_default (0, 0)
          (copyExp G B 0 n) p) + 1 =
        fst (nth_default (0, 0) B q) + k * 0 \<and>
      (\<forall>l. p < l \<longrightarrow>
        l < length G + (k * length B + q)
          \<longrightarrow>
        fst (nth_default (0, 0) B q) + k * 0 \<le>
          fst (nth_default (0, 0)
            (copyExp G B 0 n) l)) \<and>
      snd (nth_default (0, 0) B q) \<le>
        snd (nth_default (0, 0)
          (copyExp G B 0 n) p) + 1"
proof -
  have qB':
    "q < length ((v0, w0) # R)"
    using qB B by simp
  have minimal':
    "\<forall>r. r < q \<longrightarrow>
      fst (nth_default (0, 0) ((v0, w0) # R) q) \<le>
        fst (nth_default (0, 0) ((v0, w0) # R) r)"
    using minimal B by simp
  have q0: "q = 0"
  proof (rule dominated_PM_zero)
    show "\<forall>x\<in>set R. v0 < fst x" by (rule dom)
    show "q < length ((v0, w0) # R)" by (rule qB')
    show
      "\<forall>r. r < q \<longrightarrow>
        fst (nth_default (0, 0) ((v0, w0) # R) q) \<le>
          fst (nth_default (0, 0) ((v0, w0) # R) r)"
      by (rule minimal')
  qed
  have B0: "nth_default (0, 0) B 0 = (v0, w0)"
    using B by simp
  have vpos: "0 < v0"
    using pos q0 B0 by simp
  have hostG:
    "nth_default (0, 0) (G @ B @ [lp]) (length G) =
      (v0, w0)"
  proof -
    have at:
      "nth_default (0, 0) (G @ B @ [lp])
          (length G + 0) =
        nth_default (0, 0) B 0"
      by (rule hostM_getD_blk) (use B in simp)
    show ?thesis using at B0 by simp
  qed
  have hostlen:
    "length G < length (G @ B @ [lp])"
    using B by simp
  have hostpos:
    "0 < fst
      (nth_default (0, 0)
        (G @ B @ [lp]) (length G))"
    using hostG vpos by simp
  from hr hostlen hostpos obtain p where
    pG: "p < length G"
    and lev:
      "fst (nth_default (0, 0)
          (G @ B @ [lp]) p) + 1 =
        fst (nth_default (0, 0)
          (G @ B @ [lp]) (length G))"
    and between:
      "\<forall>l. p < l \<longrightarrow> l < length G \<longrightarrow>
        fst (nth_default (0, 0)
            (G @ B @ [lp]) (length G)) \<le>
          fst (nth_default (0, 0)
            (G @ B @ [lp]) l)"
    and snd:
      "snd (nth_default (0, 0)
          (G @ B @ [lp]) (length G)) \<le>
        snd (nth_default (0, 0)
          (G @ B @ [lp]) p) + 1"
    unfolding r1ok_def by blast
  have hostp:
    "nth_default (0, 0) (G @ B @ [lp]) p =
      nth_default (0, 0) G p"
    by (rule hostM_getD_pre[OF pG])
  have lev':
    "fst (nth_default (0, 0) G p) + 1 = v0"
    using lev hostp hostG by simp
  have snd':
    "w0 \<le> snd (nth_default (0, 0) G p) + 1"
    using snd hostp hostG by simp
  have pcopy:
    "nth_default (0, 0) (copyExp G B 0 n) p =
      nth_default (0, 0) G p"
    by (rule copyExp_getD_pre[OF pG])
  have bound:
    "p < length G + (k * length B + q)"
    using pG by simp
  show ?thesis
  proof (intro exI[of _ p] conjI)
    show "p < length G + (k * length B + q)"
      using bound .
    show "fst (nth_default (0, 0)
          (copyExp G B 0 n) p) + 1 =
        fst (nth_default (0, 0) B q) + k * 0"
      using pcopy lev' B0 q0 by simp
    show "\<forall>l. p < l \<longrightarrow>
        l < length G + (k * length B + q)
          \<longrightarrow>
        fst (nth_default (0, 0) B q) + k * 0 \<le>
          fst (nth_default (0, 0)
            (copyExp G B 0 n) l)"
    proof (intro allI impI)
      fix l
      assume pl: "p < l"
        and lu: "l < length G + (k * length B + q)"
      show "fst (nth_default (0, 0) B q) + k * 0 \<le>
          fst (nth_default (0, 0)
            (copyExp G B 0 n) l)"
      proof (cases "l < length G")
        case True
        have hostl:
          "nth_default (0, 0) (G @ B @ [lp]) l =
            nth_default (0, 0) G l"
          by (rule hostM_getD_pre[OF True])
        have cl:
          "nth_default (0, 0) (copyExp G B 0 n) l =
            nth_default (0, 0) G l"
          by (rule copyExp_getD_pre[OF True])
        have "v0 \<le> fst (nth_default (0, 0) G l)"
          using between[rule_format, OF pl True]
            hostG hostl by simp
        then show ?thesis using cl B0 q0 by simp
      next
        case False
        have Gl: "length G \<le> l" using False by simp
        have diff:
          "l - length G < n * length B"
        proof -
          have upto:
            "length G + (k * length B + q)
              \<le> length G + n * length B"
          proof -
            have skn: "Suc k \<le> n" using kn by simp
            have prod:
              "Suc k * length B \<le> n * length B"
              by (rule mult_le_mono1[OF skn])
            have
              "k * length B + q \<le>
                k * length B + length B"
              using qB by simp
            also have
              "\<dots> = Suc k * length B"
              by (simp add: ac_simps)
            also have
              "\<dots> \<le> n * length B"
              by (rule prod)
            finally show ?thesis by simp
          qed
          have "l < length G + n * length B"
            using lu upto by simp
          then show ?thesis using Gl
            by (simp add: less_diff_conv2 add.commute)
        qed
        have Bpos: "0 < length B" using B by simp
        obtain k' r where
          k'n: "k' < n" and rB: "r < length B"
          and dec: "l - length G = k' * length B + r"
          by (meson index_decomp[OF Bpos diff])
        have leq:
          "l = length G + (k' * length B + r)"
          using Gl dec by simp
        have lcopy:
          "nth_default (0, 0) (copyExp G B 0 n) l =
            (fst (nth_default (0, 0) B r),
             snd (nth_default (0, 0) B r))"
        proof -
          have at:
            "nth_default (0, 0)
                (copyExp G B 0 n)
                (length G + (k' * length B + r)) =
              (fst (nth_default (0, 0) B r) + k' * 0,
               snd (nth_default (0, 0) B r))"
            by (rule copyExp_getD_copy[OF k'n rB])
          show ?thesis using at leq by simp
        qed
        have base:
          "v0 \<le> fst (nth_default (0, 0) B r)"
        proof (cases r)
          case 0
          then show ?thesis using B0 by simp
        next
          case (Suc r')
          have r'R: "r' < length R"
            using rB B Suc by simp
          have mem:
            "nth_default (0, 0) R r' \<in> set R"
            by (rule getD_mem[OF r'R])
          have "v0 < fst (nth_default (0, 0) R r')"
            using dom mem by blast
          then show ?thesis using B Suc
            by (simp add: nth_default_Cons)
        qed
        show ?thesis using lcopy base B0 q0 by simp
      qed
    qed
    show "snd (nth_default (0, 0) B q) \<le>
        snd (nth_default (0, 0)
          (copyExp G B 0 n) p) + 1"
      using B0 q0 pcopy snd' by simp
  qed
qed

lemma r1ok_min_d0pos:
  assumes B: "B = (v0, w0) # R"
    and dom: "\<forall>x\<in>set R. v0 < fst x"
    and d0pos: "0 < d0"
    and lp1: "fst lp = v0 + d0"
    and step:
      "\<forall>r. r + 1 < length B \<longrightarrow>
        fst (nth_default (0, 0) B (r + 1)) \<le>
          fst (nth_default (0, 0) B r) + 1"
    and lpstep:
      "fst lp \<le>
        fst (nth_default (0, 0) B (length B - 1)) + 1"
    and climb:
      "\<forall>r'. r' < length B \<longrightarrow>
        fst (nth_default (0, 0) B r') = v0 + d0 - 1
        \<longrightarrow>
        (\<forall>rr. r' < rr \<longrightarrow> rr < length B
          \<longrightarrow> v0 + d0 \<le>
            fst (nth_default (0, 0) B rr))
        \<longrightarrow>
        w0 \<le> snd (nth_default (0, 0) B r') + 1"
    and kpos: "0 < k"
    and kn: "k < n"
    and qB: "q < length B"
    and minimal:
      "\<forall>r. r < q \<longrightarrow>
        fst (nth_default (0, 0) B q) \<le>
          fst (nth_default (0, 0) B r)"
    and pos:
      "0 < fst (nth_default (0, 0) B q) + k * d0"
  shows
    "\<exists>p.
      p < length G + (k * length B + q) \<and>
      fst (nth_default (0, 0)
          (copyExp G B d0 n) p) + 1 =
        fst (nth_default (0, 0) B q) + k * d0 \<and>
      (\<forall>l. p < l \<longrightarrow>
        l < length G + (k * length B + q)
          \<longrightarrow>
        fst (nth_default (0, 0) B q) + k * d0 \<le>
          fst (nth_default (0, 0)
            (copyExp G B d0 n) l)) \<and>
      snd (nth_default (0, 0) B q) \<le>
        snd (nth_default (0, 0)
          (copyExp G B d0 n) p) + 1"
proof -
  have qB':
    "q < length ((v0, w0) # R)"
    using qB B by simp
  have minimal':
    "\<forall>r. r < q \<longrightarrow>
      fst (nth_default (0, 0) ((v0, w0) # R) q) \<le>
        fst (nth_default (0, 0) ((v0, w0) # R) r)"
    using minimal B by simp
  have q0: "q = 0"
  proof (rule dominated_PM_zero)
    show "\<forall>x\<in>set R. v0 < fst x" by (rule dom)
    show "q < length ((v0, w0) # R)" by (rule qB')
    show
      "\<forall>r. r < q \<longrightarrow>
        fst (nth_default (0, 0) ((v0, w0) # R) q) \<le>
          fst (nth_default (0, 0) ((v0, w0) # R) r)"
      by (rule minimal')
  qed
  have Lpos: "0 < length B" using B by simp
  have B0: "nth_default (0, 0) B 0 = (v0, w0)"
    using B by simp
  let ?Q =
    "\<lambda>r. r \<le> length B - 1 \<and>
      fst (nth_default (0, 0) B r) \<le> v0 + d0 - 1"
  let ?r' = "Greatest ?Q"
  have Q0: "?Q 0"
  proof
    show "0 \<le> length B - 1" by simp
    show "fst (nth_default (0, 0) B 0) \<le> v0 + d0 - 1"
      using B0 d0pos by simp
  qed
  have Qbound: "\<And>r. ?Q r \<Longrightarrow> r \<le> length B - 1"
    by simp
  have Qr: "?Q ?r'"
  proof (rule GreatestI_nat)
    show "?Q 0" by (rule Q0)
    fix y
    assume "?Q y"
    then show "y \<le> length B - 1" by simp
  qed
  have r'le: "?r' \<le> length B - 1"
    using Qr by simp
  have greatest:
    "\<And>rr. ?Q rr \<Longrightarrow> rr \<le> ?r'"
  proof -
    fix rr
    assume Qrr: "?Q rr"
    show "rr \<le> ?r'"
    proof (rule Greatest_le_nat)
      show "?Q rr" by (rule Qrr)
      fix y
      assume "?Q y"
      then show "y \<le> length B - 1" by simp
    qed
  qed
  have after:
    "\<And>rr. ?r' < rr \<Longrightarrow> rr < length B \<Longrightarrow>
      v0 + d0 \<le> fst (nth_default (0, 0) B rr)"
  proof -
    fix rr
    assume rrr: "?r' < rr" and rrB: "rr < length B"
    have rrle: "rr \<le> length B - 1"
      using rrB Lpos by simp
    have notsmall:
      "\<not> fst (nth_default (0, 0) B rr) \<le>
        v0 + d0 - 1"
    proof
      assume small:
        "fst (nth_default (0, 0) B rr) \<le>
          v0 + d0 - 1"
      have "?Q rr" using rrle small by simp
      then have "rr \<le> ?r'" by (rule greatest)
      with rrr show False by simp
    qed
    show
      "v0 + d0 \<le> fst (nth_default (0, 0) B rr)"
      using notsmall d0pos by simp
  qed
  have exact:
    "fst (nth_default (0, 0) B ?r') = v0 + d0 - 1"
  proof -
    have upper:
      "fst (nth_default (0, 0) B ?r') \<le>
        v0 + d0 - 1"
      using Qr by simp
    show ?thesis
    proof (cases "?r' < length B - 1")
      case True
      have succB: "?r' + 1 < length B"
        using True Lpos by simp
      have high:
        "v0 + d0 \<le>
          fst (nth_default (0, 0) B (?r' + 1))"
        by (rule after) (use succB in simp_all)
      have lowstep:
        "fst (nth_default (0, 0) B (?r' + 1)) \<le>
          fst (nth_default (0, 0) B ?r') + 1"
        by (rule step[rule_format, OF succB])
      show ?thesis using upper high lowstep d0pos
        by presburger
    next
      case False
      have eq: "?r' = length B - 1"
        using False r'le by simp
      have low:
        "v0 + d0 \<le>
          fst (nth_default (0, 0) B ?r') + 1"
        using lpstep lp1 eq by simp
      show ?thesis using upper low d0pos
        by presburger
    qed
  qed
  obtain m where km: "k = Suc m"
    using kpos by (cases k) auto
  have km1: "k - 1 = m" using km by simp
  have kL:
    "k * length B = (k - 1) * length B + length B"
    using km by (simp add: ac_simps)
  have kd:
    "k * d0 = (k - 1) * d0 + d0"
    using km by (simp add: ac_simps)
  have prevn: "k - 1 < n" using kn kpos by simp
  have r'B: "?r' < length B"
    using r'le Lpos by presburger
  let ?p = "length G + ((k - 1) * length B + ?r')"
  show ?thesis
  proof (intro exI[of _ ?p] conjI)
    show "?p < length G + (k * length B + q)"
      using r'B kL q0 by simp
    show
      "fst (nth_default (0, 0)
          (copyExp G B d0 n) ?p) + 1 =
        fst (nth_default (0, 0) B q) + k * d0"
    proof -
      have at:
        "nth_default (0, 0) (copyExp G B d0 n) ?p =
          (fst (nth_default (0, 0) B ?r') +
              (k - 1) * d0,
           snd (nth_default (0, 0) B ?r'))"
        by (rule copyExp_getD_copy[OF prevn r'B])
      have atfst:
        "fst (nth_default (0, 0)
            (copyExp G B d0 n) ?p) =
          fst (nth_default (0, 0) B ?r') +
            (k - 1) * d0"
        using at by simp
      have qfst:
        "fst (nth_default (0, 0) B q) = v0"
        using B0 q0 by simp
      show ?thesis using atfst qfst exact kd d0pos
        by presburger
    qed
    show
      "\<forall>l. ?p < l \<longrightarrow>
        l < length G + (k * length B + q)
          \<longrightarrow>
        fst (nth_default (0, 0) B q) + k * d0 \<le>
          fst (nth_default (0, 0)
            (copyExp G B d0 n) l)"
    proof (intro allI impI)
      fix l
      assume pl: "?p < l"
        and lu: "l < length G + (k * length B + q)"
      have Gl: "length G \<le> l" using pl by simp
      have top:
        "l < length G + n * length B"
      proof -
        have knle: "k \<le> n" using kn by simp
        have mult:
          "k * length B \<le> n * length B"
        proof (rule mult_right_mono)
          show "k \<le> n" by (rule knle)
          show "0 \<le> length B" by simp
        qed
        have lu':
          "l < length G + k * length B"
          using lu q0 by simp
        have addmult:
          "length G + k * length B \<le>
            length G + n * length B"
          using mult by simp
        show ?thesis
        proof (rule less_le_trans)
          show "l < length G + k * length B" by (rule lu')
          show
            "length G + k * length B \<le>
              length G + n * length B"
            by (rule addmult)
        qed
      qed
      have diff: "l - length G < n * length B"
        using Gl top
        by (simp add: less_diff_conv2 add.commute)
      obtain k'' rr where
        k''n: "k'' < n" and rrB: "rr < length B"
        and dec: "l - length G = k'' * length B + rr"
        by (meson index_decomp[OF Lpos diff])
      have leq:
        "l = length G + (k'' * length B + rr)"
        using Gl dec by simp
      have lower:
        "(k - 1) * length B + ?r'
          < k'' * length B + rr"
        using pl leq by simp
      have upper:
        "k'' * length B + rr < k * length B"
        using lu leq q0 by simp
      have k''eq: "k'' = k - 1"
      proof (rule antisym)
        show "k'' \<le> k - 1"
        proof (rule ccontr)
          assume "\<not> k'' \<le> k - 1"
          then have kk: "k \<le> k''" using kpos by simp
          have mult:
            "k * length B \<le> k'' * length B"
          proof (rule mult_right_mono)
            show "k \<le> k''" by (rule kk)
            show "0 \<le> length B" by simp
          qed
          show False using upper mult by simp
        qed
        show "k - 1 \<le> k''"
        proof (rule ccontr)
          assume "\<not> k - 1 \<le> k''"
          then have sk:
            "Suc k'' \<le> k - 1" by simp
          have inside:
            "k'' * length B + rr <
              Suc k'' * length B"
            using rrB by (simp add: ac_simps)
          have mult:
            "Suc k'' * length B \<le>
              (k - 1) * length B"
          proof (rule mult_right_mono)
            show "Suc k'' \<le> k - 1" by (rule sk)
            show "0 \<le> length B" by simp
          qed
          show False using lower inside mult by simp
        qed
      qed
      have r'rr: "?r' < rr"
        using lower k''eq by simp
      have at:
        "nth_default (0, 0) (copyExp G B d0 n) l =
          (fst (nth_default (0, 0) B rr) +
              (k - 1) * d0,
           snd (nth_default (0, 0) B rr))"
      proof -
        have at0:
          "nth_default (0, 0) (copyExp G B d0 n)
              (length G + ((k - 1) * length B + rr)) =
            (fst (nth_default (0, 0) B rr) +
                (k - 1) * d0,
             snd (nth_default (0, 0) B rr))"
          by (rule copyExp_getD_copy[OF prevn rrB])
        show ?thesis using at0 leq k''eq by simp
      qed
      have high:
        "v0 + d0 \<le>
          fst (nth_default (0, 0) B rr)"
        by (rule after[OF r'rr rrB])
      show
        "fst (nth_default (0, 0) B q) + k * d0 \<le>
          fst (nth_default (0, 0)
            (copyExp G B d0 n) l)"
        using at B0 q0 high kd by simp
    qed
    show
      "snd (nth_default (0, 0) B q) \<le>
        snd (nth_default (0, 0)
          (copyExp G B d0 n) ?p) + 1"
    proof -
      have at:
        "nth_default (0, 0) (copyExp G B d0 n) ?p =
          (fst (nth_default (0, 0) B ?r') +
              (k - 1) * d0,
           snd (nth_default (0, 0) B ?r'))"
        by (rule copyExp_getD_copy[OF prevn r'B])
      have climb':
        "w0 \<le> snd (nth_default (0, 0) B ?r') + 1"
      proof (rule climb[rule_format, OF r'B exact])
        fix rr
        assume a: "?r' < rr" and b: "rr < length B"
        show "v0 + d0 \<le>
          fst (nth_default (0, 0) B rr)"
          by (rule after[OF a b])
      qed
      show ?thesis using at B0 q0 climb' by simp
    qed
  qed
qed

lemma hostM_getD_lp:
  "nth_default (0, 0) (G @ B @ [lp])
      (length G + length B) = lp"
  by (simp add: nth_default_nth nth_append)

lemma r1ok_Pred:
  assumes "r1ok M"
  shows "r1ok (Pred M)"
  unfolding Pred_def
  using assms r1ok_dropLast by auto

lemma climb_bound:
  assumes M:
      "M = G @ ((v0, w0) # R) @ [lp]"
    and d0pos: "0 < d0"
    and lp1: "fst lp = v0 + d0"
    and wlt: "w0 < snd lp"
    and nl1:
      "nextrel1 M (length G) (length M - 1)"
    and rB: "r' < length ((v0, w0) # R)"
    and lev:
      "fst (nth_default (0, 0) ((v0, w0) # R) r') =
        v0 + d0 - 1"
    and after:
      "\<forall>rr. r' < rr \<longrightarrow>
        rr < length ((v0, w0) # R) \<longrightarrow>
        v0 + d0 \<le>
          fst (nth_default (0, 0)
            ((v0, w0) # R) rr)"
  shows
    "w0 \<le>
      snd (nth_default (0, 0) ((v0, w0) # R) r') + 1"
proof (cases r')
  case 0
  then show ?thesis by simp
next
  case (Suc r0)
  let ?B = "(v0, w0) # R"
  let ?H = "G @ ?B @ [lp]"
  let ?j = "length G + r'"
  let ?last = "length G + length ?B"
  have rpos: "0 < r'" using Suc by simp
  have Mlen: "length M = length G + length ?B + 1"
    using M by simp
  have last: "length M - 1 = ?last"
    using Mlen by simp
  have nl1':
    "nextrel1 ?H (length G) ?last"
    using nl1 M last by simp
  have e0r: "entry ?H 0 ?j = v0 + d0 - 1"
    unfolding entry_def
    using hostM_getD_blk[OF rB, of G lp] lev rB
    by (simp add: nth_default_nth)
  have e0last: "entry ?H 0 ?last = v0 + d0"
    unfolding entry_def
    using hostM_getD_lp[of G ?B lp] lp1
    by (simp add: nth_default_nth)
  have nr0: "nextrel0 ?H ?j ?last"
  proof (unfold nextrel0_def, intro conjI)
    show "?j < length ?H" using rB by simp
    show "?last < length ?H" by simp
    show "?j < ?last" using rB by simp
    show "entry ?H 0 ?j < entry ?H 0 ?last"
      using e0r e0last d0pos by presburger
    show
      "\<forall>j. ?j < j \<and> j < ?last \<longrightarrow>
        entry ?H 0 ?last \<le> entry ?H 0 j"
    proof (intro allI impI)
      fix j
      assume jb: "?j < j \<and> j < ?last"
      let ?rr = "j - length G"
      have GJ: "length G \<le> j" using jb by simp
      have jeq: "j = length G + ?rr" using GJ by simp
      have rrr: "r' < ?rr" using jb jeq by presburger
      have rrB: "?rr < length ?B" using jb jeq by presburger
      have at:
        "nth_default (0, 0) ?H j =
          nth_default (0, 0) ?B ?rr"
      proof -
        have at0:
          "nth_default (0, 0) ?H
              (length G + ?rr) =
            nth_default (0, 0) ?B ?rr"
          by (rule hostM_getD_blk[OF rrB])
        show ?thesis using at0 jeq by simp
      qed
      have high:
        "v0 + d0 \<le>
          fst (nth_default (0, 0) ?B ?rr)"
        by (rule after[rule_format, OF rrr rrB])
      have e0j:
        "entry ?H 0 j =
          fst (nth_default (0, 0) ?B ?rr)"
        unfolding entry_def
        using at rrB jeq
        by (simp add: nth_default_nth)
      show "entry ?H 0 ?last \<le> entry ?H 0 j"
        using e0last e0j high by simp
    qed
  qed
  have le: "le0 ?H ?j ?last"
  proof (unfold le0_def, intro conjI)
    show "?j < length ?H" using rB by simp
    show "?last < length ?H" by simp
    show "(nextrel0 ?H)\<^sup>*\<^sup>* ?j ?last"
    proof (rule r_into_rtranclp)
      show "nextrel0 ?H ?j ?last" by (rule nr0)
    qed
  qed
  have maxrule:
    "\<forall>j. length G < j \<and> le0 ?H j ?last
      \<longrightarrow> entry ?H 1 ?last \<le> entry ?H 1 j"
    using nl1' unfolding nextrel1_def by auto
  have Gj: "length G < ?j" using rpos by simp
  have max:
    "entry ?H 1 ?last \<le> entry ?H 1 ?j"
    by (rule maxrule[rule_format]) (use Gj le in simp)
  have e1last: "entry ?H 1 ?last = snd lp"
    unfolding entry_def
    using hostM_getD_lp[of G ?B lp]
    by (simp add: nth_default_nth)
  have e1r:
    "entry ?H 1 ?j =
      snd (nth_default (0, 0) ?B r')"
    unfolding entry_def
    using hostM_getD_blk[OF rB, of G lp] rB
    by (simp add: nth_default_nth)
  show ?thesis using max e1last e1r wlt by simp
qed

lemma r1ok_oper:
  assumes n1: "1 \<le> n"
    and hr: "r1ok M"
    and st: "steps1 M"
  shows "r1ok (M\<lbrakk>n\<rbrakk>)"
proof (cases "length M - 1 = 0")
  case True
  have eq: "M\<lbrakk>n\<rbrakk> = M"
    by (rule oper_eq_self_of_short[OF True])
  show ?thesis using eq hr by simp
next
  case short: False
  show ?thesis
  proof (cases
      "entry M 0 (length M - 1) = 0 \<and>
       entry M 1 (length M - 1) = 0")
    case True
    have eq: "M\<lbrakk>n\<rbrakk> = Pred M"
      by (rule oper_eq_pred_of_zero[OF short True])
    show ?thesis using eq r1ok_Pred[OF hr] by simp
  next
    case zero: False
    show ?thesis
    proof (cases
        "hasParent M (idx1 M (length M - 1))
          (length M - 1)")
      case False
      have eq: "M\<lbrakk>n\<rbrakk> = Pred M"
        by (rule oper_eq_pred_of_noParent[
              OF short zero False])
      show ?thesis using eq r1ok_Pred[OF hr] by simp
    next
      case hp: True
      have L: "1 < length M" using short by presburger
      obtain G v0 w0 R d0 lp where
        M:
          "M = G @ ((v0, w0) # R) @ [lp]"
        and X:
          "M\<lbrakk>n\<rbrakk> =
            G @ concat
              (map
                (\<lambda>k.
                  map
                    (\<lambda>p.
                      (fst p + k * d0, snd p))
                    ((v0, w0) # R))
                [0..<n])"
        and dom:
          "\<forall>x\<in>set R. v0 < fst x"
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
        by (rule oper_bad_blocks[OF L zero hp n1])
      let ?B = "(v0, w0) # R"
      let ?H = "G @ ?B @ [lp]"
      have X': "M\<lbrakk>n\<rbrakk> = copyExp G ?B d0 n"
        using X unfolding copyExp_def by simp
      have hrH: "r1ok ?H" using hr M by simp
      have stH: "steps1 ?H" using st M by simp
      have hstep:
        "\<forall>r. r + 1 < length ?B \<longrightarrow>
          fst (nth_default (0, 0) ?B (r + 1)) \<le>
            fst (nth_default (0, 0) ?B r) + 1"
      proof (intro allI impI)
        fix r
        assume succB: "r + 1 < length ?B"
        have idx:
          "length G + r + 1 =
            length G + (r + 1)" by simp
        have bound:
          "length G + r + 1 < length ?H"
          using succB by simp
        have hs:
          "fst (nth_default (0, 0) ?H
              (length G + r + 1)) \<le>
            fst (nth_default (0, 0) ?H
              (length G + r)) + 1"
          using steps1_iff[THEN iffD1, OF stH,
            rule_format, OF bound] .
        have at1:
          "nth_default (0, 0) ?H
              (length G + (r + 1)) =
            nth_default (0, 0) ?B (r + 1)"
          by (rule hostM_getD_blk[OF succB])
        have rB: "r < length ?B" using succB by simp
        have at0:
          "nth_default (0, 0) ?H (length G + r) =
            nth_default (0, 0) ?B r"
          by (rule hostM_getD_blk[OF rB])
        show
          "fst (nth_default (0, 0) ?B (r + 1)) \<le>
            fst (nth_default (0, 0) ?B r) + 1"
          using hs at1 at0 idx by simp
      qed
      have Bpos: "0 < length ?B" by simp
      have lastB: "length ?B - 1 < length ?B"
        using Bpos by simp
      have hostbound:
        "length G + (length ?B - 1) + 1 <
          length ?H"
        using Bpos by simp
      have hsLast:
        "fst (nth_default (0, 0) ?H
            (length G + (length ?B - 1) + 1)) \<le>
          fst (nth_default (0, 0) ?H
            (length G + (length ?B - 1))) + 1"
        using steps1_iff[THEN iffD1, OF stH,
          rule_format, OF hostbound] .
      have idxLast:
        "length G + (length ?B - 1) + 1 =
          length G + length ?B"
        using Bpos by simp
      have atlp:
        "nth_default (0, 0) ?H
            (length G + length ?B) = lp"
        by (rule hostM_getD_lp)
      have atlast:
        "nth_default (0, 0) ?H
            (length G + (length ?B - 1)) =
          nth_default (0, 0) ?B (length ?B - 1)"
        by (rule hostM_getD_blk[OF lastB])
      have lpstep:
        "fst lp \<le>
          fst (nth_default (0, 0) ?B
            (length ?B - 1)) + 1"
        using hsLast idxLast atlp atlast by simp
      show ?thesis
        unfolding X'
      proof (rule r1ok_copyExp[OF hrH])
        show
          "\<forall>k q. 0 < k \<longrightarrow> k < n \<longrightarrow>
            q < length ?B \<longrightarrow>
            (\<forall>r. r < q \<longrightarrow>
              fst (nth_default (0, 0) ?B q) \<le>
                fst (nth_default (0, 0) ?B r))
            \<longrightarrow>
            0 < fst (nth_default (0, 0) ?B q) +
                k * d0
            \<longrightarrow>
            (\<exists>p.
              p < length G + (k * length ?B + q) \<and>
              fst (nth_default (0, 0)
                  (copyExp G ?B d0 n) p) + 1 =
                fst (nth_default (0, 0) ?B q) +
                  k * d0 \<and>
              (\<forall>l. p < l \<longrightarrow>
                l < length G + (k * length ?B + q)
                  \<longrightarrow>
                fst (nth_default (0, 0) ?B q) +
                    k * d0 \<le>
                  fst (nth_default (0, 0)
                    (copyExp G ?B d0 n) l)) \<and>
              snd (nth_default (0, 0) ?B q) \<le>
                snd (nth_default (0, 0)
                  (copyExp G ?B d0 n) p) + 1)"
        proof (intro allI impI)
          fix k q
          assume kpos: "0 < k"
            and kn: "k < n"
            and qB: "q < length ?B"
            and minimal:
              "\<forall>r. r < q \<longrightarrow>
                fst (nth_default (0, 0) ?B q) \<le>
                  fst (nth_default (0, 0) ?B r)"
            and pos:
              "0 < fst (nth_default (0, 0) ?B q) +
                k * d0"
          show
            "\<exists>p.
              p < length G + (k * length ?B + q) \<and>
              fst (nth_default (0, 0)
                  (copyExp G ?B d0 n) p) + 1 =
                fst (nth_default (0, 0) ?B q) +
                  k * d0 \<and>
              (\<forall>l. p < l \<longrightarrow>
                l < length G + (k * length ?B + q)
                  \<longrightarrow>
                fst (nth_default (0, 0) ?B q) +
                    k * d0 \<le>
                  fst (nth_default (0, 0)
                    (copyExp G ?B d0 n) l)) \<and>
              snd (nth_default (0, 0) ?B q) \<le>
                snd (nth_default (0, 0)
                  (copyExp G ?B d0 n) p) + 1"
          proof (cases "d0 = 0")
            case True
            then have d0: "d0 = 0" .
            show ?thesis
              unfolding d0
            proof (rule r1ok_min_d0zero)
              show "?B = (v0, w0) # R" by simp
              show "\<forall>x\<in>set R. v0 < fst x" by (rule dom)
              show "r1ok (G @ ?B @ [lp])" by (rule hrH)
              show "0 < k" by (rule kpos)
              show "k < n" by (rule kn)
              show "q < length ?B" by (rule qB)
              show
                "\<forall>r. r < q \<longrightarrow>
                  fst (nth_default (0, 0) ?B q) \<le>
                    fst (nth_default (0, 0) ?B r)"
                by (rule minimal)
              show
                "0 < fst (nth_default (0, 0) ?B q) +
                  k * 0"
                using pos d0 by simp
            qed
          next
            case False
            from branches False have d0pos: "0 < d0"
              and wlt: "w0 < snd lp"
              and lp1: "fst lp = v0 + d0"
              and nl1:
                "nextrel1 M (length G) (length M - 1)"
              by auto
            show ?thesis
            proof (rule r1ok_min_d0pos)
              show "?B = (v0, w0) # R" by simp
              show "\<forall>x\<in>set R. v0 < fst x" by (rule dom)
              show "0 < d0" by (rule d0pos)
              show "fst lp = v0 + d0" by (rule lp1)
              show
                "\<forall>r. r + 1 < length ?B \<longrightarrow>
                  fst (nth_default (0, 0) ?B (r + 1)) \<le>
                    fst (nth_default (0, 0) ?B r) + 1"
                by (rule hstep)
              show
                "fst lp \<le>
                  fst (nth_default (0, 0) ?B
                    (length ?B - 1)) + 1"
                by (rule lpstep)
              show
                "\<forall>r'. r' < length ?B \<longrightarrow>
                  fst (nth_default (0, 0) ?B r') =
                    v0 + d0 - 1
                  \<longrightarrow>
                  (\<forall>rr. r' < rr \<longrightarrow>
                    rr < length ?B \<longrightarrow>
                    v0 + d0 \<le>
                      fst (nth_default (0, 0) ?B rr))
                  \<longrightarrow>
                  w0 \<le>
                    snd (nth_default (0, 0) ?B r') + 1"
              proof (intro allI impI)
                fix r'
                assume rB: "r' < length ?B"
                  and lev:
                    "fst (nth_default (0, 0) ?B r') =
                      v0 + d0 - 1"
                  and aft:
                    "\<forall>rr. r' < rr \<longrightarrow>
                      rr < length ?B \<longrightarrow>
                      v0 + d0 \<le>
                        fst (nth_default (0, 0) ?B rr)"
                show
                  "w0 \<le>
                    snd (nth_default (0, 0) ?B r') + 1"
                proof (rule climb_bound)
                  show "M = G @ ?B @ [lp]" by (rule M)
                  show "0 < d0" by (rule d0pos)
                  show "fst lp = v0 + d0" by (rule lp1)
                  show "w0 < snd lp" by (rule wlt)
                  show
                    "nextrel1 M (length G) (length M - 1)"
                    by (rule nl1)
                  show "r' < length ?B" by (rule rB)
                  show
                    "fst (nth_default (0, 0) ?B r') =
                      v0 + d0 - 1"
                    by (rule lev)
                  show
                    "\<forall>rr. r' < rr \<longrightarrow>
                      rr < length ?B \<longrightarrow>
                      v0 + d0 \<le>
                        fst (nth_default (0, 0) ?B rr)"
                    by (rule aft)
                qed
              qed
              show "0 < k" by (rule kpos)
              show "k < n" by (rule kn)
              show "q < length ?B" by (rule qB)
              show
                "\<forall>r. r < q \<longrightarrow>
                  fst (nth_default (0, 0) ?B q) \<le>
                    fst (nth_default (0, 0) ?B r)"
                by (rule minimal)
              show
                "0 < fst (nth_default (0, 0) ?B q) +
                  k * d0"
                by (rule pos)
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma r1ok_ST_PS:
  assumes "ST_PS M"
  shows "r1ok M"
  using assms
proof (induction rule: ST_PS.induct)
  case (diag v)
  show ?case by (rule r1ok_diagSeq)
next
  case (oper M n)
  have st: "steps1 M"
    using blockok_ST_PS[OF oper.hyps(1)]
    unfolding blockok_def by simp
  show ?case
    by (rule r1ok_oper[OF oper.hyps(2) oper.IH st])
qed

lemma nextrel0_bound:
  assumes "nextrel0 M a b"
  shows "b < length M"
  using assms unfolding nextrel0_def by simp

lemma le0_le:
  assumes "le0 M a b"
  shows "a \<le> b"
proof -
  have rt: "(nextrel0 M)\<^sup>*\<^sup>* a b"
    using assms unfolding le0_def by simp
  show ?thesis
    using rt
  proof (induction rule: rtranclp_induct)
    case base
    show ?case by simp
  next
    case (step y z)
    have yz: "y < z"
      by (rule nextrel0_lt[OF step.hyps(2)])
    show ?case using step.IH yz by simp
  qed
qed

definition z0ok :: "pairseq \<Rightarrow> bool" where
  "z0ok M \<longleftrightarrow>
    (\<forall>j. j < length M \<longrightarrow>
      fst (nth_default (0, 0) M j) = 0
        \<longrightarrow>
      snd (nth_default (0, 0) M j) = 0)"

lemma z0ok_diagSeq:
  "z0ok (diagSeq 0 v)"
proof (unfold z0ok_def, intro allI impI)
  fix j
  assume jv: "j < length (diagSeq 0 v)"
    and zero:
      "fst (nth_default (0, 0) (diagSeq 0 v) j) = 0"
  have jv': "j < v + 1"
    using jv diagSeq0_length[of v] by simp
  have at:
    "nth_default (0, 0) (diagSeq 0 v) j = (j, j)"
    by (rule diagSeq0_getD[OF jv'])
  show "snd (nth_default (0, 0) (diagSeq 0 v) j) = 0"
    using zero at by simp
qed

lemma z0ok_take:
  assumes "z0ok M"
  shows "z0ok (take m M)"
proof (unfold z0ok_def, intro allI impI)
  fix j
  assume jt: "j < length (take m M)"
    and zero:
      "fst (nth_default (0, 0) (take m M) j) = 0"
  have jm: "j < m" using jt by simp
  have jM: "j < length M" using jt by simp
  have at:
    "nth_default (0, 0) (take m M) j =
      nth_default (0, 0) M j"
    by (rule getD_take[OF jm])
  have main:
    "\<forall>j. j < length M \<longrightarrow>
      fst (nth_default (0, 0) M j) = 0
        \<longrightarrow>
      snd (nth_default (0, 0) M j) = 0"
    using assms unfolding z0ok_def by simp
  show "snd (nth_default (0, 0) (take m M) j) = 0"
    using main[rule_format, OF jM] zero at by simp
qed

lemma z0ok_Pred:
  assumes "z0ok M"
  shows "z0ok (Pred M)"
  unfolding Pred_def
  using assms z0ok_take[OF assms, of "length M - 1"]
  by (auto simp: butlast_conv_take)

lemma z0ok_copyExp:
  assumes h: "z0ok (G @ B @ [lp])"
  shows "z0ok (copyExp G B d0 n)"
proof (unfold z0ok_def, intro allI impI)
  fix j
  assume jc: "j < length (copyExp G B d0 n)"
    and zero:
      "fst (nth_default (0, 0)
        (copyExp G B d0 n) j) = 0"
  have main:
    "\<forall>j. j < length (G @ B @ [lp]) \<longrightarrow>
      fst (nth_default (0, 0) (G @ B @ [lp]) j) = 0
        \<longrightarrow>
      snd (nth_default (0, 0) (G @ B @ [lp]) j) = 0"
    using h unfolding z0ok_def by simp
  show
    "snd (nth_default (0, 0)
      (copyExp G B d0 n) j) = 0"
  proof (cases "j < length G")
    case True
    have cat:
      "nth_default (0, 0) (copyExp G B d0 n) j =
        nth_default (0, 0) G j"
      by (rule copyExp_getD_pre[OF True])
    have host:
      "nth_default (0, 0) (G @ B @ [lp]) j =
        nth_default (0, 0) G j"
      by (rule hostM_getD_pre[OF True])
    have jH: "j < length (G @ B @ [lp])"
      using True by simp
    show ?thesis
      using main[rule_format, OF jH] zero cat host by simp
  next
    case False
    have Gj: "length G \<le> j" using False by simp
    have total:
      "j < length G + n * length B"
      using jc unfolding copyExp_length by simp
    have diff: "j - length G < n * length B"
      using Gj total
      by (simp add: less_diff_conv2 add.commute)
    have Bpos: "0 < length B"
    proof (rule ccontr)
      assume "\<not> 0 < length B"
      then have "length B = 0" by simp
      with total Gj show False by simp
    qed
    obtain k q where
      kn: "k < n" and qB: "q < length B"
      and dec: "j - length G = k * length B + q"
      by (meson index_decomp[OF Bpos diff])
    have jeq:
      "j = length G + (k * length B + q)"
      using Gj dec by simp
    have cat:
      "nth_default (0, 0) (copyExp G B d0 n) j =
        (fst (nth_default (0, 0) B q) + k * d0,
         snd (nth_default (0, 0) B q))"
    proof -
      have at:
        "nth_default (0, 0) (copyExp G B d0 n)
            (length G + (k * length B + q)) =
          (fst (nth_default (0, 0) B q) + k * d0,
           snd (nth_default (0, 0) B q))"
        by (rule copyExp_getD_copy[OF kn qB])
      show ?thesis using at jeq by simp
    qed
    have basezero:
      "fst (nth_default (0, 0) B q) = 0"
      using zero cat by simp
    have jH:
      "length G + q < length (G @ B @ [lp])"
      using qB by simp
    have host:
      "nth_default (0, 0) (G @ B @ [lp])
          (length G + q) =
        nth_default (0, 0) B q"
      by (rule hostM_getD_blk[OF qB])
    have
      "snd (nth_default (0, 0) B q) = 0"
      using main[rule_format, OF jH] basezero host by simp
    then show ?thesis using cat by simp
  qed
qed

lemma nextrel0_unique:
  assumes h1: "nextrel0 M k1 j"
    and h2: "nextrel0 M k2 j"
  shows "k1 = k2"
proof (cases k1 k2 rule: linorder_cases)
  case less
  have valley:
    "entry M 0 j \<le> entry M 0 k2"
    using h1 h2 less unfolding nextrel0_def by auto
  have strict:
    "entry M 0 k2 < entry M 0 j"
    using h2 unfolding nextrel0_def by simp
  show ?thesis using valley strict by simp
next
  case equal
  show ?thesis by (rule equal)
next
  case greater
  have valley:
    "entry M 0 j \<le> entry M 0 k1"
    using h1 h2 greater unfolding nextrel0_def by auto
  have strict:
    "entry M 0 k1 < entry M 0 j"
    using h1 unfolding nextrel0_def by simp
  show ?thesis using valley strict by simp
qed

lemma nextrel1_unique:
  assumes h1: "nextrel1 M k1 j"
    and h2: "nextrel1 M k2 j"
  shows "k1 = k2"
proof (cases k1 k2 rule: linorder_cases)
  case less
  have maximal:
    "entry M 1 j \<le> entry M 1 k2"
    using h1 h2 less unfolding nextrel1_def by auto
  have strict:
    "entry M 1 k2 < entry M 1 j"
    using h2 unfolding nextrel1_def by simp
  show ?thesis using maximal strict by simp
next
  case equal
  show ?thesis by (rule equal)
next
  case greater
  have maximal:
    "entry M 1 j \<le> entry M 1 k1"
    using h1 h2 greater unfolding nextrel1_def by auto
  have strict:
    "entry M 1 k1 < entry M 1 j"
    using h1 unfolding nextrel1_def by simp
  show ?thesis using maximal strict by simp
qed

lemma blockok_head_zero:
  assumes hb: "blockok 0 M"
    and Mpos: "0 < length M"
  shows "fst (nth_default (0, 0) M 0) = 0"
proof (cases M)
  case Nil
  then show ?thesis using Mpos by simp
next
  case (Cons p R)
  have head:
    "fst (hd (p # R)) = 0"
    using hb Cons unfolding blockok_def by simp
  show ?thesis using head Cons by simp
qed

lemma parent0_exists:
  assumes hb: "blockok 0 M"
    and jM: "j < length M"
    and pos: "0 < entry M 0 j"
  shows "\<exists>k. nextrel0 M k j"
proof -
  have jpos: "0 < j"
  proof (rule ccontr)
    assume "\<not> 0 < j"
    then have j0: "j = 0" by simp
    have Mpos: "0 < length M" using jM by presburger
    have head:
      "fst (nth_default (0, 0) M 0) = 0"
      by (rule blockok_head_zero[OF hb Mpos])
    have e0:
      "entry M 0 0 = fst (nth_default (0, 0) M 0)"
      unfolding entry_def using Mpos
      by (simp add: nth_default_nth)
    show False using pos j0 head e0 by simp
  qed
  let ?Q =
    "\<lambda>k. k \<le> j - 1 \<and>
      entry M 0 k < entry M 0 j"
  let ?k = "Greatest ?Q"
  have Mpos: "0 < length M" using jM by presburger
  have e0:
    "entry M 0 0 = fst (nth_default (0, 0) M 0)"
    unfolding entry_def using Mpos
    by (simp add: nth_default_nth)
  have Q0: "?Q 0"
    using jpos pos e0 blockok_head_zero[OF hb Mpos]
    by simp
  have Qbound: "\<And>x. ?Q x \<Longrightarrow> x \<le> j - 1"
    by simp
  have Qk: "?Q ?k"
  proof (rule GreatestI_nat)
    show "?Q 0" by (rule Q0)
    fix y
    assume "?Q y"
    then show "y \<le> j - 1" by simp
  qed
  have greatest:
    "\<And>x. ?Q x \<Longrightarrow> x \<le> ?k"
  proof -
    fix x
    assume Qx: "?Q x"
    show "x \<le> ?k"
    proof (rule Greatest_le_nat)
      show "?Q x" by (rule Qx)
      fix y
      assume "?Q y"
      then show "y \<le> j - 1" by simp
    qed
  qed
  have kle: "?k \<le> j - 1" using Qk by simp
  have kj: "?k < j" using kle jpos by presburger
  have kM: "?k < length M" using kj jM by simp
  have strict: "entry M 0 ?k < entry M 0 j"
    using Qk by simp
  have valley:
    "\<forall>l. ?k < l \<and> l < j
      \<longrightarrow> entry M 0 j \<le> entry M 0 l"
  proof (intro allI impI)
    fix l
    assume bounds: "?k < l \<and> l < j"
    show "entry M 0 j \<le> entry M 0 l"
    proof (rule ccontr)
      assume "\<not> entry M 0 j \<le> entry M 0 l"
      then have lower:
        "entry M 0 l < entry M 0 j" by simp
      have lj: "l \<le> j - 1"
        using bounds jpos by presburger
      have "?Q l" using lj lower by simp
      then have "l \<le> ?k" by (rule greatest)
      with bounds show False by simp
    qed
  qed
  show ?thesis
  proof (intro exI[of _ ?k])
    show "nextrel0 M ?k j"
      unfolding nextrel0_def
      using kM jM kj strict valley by simp
  qed
qed

lemma chain_to_zero:
  assumes hb: "blockok 0 M"
  shows
    "\<forall>lev j. entry M 0 j = lev \<longrightarrow>
      j < length M \<longrightarrow>
      (\<exists>r. r \<le> j \<and> entry M 0 r = 0 \<and>
        (nextrel0 M)\<^sup>*\<^sup>* r j)"
proof (intro allI impI)
  fix lev j
  assume eq: "entry M 0 j = lev"
    and jM: "j < length M"
  show
    "\<exists>r. r \<le> j \<and> entry M 0 r = 0 \<and>
      (nextrel0 M)\<^sup>*\<^sup>* r j"
    using eq jM
  proof (induction lev arbitrary: j rule: less_induct)
    case (less lev)
    show ?case
    proof (cases "entry M 0 j = 0")
      case True
      show ?thesis
        by (intro exI[of _ j]) (use True in simp)
    next
      case False
      have pos: "0 < entry M 0 j" using False by simp
      obtain k where nk: "nextrel0 M k j"
        using parent0_exists[OF hb less.prems(2) pos]
        by blast
      have kM: "k < length M"
        using nk unfolding nextrel0_def by simp
      have lower:
        "entry M 0 k < lev"
        using nk less.prems(1)
        unfolding nextrel0_def by simp
      obtain r where
        rle: "r \<le> k"
        and rzero: "entry M 0 r = 0"
        and rt: "(nextrel0 M)\<^sup>*\<^sup>* r k"
        using less.IH[OF lower, of k] kM by blast
      have rt':
        "(nextrel0 M)\<^sup>*\<^sup>* r j"
      proof (rule rtranclp.rtrancl_into_rtrancl)
        show "(nextrel0 M)\<^sup>*\<^sup>* r k" by (rule rt)
        show "nextrel0 M k j" by (rule nk)
      qed
      have kj: "k < j"
        using nk unfolding nextrel0_def by simp
      show ?thesis
        by (intro exI[of _ r]) (use rle rzero rt' kj in auto)
    qed
  qed
qed

lemma parent1_exists:
  assumes hb: "blockok 0 M"
    and hz: "z0ok M"
    and jM: "j < length M"
    and pos: "0 < entry M 1 j"
  shows "\<exists>k. nextrel1 M k j"
proof -
  have chain:
    "\<exists>r. r \<le> j \<and> entry M 0 r = 0 \<and>
      (nextrel0 M)\<^sup>*\<^sup>* r j"
  proof (rule chain_to_zero[OF hb, rule_format])
    show "entry M 0 j = entry M 0 j" by simp
    show "j < length M" by (rule jM)
  qed
  obtain r where
    rj: "r \<le> j"
    and rzero: "entry M 0 r = 0"
    and rt: "(nextrel0 M)\<^sup>*\<^sup>* r j"
    using chain by blast
  have rM: "r < length M" using rj jM by simp
  have e0r:
    "entry M 0 r = fst (nth_default (0, 0) M r)"
    unfolding entry_def using rM
    by (simp add: nth_default_nth)
  have e1r:
    "entry M 1 r = snd (nth_default (0, 0) M r)"
    unfolding entry_def using rM
    by (simp add: nth_default_nth)
  have hzmain:
    "\<forall>x. x < length M \<longrightarrow>
      fst (nth_default (0, 0) M x) = 0
        \<longrightarrow>
      snd (nth_default (0, 0) M x) = 0"
    using hz unfolding z0ok_def by simp
  have r1zero: "entry M 1 r = 0"
    using hzmain[rule_format, OF rM] rzero e0r e1r
    by simp
  have rlt: "r < j"
  proof (rule ccontr)
    assume "\<not> r < j"
    then have "r = j" using rj by simp
    with r1zero pos show False by simp
  qed
  let ?Q =
    "\<lambda>k. k \<le> j - 1 \<and> le0 M k j \<and>
      entry M 1 k < entry M 1 j"
  let ?k = "Greatest ?Q"
  have le_rj: "le0 M r j"
    unfolding le0_def using rM jM rt by simp
  have Qr: "?Q r"
    using rlt le_rj r1zero pos by simp
  have Qbound: "\<And>x. ?Q x \<Longrightarrow> x \<le> j - 1"
    by simp
  have Qk: "?Q ?k"
  proof (rule GreatestI_nat)
    show "?Q r" by (rule Qr)
    fix y
    assume "?Q y"
    then show "y \<le> j - 1" by simp
  qed
  have greatest:
    "\<And>x. ?Q x \<Longrightarrow> x \<le> ?k"
  proof -
    fix x
    assume Qx: "?Q x"
    show "x \<le> ?k"
    proof (rule Greatest_le_nat)
      show "?Q x" by (rule Qx)
      fix y
      assume "?Q y"
      then show "y \<le> j - 1" by simp
    qed
  qed
  have kle: "?k \<le> j - 1" using Qk by simp
  have jpos: "0 < j" using rlt by simp
  have kj: "?k < j" using kle jpos by presburger
  have kM: "?k < length M" using kj jM by simp
  have kstrict:
    "entry M 1 ?k < entry M 1 j"
    using Qk by simp
  have kle0: "le0 M ?k j" using Qk by simp
  have maximal:
    "\<forall>j'. ?k < j' \<and> le0 M j' j
      \<longrightarrow> entry M 1 j \<le> entry M 1 j'"
  proof (intro allI impI)
    fix j'
    assume cond: "?k < j' \<and> le0 M j' j"
    have kj': "?k < j'" using cond by simp
    have j'chain: "le0 M j' j" using cond by simp
    show "entry M 1 j \<le> entry M 1 j'"
    proof (cases "j' = j")
      case True
      show ?thesis using True by simp
    next
      case False
      have j'le: "j' \<le> j"
        by (rule le0_le[OF j'chain])
      have j'lt: "j' < j" using j'le False by simp
      show ?thesis
      proof (rule ccontr)
        assume "\<not> entry M 1 j \<le> entry M 1 j'"
        then have strict:
          "entry M 1 j' < entry M 1 j" by simp
        have j'bound: "j' \<le> j - 1"
          using j'lt by simp
        have "?Q j'" using j'bound j'chain strict by simp
        then have "j' \<le> ?k" by (rule greatest)
        with kj' show False by simp
      qed
    qed
  qed
  show ?thesis
  proof (intro exI[of _ ?k])
    show "nextrel1 M ?k j"
      unfolding nextrel1_def
      using kM jM kj kstrict kle0 maximal by simp
  qed
qed

lemma nextR_one_iff:
  "nextR M 1 k j \<longleftrightarrow> nextrel1 M k j"
  unfolding nextR_def by simp

lemma nextR_zero_iff:
  "nextR M 0 k j \<longleftrightarrow> nextrel0 M k j"
  unfolding nextR_def by simp

lemma hp_last:
  assumes hb: "blockok 0 M"
    and hz: "z0ok M"
    and Mpos: "0 < length M"
    and nz:
      "nth_default (0, 0) M (length M - 1) \<noteq> (0, 0)"
  shows
    "hasParent M (idx1 M (length M - 1))
      (length M - 1)"
proof -
  let ?j = "length M - 1"
  have jM: "?j < length M" using Mpos by simp
  have e0:
    "entry M 0 ?j =
      fst (nth_default (0, 0) M ?j)"
    unfolding entry_def using jM
    by (simp add: nth_default_nth)
  have e1:
    "entry M 1 ?j =
      snd (nth_default (0, 0) M ?j)"
    unfolding entry_def using jM
    by (simp add: nth_default_nth)
  show ?thesis
  proof (cases "0 < entry M 1 ?j")
    case True
    have idx: "idx1 M ?j = 1"
      unfolding idx1_def using True by simp
    obtain k where nk: "nextrel1 M k ?j"
      using parent1_exists[OF hb hz jM True] by blast
    show ?thesis
      unfolding hasParent_def
    proof (rule ex1I[of _ k])
      show
        "nextR M (idx1 M ?j) k ?j"
        using nk idx nextR_one_iff by simp
    next
      fix y
      assume ny:
        "nextR M (idx1 M ?j) y ?j"
      have ny': "nextrel1 M y ?j"
        using ny idx nextR_one_iff by simp
      show "y = k"
        by (rule nextrel1_unique[OF ny' nk])
    qed
  next
    case False
    have e1zero: "entry M 1 ?j = 0"
      using False by simp
    have e0pos: "0 < entry M 0 ?j"
    proof (rule ccontr)
      assume "\<not> 0 < entry M 0 ?j"
      then have e0zero: "entry M 0 ?j = 0" by simp
      have fstzero:
        "fst (nth_default (0, 0) M ?j) = 0"
        using e0zero e0 by simp
      have sndzero:
        "snd (nth_default (0, 0) M ?j) = 0"
        using e1zero e1 by simp
      have
        "nth_default (0, 0) M ?j = (0, 0)"
        using fstzero sndzero
        by (cases "nth_default (0, 0) M ?j") simp
      with nz show False by simp
    qed
    have idx: "idx1 M ?j = 0"
      unfolding idx1_def using e1zero by simp
    obtain k where nk: "nextrel0 M k ?j"
      using parent0_exists[OF hb jM e0pos] by blast
    show ?thesis
      unfolding hasParent_def
    proof (rule ex1I[of _ k])
      show
        "nextR M (idx1 M ?j) k ?j"
        using nk idx nextR_zero_iff by simp
    next
      fix y
      assume ny:
        "nextR M (idx1 M ?j) y ?j"
      have ny': "nextrel0 M y ?j"
        using ny idx nextR_zero_iff by simp
      show "y = k"
        by (rule nextrel0_unique[OF ny' nk])
    qed
  qed
qed

lemma z0ok_oper:
  assumes n1: "1 \<le> n"
    and hz0: "z0ok M"
  shows "z0ok (M\<lbrakk>n\<rbrakk>)"
proof (cases "length M - 1 = 0")
  case True
  have eq: "M\<lbrakk>n\<rbrakk> = M"
    by (rule oper_eq_self_of_short[OF True])
  show ?thesis using eq hz0 by simp
next
  case short: False
  show ?thesis
  proof (cases
      "entry M 0 (length M - 1) = 0 \<and>
       entry M 1 (length M - 1) = 0")
    case True
    have eq: "M\<lbrakk>n\<rbrakk> = Pred M"
      by (rule oper_eq_pred_of_zero[OF short True])
    show ?thesis using eq z0ok_Pred[OF hz0] by simp
  next
    case zero: False
    show ?thesis
    proof (cases
        "hasParent M (idx1 M (length M - 1))
          (length M - 1)")
      case False
      have eq: "M\<lbrakk>n\<rbrakk> = Pred M"
        by (rule oper_eq_pred_of_noParent[
              OF short zero False])
      show ?thesis using eq z0ok_Pred[OF hz0] by simp
    next
      case hp: True
      have L: "1 < length M" using short by presburger
      obtain G v0 w0 R d0 lp where
        M:
          "M = G @ ((v0, w0) # R) @ [lp]"
        and X:
          "M\<lbrakk>n\<rbrakk> =
            G @ concat
              (map
                (\<lambda>k.
                  map
                    (\<lambda>p.
                      (fst p + k * d0, snd p))
                    ((v0, w0) # R))
                [0..<n])"
        and dom:
          "\<forall>x\<in>set R. v0 < fst x"
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
        by (rule oper_bad_blocks[OF L zero hp n1])
      have X':
        "M\<lbrakk>n\<rbrakk> =
          copyExp G ((v0, w0) # R) d0 n"
        using X unfolding copyExp_def by simp
      have host:
        "z0ok (G @ ((v0, w0) # R) @ [lp])"
        using hz0 M by simp
      show ?thesis
        using z0ok_copyExp[OF host] X' by simp
    qed
  qed
qed

lemma z0ok_ST_PS:
  assumes "ST_PS M"
  shows "z0ok M"
  using assms
proof (induction rule: ST_PS.induct)
  case (diag v)
  show ?case by (rule z0ok_diagSeq)
next
  case (oper M n)
  show ?case
    by (rule z0ok_oper[OF oper.hyps(2) oper.IH])
qed

lemma rtg_through_pivot:
  assumes rt: "(nextrel0 M)\<^sup>*\<^sup>* a b"
    and ar: "a < rho"
    and rb: "rho \<le> b"
    and floor:
      "\<forall>y. rho < y \<longrightarrow> y \<le> b \<longrightarrow>
        entry M 0 rho < entry M 0 y"
  shows "(nextrel0 M)\<^sup>*\<^sup>* rho b"
  using rt ar rb floor
proof (induction arbitrary: rho rule: rtranclp_induct)
  case base
  have "a < a" using base.prems(1) base.prems(2)
    by simp
  then show ?case by simp
next
  case (step y z)
  have yz: "y < z"
    by (rule nextrel0_lt[OF step.hyps(2)])
  show ?case
  proof (cases "rho \<le> y")
    case True
    have floor_y:
      "\<forall>u. rho < u \<longrightarrow> u \<le> y \<longrightarrow>
        entry M 0 rho < entry M 0 u"
    proof (intro allI impI)
      fix u
      assume ru: "rho < u" and uy: "u \<le> y"
      have uz: "u \<le> z" using uy yz by simp
      show "entry M 0 rho < entry M 0 u"
        by (rule step.prems(3)[rule_format, OF ru uz])
    qed
    have ih: "(nextrel0 M)\<^sup>*\<^sup>* rho y"
      by (rule step.IH[OF step.prems(1) True floor_y])
    show ?thesis
    proof (rule rtranclp.rtrancl_into_rtrancl)
      show "(nextrel0 M)\<^sup>*\<^sup>* rho y" by (rule ih)
      show "nextrel0 M y z" by (rule step.hyps(2))
    qed
  next
    case False
    have yr: "y < rho" using False by simp
    show ?thesis
    proof (cases "rho = z")
      case True
      show ?thesis using True by simp
    next
      case neq: False
      have rz: "rho < z"
        using step.prems(2) neq by simp
      have valley:
        "entry M 0 z \<le> entry M 0 rho"
      proof -
        have all:
          "\<forall>u. y < u \<and> u < z
            \<longrightarrow> entry M 0 z \<le> entry M 0 u"
          using step.hyps(2) unfolding nextrel0_def by simp
        show ?thesis
          by (rule all[rule_format]) (use yr rz in simp)
      qed
      have strict:
        "entry M 0 rho < entry M 0 z"
        by (rule step.prems(3)[rule_format,
              OF rz order_refl])
      show ?thesis using valley strict by simp
    qed
  qed
qed

lemma le0_through_pivot:
  assumes h: "le0 M a b"
    and ar: "a < rho"
    and rb: "rho \<le> b"
    and floor:
      "\<forall>y. rho < y \<longrightarrow> y \<le> b \<longrightarrow>
        entry M 0 rho < entry M 0 y"
  shows "le0 M rho b"
proof -
  have bM: "b < length M"
    and rt: "(nextrel0 M)\<^sup>*\<^sup>* a b"
    using h unfolding le0_def by auto
  have rM: "rho < length M" using rb bM by simp
  have rt': "(nextrel0 M)\<^sup>*\<^sup>* rho b"
    by (rule rtg_through_pivot[OF rt ar rb floor])
  show ?thesis
    unfolding le0_def using rM bM rt' by simp
qed

lemma entry_shift:
  assumes "j < length S"
  shows
    "entry (map (\<lambda>p. (fst p + d, snd p)) S) 0 j =
        entry S 0 j + d \<and>
     entry (map (\<lambda>p. (fst p + d, snd p)) S) 1 j =
        entry S 1 j"
  using assms
  by (simp add: entry_def)

lemma nextrel0_shift_iff:
  assumes bS: "b < length S"
  shows
    "nextrel0 (map (\<lambda>p. (fst p + d, snd p)) S) a b
      \<longleftrightarrow> nextrel0 S a b"
proof -
  let ?T = "map (\<lambda>p. (fst p + d, snd p)) S"
  show ?thesis
  proof
    assume h: "nextrel0 ?T a b"
    have aS: "a < length S"
      and ab: "a < b"
      and strictT: "entry ?T 0 a < entry ?T 0 b"
      and valleyT:
        "\<forall>l. a < l \<and> l < b
          \<longrightarrow> entry ?T 0 b \<le> entry ?T 0 l"
      using h unfolding nextrel0_def by auto
    have ea:
      "entry ?T 0 a = entry S 0 a + d"
      using entry_shift[OF aS, of d] by simp
    have eb:
      "entry ?T 0 b = entry S 0 b + d"
      using entry_shift[OF bS, of d] by simp
    have strict: "entry S 0 a < entry S 0 b"
      using strictT ea eb by simp
    have valley:
      "\<forall>l. a < l \<and> l < b
        \<longrightarrow> entry S 0 b \<le> entry S 0 l"
    proof (intro allI impI)
      fix l
      assume bounds: "a < l \<and> l < b"
      have lS: "l < length S" using bounds bS by simp
      have el:
        "entry ?T 0 l = entry S 0 l + d"
        using entry_shift[OF lS, of d] by simp
      have "entry ?T 0 b \<le> entry ?T 0 l"
        by (rule valleyT[rule_format, OF bounds])
      then show "entry S 0 b \<le> entry S 0 l"
        using eb el by simp
    qed
    show "nextrel0 S a b"
      unfolding nextrel0_def
      using aS bS ab strict valley by simp
  next
    assume h: "nextrel0 S a b"
    have aS: "a < length S"
      and ab: "a < b"
      and strict: "entry S 0 a < entry S 0 b"
      and valley:
        "\<forall>l. a < l \<and> l < b
          \<longrightarrow> entry S 0 b \<le> entry S 0 l"
      using h unfolding nextrel0_def by auto
    have ea:
      "entry ?T 0 a = entry S 0 a + d"
      using entry_shift[OF aS, of d] by simp
    have eb:
      "entry ?T 0 b = entry S 0 b + d"
      using entry_shift[OF bS, of d] by simp
    have strictT: "entry ?T 0 a < entry ?T 0 b"
      using strict ea eb by simp
    have valleyT:
      "\<forall>l. a < l \<and> l < b
        \<longrightarrow> entry ?T 0 b \<le> entry ?T 0 l"
    proof (intro allI impI)
      fix l
      assume bounds: "a < l \<and> l < b"
      have lS: "l < length S" using bounds bS by simp
      have el:
        "entry ?T 0 l = entry S 0 l + d"
        using entry_shift[OF lS, of d] by simp
      have "entry S 0 b \<le> entry S 0 l"
        by (rule valley[rule_format, OF bounds])
      then show "entry ?T 0 b \<le> entry ?T 0 l"
        using eb el by simp
    qed
    show "nextrel0 ?T a b"
      unfolding nextrel0_def
      using aS bS ab strictT valleyT by simp
  qed
qed

lemma rtg_shift_of:
  assumes
    "(nextrel0
      (map (\<lambda>p. (fst p + d, snd p)) S))\<^sup>*\<^sup>* a b"
  shows "(nextrel0 S)\<^sup>*\<^sup>* a b"
  using assms
proof (induction rule: rtranclp_induct)
  case base
  show ?case by simp
next
  case (step y z)
  have zS: "z < length S"
    using nextrel0_bound[OF step.hyps(2)] by simp
  have edge: "nextrel0 S y z"
    using step.hyps(2)
      nextrel0_shift_iff[OF zS, of d y]
    by simp
  show ?case
  proof (rule rtranclp.rtrancl_into_rtrancl)
    show "(nextrel0 S)\<^sup>*\<^sup>* a y" by (rule step.IH)
    show "nextrel0 S y z" by (rule edge)
  qed
qed

lemma rtg_shift_to:
  assumes "(nextrel0 S)\<^sup>*\<^sup>* a b"
  shows
    "(nextrel0
      (map (\<lambda>p. (fst p + d, snd p)) S))\<^sup>*\<^sup>* a b"
  using assms
proof (induction rule: rtranclp_induct)
  case base
  show ?case by simp
next
  case (step y z)
  have zS: "z < length S"
    by (rule nextrel0_bound[OF step.hyps(2)])
  have edge:
    "nextrel0 (map (\<lambda>p. (fst p + d, snd p)) S) y z"
    using step.hyps(2)
      nextrel0_shift_iff[OF zS, of d y]
    by simp
  show ?case
  proof (rule rtranclp.rtrancl_into_rtrancl)
    show
      "(nextrel0
        (map (\<lambda>p. (fst p + d, snd p)) S))\<^sup>*\<^sup>*
          a y"
      by (rule step.IH)
    show
      "nextrel0
        (map (\<lambda>p. (fst p + d, snd p)) S) y z"
      by (rule edge)
  qed
qed

lemma le0_shift_iff:
  "le0 (map (\<lambda>p. (fst p + d, snd p)) S) a b
    \<longleftrightarrow> le0 S a b"
proof
  assume h:
    "le0 (map (\<lambda>p. (fst p + d, snd p)) S) a b"
  have aS: "a < length S"
    and bS: "b < length S"
    and rt:
      "(nextrel0
        (map (\<lambda>p. (fst p + d, snd p)) S))\<^sup>*\<^sup>* a b"
    using h unfolding le0_def by auto
  have rt': "(nextrel0 S)\<^sup>*\<^sup>* a b"
    by (rule rtg_shift_of[OF rt])
  show "le0 S a b"
    unfolding le0_def using aS bS rt' by simp
next
  assume h: "le0 S a b"
  have aS: "a < length S"
    and bS: "b < length S"
    and rt: "(nextrel0 S)\<^sup>*\<^sup>* a b"
    using h unfolding le0_def by auto
  have rt':
    "(nextrel0
      (map (\<lambda>p. (fst p + d, snd p)) S))\<^sup>*\<^sup>* a b"
    by (rule rtg_shift_to[OF rt])
  show
    "le0 (map (\<lambda>p. (fst p + d, snd p)) S) a b"
    unfolding le0_def using aS bS rt' by simp
qed

lemma idx1_shift:
  "idx1 (map (\<lambda>p. (fst p + d, snd p)) S) j =
    idx1 S j"
proof (cases "j < length S")
  case True
  have row1:
    "entry (map (\<lambda>p. (fst p + d, snd p)) S) 1 j =
      entry S 1 j"
    using entry_shift[OF True, of d] by simp
  show ?thesis unfolding idx1_def using row1 by simp
next
  case False
  have eS: "entry S 1 j = 0"
    unfolding entry_def using False by simp
  have eT:
    "entry (map (\<lambda>p. (fst p + d, snd p)) S) 1 j = 0"
    unfolding entry_def using False by simp
  show ?thesis unfolding idx1_def using eS eT by simp
qed

lemma nextrel1_shift_iff:
  assumes bS: "b < length S"
  shows
    "nextrel1 (map (\<lambda>p. (fst p + d, snd p)) S) a b
      \<longleftrightarrow> nextrel1 S a b"
proof -
  let ?T = "map (\<lambda>p. (fst p + d, snd p)) S"
  have b1: "entry ?T 1 b = entry S 1 b"
    using entry_shift[OF bS, of d] by simp
  show ?thesis
  proof
    assume h: "nextrel1 ?T a b"
    have aS: "a < length S"
      and ab: "a < b"
      and strictT: "entry ?T 1 a < entry ?T 1 b"
      and chainT: "le0 ?T a b"
      and maximalT:
        "\<forall>l. a < l \<and> le0 ?T l b
          \<longrightarrow> entry ?T 1 b \<le> entry ?T 1 l"
      using h unfolding nextrel1_def by auto
    have a1: "entry ?T 1 a = entry S 1 a"
      using entry_shift[OF aS, of d] by simp
    have chain: "le0 S a b"
      using chainT by (simp only: le0_shift_iff)
    have maximal:
      "\<forall>l. a < l \<and> le0 S l b
        \<longrightarrow> entry S 1 b \<le> entry S 1 l"
    proof (intro allI impI)
      fix l
      assume cond: "a < l \<and> le0 S l b"
      have chainl: "le0 S l b" using cond by simp
      have lb: "l \<le> b"
      proof (rule le0_le)
        show "le0 S l b" by (rule chainl)
      qed
      have lS: "l < length S" using lb bS by simp
      have l1: "entry ?T 1 l = entry S 1 l"
        using entry_shift[OF lS, of d] by simp
      have chainT': "le0 ?T l b"
        using cond by (simp only: le0_shift_iff)
      have "entry ?T 1 b \<le> entry ?T 1 l"
        by (rule maximalT[rule_format])
           (use cond chainT' in simp)
      then show "entry S 1 b \<le> entry S 1 l"
        using b1 l1 by simp
    qed
    show "nextrel1 S a b"
      unfolding nextrel1_def
      using aS bS ab strictT a1 b1 chain maximal
      by simp
  next
    assume h: "nextrel1 S a b"
    have aS: "a < length S"
      and ab: "a < b"
      and strict: "entry S 1 a < entry S 1 b"
      and chain: "le0 S a b"
      and maximal:
        "\<forall>l. a < l \<and> le0 S l b
          \<longrightarrow> entry S 1 b \<le> entry S 1 l"
      using h unfolding nextrel1_def by auto
    have a1: "entry ?T 1 a = entry S 1 a"
      using entry_shift[OF aS, of d] by simp
    have chainT: "le0 ?T a b"
      using chain by (simp only: le0_shift_iff)
    have maximalT:
      "\<forall>l. a < l \<and> le0 ?T l b
        \<longrightarrow> entry ?T 1 b \<le> entry ?T 1 l"
    proof (intro allI impI)
      fix l
      assume cond: "a < l \<and> le0 ?T l b"
      have chainl: "le0 S l b"
        using cond by (simp only: le0_shift_iff)
      have lb: "l \<le> b" by (rule le0_le[OF chainl])
      have lS: "l < length S" using lb bS by simp
      have l1: "entry ?T 1 l = entry S 1 l"
        using entry_shift[OF lS, of d] by simp
      have "entry S 1 b \<le> entry S 1 l"
        by (rule maximal[rule_format])
           (use cond chainl in simp)
      then show "entry ?T 1 b \<le> entry ?T 1 l"
        using b1 l1 by simp
    qed
    show "nextrel1 ?T a b"
      unfolding nextrel1_def
      using aS bS ab strict a1 b1 chainT maximalT
      by simp
  qed
qed

end
