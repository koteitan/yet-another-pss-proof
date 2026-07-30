theory Wset
  imports ArgDom
begin

lemma translate_eq_Z_iff:
  "translate M = Z \<longleftrightarrow> M = []"
  by (cases M) simp_all

lemma eq_Z_of_olt_one:
  assumes h: "t <o P 0 Z Z"
  shows "t = Z"
  using h by (cases t) auto

lemma stps_ne_nil:
  assumes hM: "ST_PS M"
  shows "M \<noteq> []"
proof
  assume "M = []"
  then show False
    using stps_len_pos[OF hM] by simp
qed

lemma stps_len_one:
  assumes hM: "ST_PS M"
    and len: "length M = 1"
  shows "M = [(0, 0)]"
proof -
  obtain p where M: "M = [p]"
    using len by (cases M) auto
  have head:
    "hd M = (0, 0)"
    by (rule stps_head[OF hM])
  show ?thesis using M head by simp
qed

definition domT ::
  "pairseq \<Rightarrow> nat \<Rightarrow> bool"
where
  "domT M m \<longleftrightarrow>
    entry M 1 (length M - 1) = m + 1 \<and>
    \<not> hasParent M 1 (length M - 1)"

definition graft ::
  "pairseq \<Rightarrow> pairseq \<Rightarrow> pairseq"
where
  "graft M z =
    butlast M @
      map
        (\<lambda>p.
          (fst p +
            entry M 0 (length M - 1),
           snd p))
        z"

definition based :: "pairseq \<Rightarrow> bool" where
  "based z \<longleftrightarrow> entry z 0 0 = 0"

lemma based_nil [simp]:
  "based []"
  unfolding based_def entry_def by simp

lemma graft_nil [simp]:
  "graft M [] = butlast M"
  unfolding graft_def by simp

lemma not_domT_nil:
  "\<not> domT [] m"
  unfolding domT_def entry_def by simp

definition natDom :: "pairseq \<Rightarrow> bool" where
  "natDom M \<longleftrightarrow> (\<forall>m. \<not> domT M m)"

lemma natDom_iff:
  "natDom M \<longleftrightarrow>
    entry M 1 (length M - 1) = 0 \<or>
    hasParent M 1 (length M - 1)"
proof
  assume h: "natDom M"
  show
    "entry M 1 (length M - 1) = 0 \<or>
      hasParent M 1 (length M - 1)"
  proof (cases
    "entry M 1 (length M - 1) = 0")
    case True
    then show ?thesis by simp
  next
    case False
    show ?thesis
    proof (rule disjI2, rule ccontr)
      assume hp:
        "\<not> hasParent M 1 (length M - 1)"
      let ?e = "entry M 1 (length M - 1)"
      have eq: "?e = (?e - 1) + 1"
        using False by presburger
      have "domT M (?e - 1)"
        unfolding domT_def
        using eq hp by simp
      moreover have "\<not> domT M (?e - 1)"
        using h unfolding natDom_def by blast
      ultimately show False by simp
    qed
  qed
next
  assume h:
    "entry M 1 (length M - 1) = 0 \<or>
      hasParent M 1 (length M - 1)"
  show "natDom M"
    unfolding natDom_def
  proof (intro allI notI)
    fix m
    assume d: "domT M m"
    have val:
      "entry M 1 (length M - 1) = m + 1"
      and np:
      "\<not> hasParent M 1 (length M - 1)"
      using d unfolding domT_def by blast+
    from h show False
    proof
      assume
        "entry M 1 (length M - 1) = 0"
      then show False using val by simp
    next
      assume
        "hasParent M 1 (length M - 1)"
      then show False using np by simp
    qed
  qed
qed

lemma oper_eq_graft_nil_of_domT:
  assumes L: "1 < length M"
    and d: "domT M m"
  shows "M\<lbrakk>n\<rbrakk> = graft M []"
proof -
  have val:
    "entry M 1 (length M - 1) = m + 1"
    and hp:
    "\<not> hasParent M 1 (length M - 1)"
    using d unfolding domT_def by blast+
  have short: "length M - 1 \<noteq> 0"
    using L by presburger
  have pos:
    "0 < entry M 1 (length M - 1)"
    using val by simp
  have idx:
    "idx1 M (length M - 1) = 1"
    unfolding idx1_def using pos by simp
  have nz:
    "\<not>
      (entry M 0 (length M - 1) = 0 \<and>
       entry M 1 (length M - 1) = 0)"
    using pos by auto
  have op: "M\<lbrakk>n\<rbrakk> = Pred M"
    by (rule oper_eq_pred_of_noParent[
          OF short nz])
       (use hp idx in simp)
  show ?thesis
    using op L
    unfolding Pred_def by simp
qed

definition r1cand ::
  "pairseq \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "r1cand M j1 j0 \<longleftrightarrow>
    j0 < j1 \<and>
    le0 M j0 j1 \<and>
    entry M 1 j0 < entry M 1 j1"

lemma hasParent_one_iff:
  assumes j1: "j1 < length M"
  shows
    "hasParent M 1 j1 \<longleftrightarrow>
      (\<exists>j0. r1cand M j1 j0)"
proof
  assume h: "hasParent M 1 j1"
  then obtain j0 where nr:
      "nextR M 1 j0 j1"
    and unique:
      "\<forall>y. nextR M 1 y j1 \<longrightarrow> y = j0"
    unfolding hasParent_def by blast
  have n1: "nextrel1 M j0 j1"
    using nr unfolding nextR_def by simp
  show "\<exists>j0. r1cand M j1 j0"
    unfolding r1cand_def
    using n1 unfolding nextrel1_def by blast
next
  assume ex: "\<exists>j0. r1cand M j1 j0"
  let ?C = "{k. r1cand M j1 k}"
  obtain j0 where j0C: "j0 \<in> ?C"
    using ex by blast
  have finite: "finite ?C"
  proof (rule finite_subset[
      of ?C "{..<j1}"])
    show "finite {..<j1}" by simp
    show "?C \<subseteq> {..<j1}"
      unfolding r1cand_def by auto
  qed
  let ?k = "Max ?C"
  have Cne: "?C \<noteq> {}"
    using j0C by auto
  have kC: "?k \<in> ?C"
    by (rule Max_in[OF finite Cne])
  have kmax:
    "\<forall>q\<in>?C. q \<le> ?k"
    by (intro ballI)
       (rule Max_ge[OF finite])
  have kc:
      "?k < j1"
    and kle: "le0 M ?k j1"
    and krow:
      "entry M 1 ?k < entry M 1 j1"
    using kC unfolding r1cand_def by blast+
  have n1: "nextrel1 M ?k j1"
    unfolding nextrel1_def
  proof (intro conjI)
    show "?k < length M"
      using kc j1 by simp
    show "j1 < length M" by (rule j1)
    show "?k < j1" by (rule kc)
    show "entry M 1 ?k < entry M 1 j1"
      by (rule krow)
    show "le0 M ?k j1" by (rule kle)
    show
      "\<forall>j. ?k < j \<and> le0 M j j1
        \<longrightarrow>
        entry M 1 j1 \<le> entry M 1 j"
    proof (intro allI impI)
      fix j
      assume cond:
        "?k < j \<and> le0 M j j1"
      show "entry M 1 j1 \<le> entry M 1 j"
      proof (rule ccontr)
        assume notle:
          "\<not>
            entry M 1 j1 \<le> entry M 1 j"
        have row:
          "entry M 1 j < entry M 1 j1"
          using notle by simp
        have jj1: "j < j1"
        proof -
          have le:
            "j \<le> j1"
            using cond
            unfolding le0_def
            by (auto dest:
              nextrel0_rtrancl_index_le)
          show ?thesis
          proof (cases "j = j1")
            case True
            then show ?thesis using row by simp
          next
            case False
            then show ?thesis using le by simp
          qed
        qed
        have "j \<in> ?C"
          unfolding r1cand_def
          using cond jj1 row by simp
        then have "j \<le> ?k"
          by (rule kmax[rule_format])
        then show False using cond by simp
      qed
    qed
  qed
  have nr: "nextR M 1 ?k j1"
    using n1 unfolding nextR_def by simp
  show "hasParent M 1 j1"
    unfolding hasParent_def
  proof (intro ex1I[of _ ?k])
    show "nextR M 1 ?k j1" by (rule nr)
    fix y
    assume ynr: "nextR M 1 y j1"
    have yn1: "nextrel1 M y j1"
      using ynr unfolding nextR_def by simp
    show "y = ?k"
      by (rule nextrel1_unique[
            OF yn1 n1])
  qed
qed

lemma domT_iff:
  assumes ne: "M \<noteq> []"
  shows
    "domT M m \<longleftrightarrow>
      (entry M 1 (length M - 1) = m + 1 \<and>
       (\<forall>j0.
        j0 < length M - 1 \<longrightarrow>
        le0 M j0 (length M - 1) \<longrightarrow>
        m + 1 \<le> entry M 1 j0))"
proof -
  have last:
    "length M - 1 < length M"
    using ne by (cases M) simp_all
  show ?thesis
    unfolding domT_def
    unfolding hasParent_one_iff[OF last]
    unfolding r1cand_def
    by (auto simp: linorder_not_less)
qed

definition lfpS ::
  "(pairseq set \<Rightarrow> pairseq set) \<Rightarrow>
    pairseq set"
where
  "lfpS f = \<Inter>{Y. f Y \<subseteq> Y}"

lemma lfpS_eq_lfp:
  "lfpS f = lfp f"
  by (simp add: lfpS_def lfp_def)

lemma lfpS_lowerbound:
  assumes h: "f Y \<subseteq> Y"
  shows "lfpS f \<subseteq> Y"
  using lfp_lowerbound[
    where f=f and A=Y, OF h]
  by (simp add: lfpS_eq_lfp)

lemma lfpS_unfold_le:
  assumes mono: "mono f"
  shows "f (lfpS f) \<subseteq> lfpS f"
  using lfp_fixpoint[OF mono]
  by (simp add: lfpS_eq_lfp)

lemma lfpS_unfold_ge:
  assumes mono: "mono f"
  shows "lfpS f \<subseteq> f (lfpS f)"
  using lfp_fixpoint[OF mono]
  by (simp add: lfpS_eq_lfp)

lemma lfpS_unfold:
  assumes mono: "mono f"
  shows "f (lfpS f) = lfpS f"
  using lfp_fixpoint[OF mono]
  by (simp add: lfpS_eq_lfp)

definition Aop ::
  "(nat \<Rightarrow> pairseq set) \<Rightarrow>
   nat \<Rightarrow> pairseq set \<Rightarrow>
   pairseq \<Rightarrow> bool"
where
  "Aop Wfam u X M \<longleftrightarrow>
    (length M \<le> 1 \<and> entry M 1 0 = 0) \<or>
    (natDom M \<and>
      (\<forall>n. 1 \<le> n \<longrightarrow> M\<lbrakk>n\<rbrakk> \<in> X)) \<or>
    (\<exists>m<u.
      domT M m \<and>
      (\<forall>z\<in>Wfam m.
        based z \<longrightarrow> graft M z \<in> X))"

definition Aset ::
  "(nat \<Rightarrow> pairseq set) \<Rightarrow>
   nat \<Rightarrow> pairseq set \<Rightarrow>
   pairseq set"
where
  "Aset Wfam u X = {M. Aop Wfam u X M}"

lemma Aop_mono_X:
  assumes h: "Aop Wfam u X M"
    and XY: "X \<subseteq> Y"
  shows "Aop Wfam u Y M"
  using h
  unfolding Aop_def
  by (elim disjE exE conjE)
     (auto intro: XY[THEN subsetD])

lemma Aset_mono:
  "mono (Aset Wfam u)"
  unfolding mono_def Aset_def
  using Aop_mono_X by blast

lemma Aop_mono_level:
  assumes uv: "u \<le> v"
    and h: "Aop Wfam u X M"
  shows "Aop Wfam v X M"
  unfolding Aop_def
proof -
  have cases:
    "(length M \<le> 1 \<and> entry M 1 0 = 0) \<or>
     (natDom M \<and>
       (\<forall>n. 1 \<le> n \<longrightarrow> M\<lbrakk>n\<rbrakk> \<in> X)) \<or>
     (\<exists>m<u.
       domT M m \<and>
       (\<forall>z\<in>Wfam m.
         based z \<longrightarrow> graft M z \<in> X))"
    using h unfolding Aop_def .
  from cases show
    "(length M \<le> 1 \<and> entry M 1 0 = 0) \<or>
     (natDom M \<and>
       (\<forall>n. 1 \<le> n \<longrightarrow> M\<lbrakk>n\<rbrakk> \<in> X)) \<or>
     (\<exists>m<v.
       domT M m \<and>
       (\<forall>z\<in>Wfam m.
         based z \<longrightarrow> graft M z \<in> X))"
  proof
    assume base:
      "length M \<le> 1 \<and> entry M 1 0 = 0"
    then show ?thesis by simp
  next
    assume rest:
      "(natDom M \<and>
        (\<forall>n. 1 \<le> n \<longrightarrow> M\<lbrakk>n\<rbrakk> \<in> X)) \<or>
       (\<exists>m<u.
        domT M m \<and>
        (\<forall>z\<in>Wfam m.
          based z \<longrightarrow> graft M z \<in> X))"
    from rest show ?thesis
    proof
      assume nat:
        "natDom M \<and>
          (\<forall>n. 1 \<le> n \<longrightarrow> M\<lbrakk>n\<rbrakk> \<in> X)"
      then show ?thesis by simp
    next
      assume graft:
        "\<exists>m<u.
          domT M m \<and>
          (\<forall>z\<in>Wfam m.
            based z \<longrightarrow> graft M z \<in> X)"
      then obtain m where mu: "m < u"
        and rest:
          "domT M m \<and>
           (\<forall>z\<in>Wfam m.
             based z \<longrightarrow> graft M z \<in> X)"
        by blast
      have mv: "m < v"
        using mu uv by (rule less_le_trans)
      show ?thesis using mv rest by blast
    qed
  qed
qed

lemma Aop_cong:
  assumes e:
    "\<forall>m<u. Wfam m = Wgam m"
  shows
    "Aop Wfam u X M \<longleftrightarrow>
      Aop Wgam u X M"
  using e unfolding Aop_def
  by auto

fun Wf :: "nat \<Rightarrow> nat \<Rightarrow> pairseq set" where
  "Wf 0 m = {}"
| "Wf (Suc v) m =
    (if m = v
     then lfpS (Aset (Wf v) v)
     else Wf v m)"

definition W :: "nat \<Rightarrow> pairseq set" where
  "W u = Wf (u + 1) u"

lemma Wf_coh:
  assumes h: "m < n"
  shows "Wf n m = Wf (m + 1) m"
  using h
proof (induction n arbitrary: m)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "m = n")
    case True
    then show ?thesis by simp
  next
    case False
    have mn: "m < n"
      using Suc.prems False by presburger
    show ?thesis
      using Suc.IH[OF mn] False by simp
  qed
qed

lemma Wf_eq_W:
  assumes "m < n"
  shows "Wf n m = W m"
  using Wf_coh[OF assms]
  unfolding W_def by simp

lemma W_unfold:
  "W u = lfpS (Aset W u)"
proof -
  have stage:
    "W u = lfpS (Aset (Wf u) u)"
    unfolding W_def by simp
  have fam:
    "\<forall>m<u. Wf u m = W m"
    by (intro allI impI)
       (rule Wf_eq_W)
  have aset:
    "\<forall>X. Aset (Wf u) u X = Aset W u X"
  proof
    fix X
    show "Aset (Wf u) u X = Aset W u X"
      unfolding Aset_def
      by (rule Collect_cong)
         (rule Aop_cong[OF fam])
  qed
  have funeq:
    "Aset (Wf u) u = Aset W u"
    by (rule ext)
       (rule aset[rule_format])
  show ?thesis using stage funeq by simp
qed

lemma A1:
  "Aset W u (W u) = W u"
  unfolding W_unfold[of u]
  by (rule lfpS_unfold[OF Aset_mono])

lemma A2:
  assumes h: "Aset W u Y \<subseteq> Y"
  shows "W u \<subseteq> Y"
  unfolding W_unfold[of u]
  by (rule lfpS_lowerbound[
        where f="Aset W u" and Y=Y,
        OF h])

lemma A2':
  assumes h:
    "\<forall>M. Aop W u Y M \<longrightarrow> M \<in> Y"
  shows "W u \<subseteq> Y"
proof (rule A2)
  show "Aset W u Y \<subseteq> Y"
    unfolding Aset_def
    by (intro subsetI)
       (rule h[rule_format], simp)
qed

lemma A1_intro:
  assumes h: "Aop W u (W u) M"
  shows "M \<in> W u"
proof -
  have "M \<in> Aset W u (W u)"
    using h unfolding Aset_def by simp
  then show ?thesis using A1[of u] by simp
qed

lemma W_nil:
  "[] \<in> W u"
  by (rule A1_intro)
     (simp add: Aop_def entry_def)

lemma W_mono:
  assumes uv: "u \<le> v"
  shows "W u \<subseteq> W v"
  by (rule A2')
     (metis A1_intro Aop_mono_level uv)

definition Rst :: "pairseq \<Rightarrow> pairseq \<Rightarrow> bool" where
  "Rst a b \<longleftrightarrow>
    ST_PS a \<and> ST_PS b \<and>
    translate a <o translate b"

lemma acc_of_translate_eq:
  assumes ast: "ST_PS a"
    and eq: "translate b = translate a"
    and acc: "Wellfounded.accp Rst a"
  shows "Wellfounded.accp Rst b"
proof (rule accp.accI)
  fix y
  assume yb: "Rst y b"
  have ya: "Rst y a"
    using yb ast eq unfolding Rst_def by simp
  show "Wellfounded.accp Rst y"
    by (rule accp_downward[OF acc ya])
qed

lemma acc_of_nat_branch:
  assumes cof:
    "\<And>M N.
      ST_PS M \<Longrightarrow> ST_PS N \<Longrightarrow>
      translate N <o translate M \<Longrightarrow>
      \<exists>n. 1 \<le> n \<and>
        translate N \<le>o translate (M\<lbrakk>n\<rbrakk>)"
    and cst: "ST_PS c"
    and branches:
      "\<And>n. 1 \<le> n \<Longrightarrow>
        Wellfounded.accp Rst (c\<lbrakk>n\<rbrakk>)"
  shows "Wellfounded.accp Rst c"
proof (rule accp.accI)
  fix b
  assume bc: "Rst b c"
  have bst: "ST_PS b"
    and lt: "translate b <o translate c"
    using bc unfolding Rst_def by blast+
  obtain n where n1: "1 \<le> n"
    and le:
      "translate b \<le>o
        translate (c\<lbrakk>n\<rbrakk>)"
    using cof[OF cst bst lt] by blast
  have acc:
    "Wellfounded.accp Rst (c\<lbrakk>n\<rbrakk>)"
    by (rule branches[OF n1])
  have opst: "ST_PS (c\<lbrakk>n\<rbrakk>)"
    by (rule ST_PS.oper[OF cst n1])
  have le_cases:
    "translate b <o translate (c\<lbrakk>n\<rbrakk>) \<or>
     translate b = translate (c\<lbrakk>n\<rbrakk>)"
    using le unfolding ole_def .
  show "Wellfounded.accp Rst b"
  using le_cases
  proof
    assume lt':
      "translate b <o translate (c\<lbrakk>n\<rbrakk>)"
    have rel: "Rst b (c\<lbrakk>n\<rbrakk>)"
      using bst opst lt' unfolding Rst_def by simp
    show ?thesis
      by (rule accp_downward[OF acc rel])
  next
    assume eq':
      "translate b = translate (c\<lbrakk>n\<rbrakk>)"
    show ?thesis
      by (rule acc_of_translate_eq[
            OF opst eq' acc])
  qed
qed

lemma acc_of_not_ST_PS:
  assumes notst: "\<not> ST_PS c"
  shows "Wellfounded.accp Rst c"
proof (rule accp.accI)
  fix y
  assume yc: "Rst y c"
  have cst: "ST_PS c"
    using yc unfolding Rst_def by blast
  show "Wellfounded.accp Rst y"
    using notst cst by simp
qed

lemma acc_of_Aop_base:
  assumes cst: "ST_PS c"
    and base:
      "length c \<le> 1 \<and> entry c 1 0 = 0"
  shows "Wellfounded.accp Rst c"
proof (rule accp.accI)
  fix y
  assume yc: "Rst y c"
  have len: "length c = 1"
    using stps_len_pos[OF cst] base
    by presburger
  have c0: "c = [(0, 0)]"
    by (rule stps_len_one[OF cst len])
  have yst: "ST_PS y"
    and ylt: "translate y <o translate c"
    using yc unfolding Rst_def by blast+
  have trc: "translate c = P 0 Z Z"
    using c0 by simp
  have "translate y = Z"
    by (rule eq_Z_of_olt_one)
       (use ylt trc in simp)
  then have "y = []"
    using translate_eq_Z_iff by simp
  then show "Wellfounded.accp Rst y"
    using stps_ne_nil[OF yst] by simp
qed

lemma domT_length_gt_one:
  assumes cst: "ST_PS c"
    and d: "domT c m"
  shows "1 < length c"
proof (rule ccontr)
  assume not_gt: "\<not> 1 < length c"
  have len: "length c = 1"
    using stps_len_pos[OF cst] not_gt
    by presburger
  have c0: "c = [(0, 0)]"
    by (rule stps_len_one[OF cst len])
  have val:
    "entry c 1 (length c - 1) = m + 1"
    using d unfolding domT_def by blast
  show False
    using val c0
    unfolding entry_def by simp
qed

lemma acc_of_Aop_nat:
  assumes cof:
    "\<forall>M N.
      ST_PS M \<longrightarrow> ST_PS N \<longrightarrow>
      translate N <o translate M \<longrightarrow>
      (\<exists>n. 1 \<le> n \<and>
        translate N \<le>o translate (M\<lbrakk>n\<rbrakk>))"
    and cst: "ST_PS c"
    and nat:
      "natDom c \<and>
       (\<forall>n. 1 \<le> n \<longrightarrow>
          Wellfounded.accp Rst (c\<lbrakk>n\<rbrakk>))"
  shows "Wellfounded.accp Rst c"
  by (metis acc_of_nat_branch
        cof cst nat)

lemma acc_of_Aop_graft:
  assumes cof:
    "\<forall>M N.
      ST_PS M \<longrightarrow> ST_PS N \<longrightarrow>
      translate N <o translate M \<longrightarrow>
      (\<exists>n. 1 \<le> n \<and>
        translate N \<le>o translate (M\<lbrakk>n\<rbrakk>))"
    and cst: "ST_PS c"
    and graft_case:
      "\<exists>m<u.
        domT c m \<and>
        (\<forall>z\<in>W m.
          based z \<longrightarrow>
          Wellfounded.accp Rst (graft c z))"
  shows "Wellfounded.accp Rst c"
  using assms
  by (metis acc_of_nat_branch
        domT_length_gt_one
        W_nil based_nil
        oper_eq_graft_nil_of_domT)

lemma acc_of_Aop_ST:
  assumes cof:
    "\<forall>M N.
      ST_PS M \<longrightarrow> ST_PS N \<longrightarrow>
      translate N <o translate M \<longrightarrow>
      (\<exists>n. 1 \<le> n \<and>
        translate N \<le>o translate (M\<lbrakk>n\<rbrakk>))"
    and cst: "ST_PS c"
    and A:
      "Aop W u
        {M. Wellfounded.accp Rst M} c"
  shows "Wellfounded.accp Rst c"
  using A
  unfolding Aop_def mem_Collect_eq
  by (metis acc_of_Aop_base[
        OF cst]
      acc_of_Aop_nat[OF cof cst]
      acc_of_Aop_graft[OF cof cst])

lemma acc_of_W_closed:
  assumes cof:
    "\<forall>M N.
      ST_PS M \<longrightarrow> ST_PS N \<longrightarrow>
      translate N <o translate M \<longrightarrow>
      (\<exists>n. 1 \<le> n \<and>
        translate N \<le>o translate (M\<lbrakk>n\<rbrakk>))"
  shows
    "\<forall>c.
      Aop W u
        {M. Wellfounded.accp Rst M} c
      \<longrightarrow>
      c \<in> {M. Wellfounded.accp Rst M}"
  by (intro allI impI)
     (metis acc_of_Aop_ST
        acc_of_not_ST_PS cof
        mem_Collect_eq)

lemma acc_of_W:
  assumes cof:
    "\<And>M N.
      ST_PS M \<Longrightarrow> ST_PS N \<Longrightarrow>
      translate N <o translate M \<Longrightarrow>
      \<exists>n. 1 \<le> n \<and>
        translate N \<le>o translate (M\<lbrakk>n\<rbrakk>)"
  shows
    "\<forall>M. M \<in> W u \<longrightarrow>
      Wellfounded.accp Rst M"
proof (intro allI impI)
  fix target
  assume targetW: "target \<in> W u"
  have cof_obj:
    "\<forall>M N.
      ST_PS M \<longrightarrow> ST_PS N \<longrightarrow>
      translate N <o translate M \<longrightarrow>
      (\<exists>n. 1 \<le> n \<and>
        translate N \<le>o translate (M\<lbrakk>n\<rbrakk>))"
  proof (intro allI impI)
    fix M N
    assume Mst: "ST_PS M"
      and Nst: "ST_PS N"
      and lt: "translate N <o translate M"
    show
      "\<exists>n. 1 \<le> n \<and>
        translate N \<le>o translate (M\<lbrakk>n\<rbrakk>)"
      by (rule cof[OF Mst Nst lt])
  qed
  have subset:
    "W u \<subseteq>
      {M. Wellfounded.accp Rst M}"
    by (rule A2')
       (rule acc_of_W_closed[OF cof_obj])
  show "Wellfounded.accp Rst target"
    using subset targetW by blast
qed

definition argOK :: "pairseq \<Rightarrow> bool" where
  "argOK R \<longleftrightarrow>
    (\<forall>p\<in>set R. 0 < fst p)"

definition rsum :: "pairseq \<Rightarrow> pairseq \<Rightarrow> bool" where
  "rsum A Q \<longleftrightarrow>
    (\<forall>p\<in>set (A @ Q).
      entry Q 0 0 \<le> fst p)"

lemma nextR_shift_iff:
  assumes hb: "b < length S"
  shows
    "nextR (map (\<lambda>p. (fst p + d, snd p)) S)
        i a b
      \<longleftrightarrow> nextR S i a b"
  unfolding nextR_def
  using nextrel0_shift_iff[OF hb, of d a]
    nextrel1_shift_iff[OF hb, of d a]
  by (cases "i = 0") auto

lemma hasParent_shift:
  assumes hb: "b < length S"
  shows
    "hasParent
        (map (\<lambda>p. (fst p + d, snd p)) S)
        i b
      \<longleftrightarrow> hasParent S i b"
  unfolding hasParent_def
  by (simp add: nextR_shift_iff[OF hb])

lemma parent_shift:
  assumes hb: "b < length S"
  shows
    "parent
        (map (\<lambda>p. (fst p + d, snd p)) S)
        i b =
      parent S i b"
  unfolding parent_def
  by (simp add: nextR_shift_iff[OF hb])

lemma oper_shift:
  "oper (map (\<lambda>p. (fst p + d, snd p)) M) n =
    map (\<lambda>p. (fst p + d, snd p)) (oper M n)"
proof (cases "length M - 1 = 0")
  case short: True
  have short_map:
    "length (map (\<lambda>p. (fst p + d, snd p)) M) - 1 = 0"
    using short by simp
  show ?thesis
    using oper_eq_self_of_short[
        OF short_map, of n]
      oper_eq_self_of_short[OF short, of n]
    by simp
next
  case long: False
  let ?sh = "\<lambda>p. (fst p + d, snd p)"
  let ?T = "map ?sh M"
  let ?j1 = "length M - 1"
  have last: "?j1 < length M"
    using long by presburger
  have lenT:
    "length ?T - 1 = ?j1"
    by simp
  have longT: "length ?T - 1 \<noteq> 0"
    using long by simp
  have idx:
    "idx1 ?T ?j1 = idx1 M ?j1"
    by (rule idx1_shift)
  show ?thesis
  proof (cases
      "hasParent M (idx1 M ?j1) ?j1")
    case hp: True
    have pos: "0 < entry M 0 ?j1"
      using no_hasParent_of_row0_zero hp
      by (cases "entry M 0 ?j1 = 0") auto
    have nz:
      "\<not> (entry M 0 ?j1 = 0 \<and>
        entry M 1 ?j1 = 0)"
      using pos by simp
    have hpT:
      "hasParent ?T
        (idx1 ?T (length ?T - 1))
        (length ?T - 1)"
      using hp lenT idx
        hasParent_shift[OF last, of d
          "idx1 M ?j1"]
      by simp
    have nzT:
      "\<not> (entry ?T 0 (length ?T - 1) = 0 \<and>
        entry ?T 1 (length ?T - 1) = 0)"
      using entry_shift[OF last, of d]
        lenT pos
      by simp
    let ?j0 =
      "parent M (idx1 M ?j1) ?j1"
    let ?D =
      "if 0 < idx1 M ?j1
       then entry M 0 ?j1 - entry M 0 ?j0
       else 0"
    have j0last: "?j0 < ?j1"
      by (rule nextR_index_lt)
         (rule parent_nextR[OF hp])
    have j0M: "?j0 < length M"
      using j0last last by simp
    have parT:
      "parent ?T (idx1 ?T (length ?T - 1))
          (length ?T - 1) = ?j0"
      using lenT idx parent_shift[
        OF last, of d "idx1 M ?j1"]
      by simp
    have delta:
      "(if 0 < idx1 ?T (length ?T - 1)
        then entry ?T 0 (length ?T - 1) -
          entry ?T 0
            (parent ?T
              (idx1 ?T (length ?T - 1))
              (length ?T - 1))
        else 0) = ?D"
      using entry_shift[OF last, of d]
        entry_shift[OF j0M, of d]
        lenT parT idx
      by simp
    have copies:
      "concat
        (map
          (\<lambda>k. map
            (\<lambda>j.
              (entry ?T 0 j +
                k * ?D,
               entry ?T 1 j))
            [?j0..<?j1])
          [0..<n]) =
       map ?sh
        (concat
          (map
            (\<lambda>k. map
              (\<lambda>j.
                (entry M 0 j +
                  k * ?D,
                 entry M 1 j))
              [?j0..<?j1])
            [0..<n]))"
    proof -
      show ?thesis
        apply (simp only: map_concat map_map
          o_def)
        apply (rule arg_cong[
          where f=concat])
        apply (rule map_cong)
         apply simp
        apply (rule map_cong)
         apply simp
        subgoal premises prems for k j
        proof -
          have jlt: "j < length M"
            using prems last by simp
          note es = entry_shift[
            OF jlt, of d]
          show ?thesis
            using es
            by (simp add:
                  add.assoc add.left_commute
                  add.commute)
        qed
        done
    qed
    have uT:
      "oper ?T n =
        take
          (parent ?T
            (idx1 ?T (length ?T - 1))
            (length ?T - 1)) ?T @
        concat
          (map
            (\<lambda>k. map
              (\<lambda>j.
                (entry ?T 0 j +
                  k * ?D,
                 entry ?T 1 j))
              [?j0..<?j1])
            [0..<n])"
      using oper_bad_unfold[
        OF longT nzT hpT, of n]
        lenT parT idx delta
      by simp
    have uM:
      "oper M n =
        take ?j0 M @
        concat
          (map
            (\<lambda>k. map
              (\<lambda>j.
                (entry M 0 j +
                  k * ?D,
                 entry M 1 j))
              [?j0..<?j1])
            [0..<n])"
      using oper_bad_unfold[
        OF long nz hp, of n]
      by simp
    show ?thesis
      using uT uM parT copies
      by (simp add: take_map)
  next
    case hp: False
    have hpT:
      "\<not> hasParent ?T
        (idx1 ?T (length ?T - 1))
        (length ?T - 1)"
      using hp lenT idx
        hasParent_shift[OF last, of d
          "idx1 M ?j1"]
      by simp
    have predM: "oper M n = Pred M"
    proof (cases
        "entry M 0 ?j1 = 0 \<and>
         entry M 1 ?j1 = 0")
      case True
      show ?thesis
        by (rule oper_eq_pred_of_zero[
              OF long True])
    next
      case False
      show ?thesis
        by (rule oper_eq_pred_of_noParent[
              OF long False hp])
    qed
    have predT: "oper ?T n = Pred ?T"
    proof (cases
        "entry ?T 0 (length ?T - 1) = 0 \<and>
         entry ?T 1 (length ?T - 1) = 0")
      case True
      show ?thesis
        by (rule oper_eq_pred_of_zero[
              OF longT True])
    next
      case False
      show ?thesis
        by (rule oper_eq_pred_of_noParent[
              OF longT False hpT])
    qed
    show ?thesis
      using predM predT
      unfolding Pred_def
      by (simp add: map_butlast)
  qed
qed

lemma domT_shift:
  "domT
      (map (\<lambda>p. (fst p + d, snd p)) M)
      m
    \<longleftrightarrow> domT M m"
proof (cases M)
  case Nil
  show ?thesis
    using Nil
    by (simp add: domT_def entry_def
          hasParent_def nextR_def
          nextrel0_def nextrel1_def)
next
  case (Cons p rest)
  have last:
    "length (p # rest) - 1 <
      length (p # rest)"
    by simp
  show ?thesis
    using Cons entry_shift[
        OF last, of d]
      hasParent_shift[
        OF last, of d 1]
    unfolding domT_def by simp
qed

lemma natDom_shift:
  "natDom
      (map (\<lambda>p. (fst p + d, snd p)) M)
    \<longleftrightarrow> natDom M"
  unfolding natDom_def
  using domT_shift[
    where M=M and d=d]
  by blast

lemma graft_shift:
  assumes Mne: "M \<noteq> []"
  shows
    "graft
      (map (\<lambda>p. (fst p + d, snd p)) M)
      z =
     map (\<lambda>p. (fst p + d, snd p))
      (graft M z)"
proof -
  have last:
    "length M - 1 < length M"
    using Mne by simp
  note es = entry_shift[OF last, of d]
  show ?thesis
    using es
    unfolding graft_def
    by (simp add: map_butlast map_map
          o_def add.assoc)
qed

lemma graft_shift_mem:
  assumes Mne: "M \<noteq> []"
    and mem:
      "map (\<lambda>p. (fst p + d, snd p))
        (graft M z) \<in> X"
  shows
    "graft
      (map (\<lambda>p. (fst p + d, snd p)) M)
      z \<in> X"
  using mem graft_shift[
    OF Mne, of d z]
  by simp

lemma Aop_shift_nat:
  assumes nat:
    "natDom M \<and>
     (\<forall>n. 1 \<le> n \<longrightarrow>
       map (\<lambda>p. (fst p + d, snd p))
         (oper M n) \<in> W u)"
  shows
    "natDom
        (map (\<lambda>p. (fst p + d, snd p)) M)
     \<and>
     (\<forall>n. 1 \<le> n \<longrightarrow>
       oper
        (map (\<lambda>p. (fst p + d, snd p)) M)
        n \<in> W u)"
  using nat natDom_shift[
      where M=M and d=d]
    oper_shift[where M=M and d=d]
  by auto

lemma domT_nonempty:
  assumes "domT M m"
  shows "M \<noteq> []"
  using assms not_domT_nil[of m]
  by blast

lemma Aop_shift_graft:
  assumes graft_case:
    "\<exists>m<u.
      domT M m \<and>
      (\<forall>z\<in>W m.
        based z \<longrightarrow>
        map (\<lambda>p. (fst p + d, snd p))
          (graft M z) \<in> W u)"
  shows
    "\<exists>m<u.
      domT
        (map (\<lambda>p. (fst p + d, snd p)) M)
        m \<and>
      (\<forall>z\<in>W m.
        based z \<longrightarrow>
        graft
          (map (\<lambda>p. (fst p + d, snd p)) M)
          z \<in> W u)"
  using graft_case
  by (fastforce simp: domT_shift
        intro: graft_shift_mem
        dest: domT_nonempty)

lemma Aop_shift_base:
  assumes base:
    "length M \<le> 1 \<and> entry M 1 0 = 0"
  shows
    "length
      (map (\<lambda>p. (fst p + d, snd p)) M)
      \<le> 1 \<and>
     entry
      (map (\<lambda>p. (fst p + d, snd p)) M)
      1 0 = 0"
  using base
  by (cases M)
     (simp_all add: entry_def)

lemma Aop_shift:
  assumes A:
    "Aop W u
      {N. map (\<lambda>p. (fst p + d, snd p)) N
          \<in> W u}
      M"
  shows
    "Aop W u (W u)
      (map (\<lambda>p. (fst p + d, snd p)) M)"
  using A
  unfolding Aop_def mem_Collect_eq
  apply (elim disjE)
    apply (rule disjI1)
    apply (erule Aop_shift_base)
   apply (rule disjI2, rule disjI1)
   apply (erule Aop_shift_nat)
  apply (rule disjI2, rule disjI2)
  by (erule Aop_shift_graft)

lemma W_shift_subset:
  shows
    "W u \<subseteq>
      {N. map (\<lambda>p. (fst p + d, snd p)) N
        \<in> W u}"
  by (rule A2)
     (auto simp: Aset_def
        intro: A1_intro Aop_shift)

lemma W_shift:
  assumes h: "M \<in> W u"
  shows
    "map (\<lambda>p. (fst p + d, snd p)) M
      \<in> W u"
  using W_shift_subset[
      where u=u and d=d]
    h
  by blast

lemma split_lastMin:
  assumes Mne: "M \<noteq> []"
  shows
    "\<exists>A Q.
      M = A @ Q \<and>
      Q \<noteq> [] \<and>
      rsum A Q \<and>
      (\<forall>p\<in>set (tl Q).
        entry Q 0 0 < fst p)"
  using Mne
proof (induction M rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc q M')
  show ?case
  proof (cases "M' = []")
    case True
    show ?thesis
    proof (intro exI conjI)
      show "M' @ [q] = [] @ [q]"
        using True by simp
      show "[q] \<noteq> []" by simp
      show "rsum [] [q]"
        unfolding rsum_def entry_def
        by simp
      show
        "\<forall>p\<in>set (tl [q]).
          entry [q] 0 0 < fst p"
        by simp
    qed
  next
    case False
    obtain A Q where eq: "M' = A @ Q"
      and Qne: "Q \<noteq> []"
      and rs: "rsum A Q"
      and tail:
        "\<forall>p\<in>set (tl Q).
          entry Q 0 0 < fst p"
      using snoc.IH[OF False] by blast
    show ?thesis
    proof (cases "fst q \<le> entry Q 0 0")
      case qmin: True
      show ?thesis
      proof (intro exI conjI)
        show "M' @ [q] = M' @ [q]" ..
        show "[q] \<noteq> []" by simp
        show "rsum M' [q]"
        proof (unfold rsum_def, intro ballI)
          fix p
          assume p: "p \<in> set (M' @ [q])"
          have head:
            "entry [q] 0 0 = fst q"
            unfolding entry_def by simp
          show "entry [q] 0 0 \<le> fst p"
          proof (cases "p = q")
            case True
            show ?thesis using True head by simp
          next
            case False
            have pM: "p \<in> set M'"
              using p False by auto
            have pAQ: "p \<in> set (A @ Q)"
              using pM eq by simp
            have
              "entry Q 0 0 \<le> fst p"
              using rs pAQ
              unfolding rsum_def by blast
            then show ?thesis
              using qmin head by simp
          qed
        qed
        show
          "\<forall>p\<in>set (tl [q]).
            entry [q] 0 0 < fst p"
          by simp
      qed
    next
      case qdeep: False
      have head:
        "entry (Q @ [q]) 0 0 =
          entry Q 0 0"
        using Qne
        by (cases Q)
           (simp_all add: entry_def)
      show ?thesis
      proof (intro exI conjI)
        show "M' @ [q] = A @ (Q @ [q])"
          using eq by simp
        show "Q @ [q] \<noteq> []" by simp
        show "rsum A (Q @ [q])"
        proof (unfold rsum_def, intro ballI)
          fix p
          assume p:
            "p \<in> set (A @ Q @ [q])"
          show
            "entry (Q @ [q]) 0 0 \<le> fst p"
          proof (cases "p = q")
            case True
            show ?thesis
              using True qdeep head
              by simp
          next
            case False
            have pAQ: "p \<in> set (A @ Q)"
              using p False by auto
            have rp:
              "entry Q 0 0 \<le> fst p"
              using rs pAQ
              unfolding rsum_def by blast
            show ?thesis
              using rp head by simp
          qed
        qed
        show
          "\<forall>p\<in>set (tl (Q @ [q])).
            entry (Q @ [q]) 0 0 < fst p"
        proof (cases Q)
          case Nil
          then show ?thesis using Qne by simp
        next
          case (Cons p0 rest)
          show ?thesis
          proof (intro ballI)
            fix p
            assume p:
              "p \<in> set (tl (Q @ [q]))"
            have cases:
              "p \<in> set (tl Q) \<or> p = q"
              using p Cons by auto
            from cases show
              "entry (Q @ [q]) 0 0 < fst p"
            proof
              assume pt: "p \<in> set (tl Q)"
              have tq:
                "entry Q 0 0 < fst p"
                using tail pt by blast
              show ?thesis
                using tq head by simp
            next
              assume "p = q"
              then show ?thesis
                using qdeep head by simp
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma map_sub_add:
  fixes X :: pairseq
    and c :: nat
  assumes h: "\<forall>p\<in>set X. c \<le> fst p"
  shows
    "map (\<lambda>p. (fst p + c, snd p))
      (map (\<lambda>p. (fst p - c, snd p)) X) =
     X"
  using h
proof (induction X)
  case Nil
  then show ?case by simp
next
  case (Cons q X)
  have qc: "c \<le> fst q"
    using Cons.prems by simp
  have tail:
    "\<forall>p\<in>set X. c \<le> fst p"
    using Cons.prems by simp
  note IH = Cons.IH[OF tail]
  obtain a b where q: "q = (a, b)"
    by (cases q)
  have ac: "c \<le> a"
    using qc by (simp add: q)
  have nless: "\<not> a < c"
    using ac by simp
  have inv':
    "c + (a - c) = a"
    by (rule add_diff_inverse_nat[OF nless])
  have inv: "a - c + c = a"
    using inv' by (simp add: add.commute)
  show ?case
    using IH inv
    by (simp add: q)
qed

lemma rsum_decomp:
  assumes h: "rsum A Q"
  shows
    "map
      (\<lambda>p. (fst p + entry Q 0 0, snd p))
      (map
        (\<lambda>p.
          (fst p - entry Q 0 0, snd p))
        A @
       map
        (\<lambda>p.
          (fst p - entry Q 0 0, snd p))
        Q) =
     A @ Q"
proof -
  have hA:
    "\<forall>p\<in>set A.
      entry Q 0 0 \<le> fst p"
    using h unfolding rsum_def by auto
  have hQ:
    "\<forall>p\<in>set Q.
      entry Q 0 0 \<le> fst p"
    using h unfolding rsum_def by auto
  show ?thesis
    using map_sub_add[OF hA]
      map_sub_add[OF hQ]
    by simp
qed

lemma entry_sub_zero:
  assumes Qne: "Q \<noteq> []"
  shows
    "entry
      (map
        (\<lambda>p.
          (fst p - entry Q 0 0, snd p))
        Q)
      0 0 = 0"
  using Qne
  by (cases Q)
     (simp_all add: entry_def)

lemma oper_append_gen:
  assumes Qlen: "2 \<le> length Q"
    and rs: "rsum A Q"
  shows
    "oper (A @ Q) n = A @ oper Q n"
proof -
  let ?c = "entry Q 0 0"
  let ?down =
    "\<lambda>p. (fst p - ?c, snd p)"
  let ?up =
    "\<lambda>p. (fst p + ?c, snd p)"
  let ?A0 = "map ?down A"
  let ?Q0 = "map ?down Q"
  have Qne: "Q \<noteq> []"
    using Qlen by auto
  have root:
    "entry ?Q0 0 0 = 0"
    by (rule entry_sub_zero[OF Qne])
  have len0:
    "2 \<le> length ?Q0"
    using Qlen by simp
  have AP:
    "map ?up (?A0 @ ?Q0) = A @ Q"
    by (rule rsum_decomp[OF rs])
  have Arec:
    "map ?up ?A0 = A"
    by (rule map_sub_add)
       (use rs in \<open>auto simp: rsum_def\<close>)
  have Qrec:
    "map ?up ?Q0 = Q"
    by (rule map_sub_add)
       (use rs in \<open>auto simp: rsum_def\<close>)
  have shiftAP:
    "oper (map ?up (?A0 @ ?Q0)) n =
      map ?up (oper (?A0 @ ?Q0) n)"
    by (rule oper_shift)
  have append0:
    "oper (?A0 @ ?Q0) n =
      ?A0 @ oper ?Q0 n"
    by (rule oper_append_right[
          OF len0 root])
  have shiftQ:
    "oper (map ?up ?Q0) n =
      map ?up (oper ?Q0 n)"
    by (rule oper_shift)
  show ?thesis
    using AP Arec Qrec shiftAP append0
      shiftQ
    by simp
qed

lemma graft_append:
  assumes Qne: "Q \<noteq> []"
  shows
    "graft (A @ Q) z = A @ graft Q z"
proof -
  obtain q Q' where Q: "Q = q # Q'"
    using Qne by (cases Q) auto
  have len:
    "length (A @ Q) - 1 =
      length A + (length Q - 1)"
    using Q by simp
  show ?thesis
    using Qne len
    unfolding graft_def
    by (simp add: butlast_append
          entry_append_right add.assoc)
qed

lemma hasParent_append_gen:
  assumes jQ: "j < length Q"
    and rs: "rsum A Q"
  shows
    "hasParent (A @ Q) i (length A + j)
      \<longleftrightarrow> hasParent Q i j"
proof -
  let ?c = "entry Q 0 0"
  let ?down =
    "\<lambda>p. (fst p - ?c, snd p)"
  let ?up =
    "\<lambda>p. (fst p + ?c, snd p)"
  let ?A0 = "map ?down A"
  let ?Q0 = "map ?down Q"
  have Qne: "Q \<noteq> []"
    using jQ by auto
  have root:
    "entry ?Q0 0 0 = 0"
    by (rule entry_sub_zero[OF Qne])
  have AP:
    "map ?up (?A0 @ ?Q0) = A @ Q"
    by (rule rsum_decomp[OF rs])
  have Qrec:
    "map ?up ?Q0 = Q"
    by (rule map_sub_add)
       (use rs in \<open>auto simp: rsum_def\<close>)
  have lenA:
    "length ?A0 = length A"
    by simp
  have lenQ:
    "length ?Q0 = length Q"
    by simp
  have bound:
    "length A + j < length (?A0 @ ?Q0)"
    using jQ by simp
  have step1:
    "hasParent (A @ Q) i (length A + j)
      \<longleftrightarrow>
     hasParent (?A0 @ ?Q0) i (length ?A0 + j)"
    using hasParent_shift[
        OF bound, of ?c i]
      AP lenA
    by simp
  have step3:
    "hasParent ?Q0 i j
      \<longleftrightarrow> hasParent Q i j"
    using hasParent_shift[
        of j ?Q0 ?c i]
      Qrec jQ lenQ
    by simp
  have step2:
    "hasParent (?A0 @ ?Q0) i
        (length ?A0 + j)
      \<longleftrightarrow>
     hasParent ?Q0 i j"
  proof (cases "entry ?Q0 0 j = 0")
    case zero: True
    have left:
      "\<not> hasParent (?A0 @ ?Q0) i
        (length ?A0 + j)"
    proof
      assume hp:
        "hasParent (?A0 @ ?Q0) i
          (length ?A0 + j)"
      have eappend:
        "entry (?A0 @ ?Q0) 0
          (length ?A0 + j) =
         entry ?Q0 0 j"
        by (rule entry_append_right)
      have ez:
        "entry (?A0 @ ?Q0) 0
          (length ?A0 + j) = 0"
        using zero eappend by simp
      show False
        by (rule no_hasParent_of_row0_zero[
              OF ez hp])
    qed
    have right:
      "\<not> hasParent ?Q0 i j"
      using zero no_hasParent_of_row0_zero
      by blast
    show ?thesis using left right by blast
  next
    case nonzero: False
    have eappend:
      "entry (?A0 @ ?Q0) 0
        (length ?A0 + j) =
       entry ?Q0 0 j"
      by (rule entry_append_right)
    have pos:
      "0 <
        entry (?A0 @ ?Q0) 0
          (length ?A0 + j)"
      using nonzero eappend by simp
    show ?thesis
      by (rule hasParent_append_right[
            OF root pos])
  qed
  show ?thesis
    using step1 step2 step3 by blast
qed

lemma domT_append:
  assumes Qne: "Q \<noteq> []"
    and rs: "rsum A Q"
  shows
    "domT (A @ Q) m \<longleftrightarrow> domT Q m"
proof -
  obtain q Q' where Q: "Q = q # Q'"
    using Qne by (cases Q) auto
  have pos: "0 < length Q"
    using Q by simp
  have len:
    "length (A @ Q) - 1 =
      length A + (length Q - 1)"
    using Q by simp
  show ?thesis
    unfolding domT_def
    using hasParent_append_gen[
        of "length Q - 1" Q A 1]
      rs pos len
    by (simp add: entry_append_right)
qed

lemma natDom_append:
  assumes Qne: "Q \<noteq> []"
    and rs: "rsum A Q"
  shows
    "natDom (A @ Q) \<longleftrightarrow> natDom Q"
  unfolding natDom_def
  using domT_append[
      OF Qne rs]
  by blast

definition XA ::
  "pairseq \<Rightarrow> pairseq set \<Rightarrow>
   pairseq set"
where
  "XA A X =
    {B. rsum A B \<longrightarrow> A @ B \<in> X}"

lemma entry_zero_headD:
  "entry X 0 0 =
    fst (nth_default (0, 0) X 0)"
  by (cases X)
     (simp_all add: entry_def
        nth_default_def)

lemma oper_head_eq:
  assumes hn: "1 \<le> n"
  shows
    "entry (oper B n) 0 0 =
      entry B 0 0"
proof (cases "1 < length B")
  case long: True
  obtain R where op:
    "oper B n = butlast B @ R"
    by (meson oper_eq_dropLast_append[
          OF long hn])
  obtain a B' where B1: "B = a # B'"
    using long by (cases B) auto
  obtain b U where B2: "B' = b # U"
    using long B1 by (cases B') auto
  have B: "B = a # b # U"
    using B1 B2 by simp
  show ?thesis
    using op B
    by (simp add: entry_def)
next
  case False
  have short: "length B - 1 = 0"
    using False by simp
  show ?thesis
    using oper_eq_self_of_short[
        OF short, of n]
    by simp
qed

lemma entry_pair_mem:
  assumes jB: "j < length B"
  shows
    "(entry B 0 j, entry B 1 j)
      \<in> set B"
proof -
  have pair:
    "(entry B 0 j, entry B 1 j) =
      B ! j"
    using jB
    by (simp add: entry_def prod_eq_iff)
  have mem: "B ! j \<in> set B"
    by (rule nth_mem[OF jB])
  show ?thesis
    using pair mem by simp
qed

lemma oper_mem_ge:
  assumes ge:
    "\<forall>p\<in>set B. c \<le> fst p"
  shows
    "\<forall>p\<in>set (oper B n).
      c \<le> fst p"
proof -
  let ?down =
    "\<lambda>p. (fst p - c, snd p)"
  let ?up =
    "\<lambda>p. (fst p + c, snd p)"
  let ?B0 = "map ?down B"
  have rec:
    "map ?up ?B0 = B"
    by (rule map_sub_add[OF ge])
  have shift:
    "oper (map ?up ?B0) n =
      map ?up (oper ?B0 n)"
    by (rule oper_shift)
  show ?thesis
    using rec shift by auto
qed

lemma graft_mem_ge:
  assumes Bne: "B \<noteq> []"
    and ge:
      "\<forall>p\<in>set B. c \<le> fst p"
  shows
    "\<forall>p\<in>set (graft B z).
      c \<le> fst p"
proof -
  let ?down =
    "\<lambda>p. (fst p - c, snd p)"
  let ?up =
    "\<lambda>p. (fst p + c, snd p)"
  let ?B0 = "map ?down B"
  have B0ne: "?B0 \<noteq> []"
    using Bne by simp
  have rec:
    "map ?up ?B0 = B"
    by (rule map_sub_add[OF ge])
  have shift:
    "graft (map ?up ?B0) z =
      map ?up (graft ?B0 z)"
    by (rule graft_shift[OF B0ne])
  show ?thesis
    using rec shift by auto
qed

lemma graft_head_eq:
  assumes Bne: "B \<noteq> []"
    and bz: "based z"
    and grne: "graft B z \<noteq> []"
  shows
    "entry (graft B z) 0 0 =
      entry B 0 0"
proof -
  obtain b0 B' where B: "B = b0 # B'"
    using Bne by (cases B) auto
  show ?thesis
  proof (cases B')
    case Nil
    have Bs: "B = [b0]"
      using B Nil by simp
    show ?thesis
    proof (cases z)
      case Nilz: Nil
      then show ?thesis
        using grne Bs
        by (simp add: graft_def)
    next
      case (Cons z0 z')
      have z0:
        "fst z0 = 0"
        using bz Cons
        unfolding based_def
        by (simp add: entry_def)
      show ?thesis
        using Bs Cons z0
        by (simp add: graft_def entry_def)
    qed
  next
    case (Cons b1 B'')
    have Bs: "B = b0 # b1 # B''"
      using B Cons by simp
    then show ?thesis
      by (simp add: graft_def entry_def)
  qed
qed

lemma no_hasParent_at_zero:
  "\<not> hasParent M i 0"
proof
  assume hp: "hasParent M i 0"
  then obtain j where rel:
    "nextR M i j 0"
    unfolding hasParent_def by blast
  have "j < 0"
    by (rule nextR_index_lt[OF rel])
  then show False by simp
qed

lemma XA_closed:
  assumes closed:
    "\<forall>M. Aop W u X M \<longrightarrow> M \<in> X"
    and A_X: "A \<in> X"
  shows
    "\<forall>B. Aop W u (XA A X) B
      \<longrightarrow> B \<in> XA A X"
proof (intro allI impI)
  fix B
  assume AB: "Aop W u (XA A X) B"
  show "B \<in> XA A X"
    unfolding XA_def mem_Collect_eq
  proof (intro impI)
    assume rs: "rsum A B"
    show "A @ B \<in> X"
    proof (cases "B = []")
      case True
      then show ?thesis using A_X by simp
    next
      case Bne: False
      have Bge:
        "\<forall>p\<in>set B.
          entry B 0 0 \<le> fst p"
        using rs unfolding rsum_def by auto
      have Age:
        "\<forall>p\<in>set A.
          entry B 0 0 \<le> fst p"
        using rs unfolding rsum_def by auto
      have branches:
        "(length B \<le> 1 \<and>
            entry B 1 0 = 0) \<or>
         (natDom B \<and>
            (\<forall>n. 1 \<le> n \<longrightarrow>
              oper B n \<in> XA A X)) \<or>
         (\<exists>m<u.
            domT B m \<and>
            (\<forall>z\<in>W m.
              based z \<longrightarrow>
              graft B z \<in> XA A X))"
        using AB unfolding Aop_def by blast
      from branches show ?thesis
      proof
        assume base:
          "length B \<le> 1 \<and>
            entry B 1 0 = 0"
        have Blen: "length B = 1"
          using Bne base by (cases B) auto
        obtain q where B: "B = [q]"
          using Blen by (cases B) auto
        show ?thesis
        proof (cases "A = []")
          case True
          have "B \<in> X"
            by (rule closed[rule_format])
               (use base in
                 \<open>auto simp: Aop_def\<close>)
          then show ?thesis using True by simp
        next
          case Ane: False
          have row:
            "entry B 1 (length B - 1) = 0"
            using base Blen by simp
          have natB: "natDom B"
            using natDom_iff[
                where M=B] row
            by blast
          have natAB: "natDom (A @ B)"
            by (rule natDom_append[
                  OF Bne rs, THEN iffD2,
                  OF natB])
          have last:
            "length (A @ B) - 1 =
              length A"
            using B Ane by simp
          have nop:
            "\<forall>i.
              \<not> hasParent (A @ B) i
                (length (A @ B) - 1)"
          proof (intro allI)
            fix i
            have suffix:
              "hasParent (A @ B) i
                  (length A + 0)
                \<longleftrightarrow>
               hasParent B i 0"
              by (rule hasParent_append_gen[
                    OF _ rs])
                 (use Blen in simp)
            show
              "\<not> hasParent (A @ B) i
                (length (A @ B) - 1)"
              using suffix last
                no_hasParent_at_zero[
                  where M=B and i=i]
              by simp
          qed
          have pred:
            "Pred (A @ B) = A"
            using Ane B
            by (simp add: Pred_def
                  butlast_append)
          have ops:
            "\<forall>n. 1 \<le> n \<longrightarrow>
              oper (A @ B) n \<in> X"
          proof (intro allI impI)
            fix n :: nat
            assume "1 \<le> n"
            have long:
              "length (A @ B) - 1 \<noteq> 0"
              using Ane B by simp
            have op:
              "oper (A @ B) n =
                Pred (A @ B)"
            proof (cases
              "entry (A @ B) 0
                  (length (A @ B) - 1) = 0
               \<and>
               entry (A @ B) 1
                  (length (A @ B) - 1) = 0")
              case True
              show ?thesis
                by (rule oper_eq_pred_of_zero[
                      OF long True])
            next
              case False
              show ?thesis
                by (rule oper_eq_pred_of_noParent[
                      OF long False])
                   (use nop in simp)
            qed
            show "oper (A @ B) n \<in> X"
              using op pred A_X by simp
          qed
          show ?thesis
            by (rule closed[rule_format])
               (use natAB ops in
                 \<open>auto simp: Aop_def\<close>)
        qed
      next
        assume rest:
          "(natDom B \<and>
              (\<forall>n. 1 \<le> n \<longrightarrow>
                oper B n \<in> XA A X)) \<or>
           (\<exists>m<u.
              domT B m \<and>
              (\<forall>z\<in>W m.
                based z \<longrightarrow>
                graft B z \<in> XA A X))"
        from rest show ?thesis
        proof
          assume nat:
            "natDom B \<and>
              (\<forall>n. 1 \<le> n \<longrightarrow>
                oper B n \<in> XA A X)"
          show ?thesis
          proof (cases "2 \<le> length B")
            case long: True
            have natAB: "natDom (A @ B)"
              by (rule natDom_append[
                    OF Bne rs, THEN iffD2])
                 (use nat in simp)
            have ops:
              "\<forall>n. 1 \<le> n \<longrightarrow>
                oper (A @ B) n \<in> X"
            proof (intro allI impI)
              fix n :: nat
              assume n1: "1 \<le> n"
              have mem:
                "oper B n \<in> XA A X"
                using nat n1 by blast
              have rsop:
                "rsum A (oper B n)"
                unfolding rsum_def
              proof (intro ballI)
                fix p
                assume p:
                  "p \<in> set (A @ oper B n)"
                have head:
                  "entry (oper B n) 0 0 =
                    entry B 0 0"
                  by (rule oper_head_eq[OF n1])
                show
                  "entry (oper B n) 0 0
                    \<le> fst p"
                  using p head Age
                    oper_mem_ge[
                      OF Bge, where n=n]
                  by auto
              qed
              have append:
                "A @ oper B n \<in> X"
                using mem rsop
                unfolding XA_def by simp
              show "oper (A @ B) n \<in> X"
                using oper_append_gen[
                    OF long rs, of n]
                  append
                by simp
            qed
            show ?thesis
              by (rule closed[rule_format])
                 (use natAB ops in
                   \<open>auto simp: Aop_def\<close>)
          next
            case False
            have pos: "0 < length B"
              using Bne by simp
            have less: "length B < 2"
              using False by simp
            have len1: "length B = 1"
              using pos less by presburger
            have short:
              "length B - 1 = 0"
              using len1 by simp
            have op1: "oper B 1 = B"
              by (rule oper_eq_self_of_short[
                    OF short])
            have mem: "oper B 1 \<in> XA A X"
              using nat by simp
            show ?thesis
              using mem rs op1
              unfolding XA_def by simp
          qed
        next
          assume gr:
            "\<exists>m<u.
              domT B m \<and>
              (\<forall>z\<in>W m.
                based z \<longrightarrow>
                graft B z \<in> XA A X)"
          obtain m where mu: "m < u"
            and dom: "domT B m"
            and grX:
              "\<forall>z\<in>W m.
                based z \<longrightarrow>
                graft B z \<in> XA A X"
            using gr by blast
          have domAB: "domT (A @ B) m"
            by (rule domT_append[
                  OF Bne rs, THEN iffD2,
                  OF dom])
          have grafts:
            "\<forall>z\<in>W m.
              based z \<longrightarrow>
              graft (A @ B) z \<in> X"
          proof (intro ballI impI)
            fix z
            assume zW: "z \<in> W m"
              and bz: "based z"
            have mem:
              "graft B z \<in> XA A X"
              using grX zW bz by blast
            have rsg:
              "rsum A (graft B z)"
            proof (cases "graft B z = []")
              case True
              then show ?thesis
                unfolding rsum_def entry_def
                by simp
            next
              case grne: False
              have head:
                "entry (graft B z) 0 0 =
                  entry B 0 0"
                by (rule graft_head_eq[
                      OF Bne bz grne])
              show ?thesis
                unfolding rsum_def
                using head Age
                  graft_mem_ge[
                    OF Bne Bge, where z=z]
                by auto
            qed
            have append:
              "A @ graft B z \<in> X"
              using mem rsg
              unfolding XA_def by simp
            show "graft (A @ B) z \<in> X"
              using graft_append[
                  OF Bne, of A z]
                append by simp
          qed
          show ?thesis
            by (rule closed[rule_format])
               (use mu domAB grafts in
                 \<open>auto simp: Aop_def\<close>)
        qed
      qed
    qed
  qed
qed

lemma W_add:
  assumes A: "A \<in> W u"
    and B: "B \<in> W u"
    and rs: "rsum A B"
  shows "A @ B \<in> W u"
proof -
  have closed:
    "\<forall>M. Aop W u (W u) M
      \<longrightarrow> M \<in> W u"
    using A1_intro by blast
  have sub:
    "W u \<subseteq> XA A (W u)"
    by (rule A2')
       (rule XA_closed[OF closed A])
  have BX: "B \<in> XA A (W u)"
    using sub B by blast
  show ?thesis
    using BX rs unfolding XA_def by simp
qed

lemma graft_Om:
  "graft [(0, v)] z = z"
  unfolding graft_def entry_def
  by simp

lemma domT_Om:
  "domT [(0, m + 1)] m"
proof -
  have nop:
    "\<not> hasParent [(0, m + 1)] 1 0"
    by (rule no_hasParent_at_zero)
  show ?thesis
    using nop
    unfolding domT_def entry_def
    by simp
qed

lemma Om_mem_W:
  "[(0, v)] \<in> W v"
proof (cases v)
  case 0
  show ?thesis
    by (rule A1_intro)
       (use 0 in
         \<open>auto simp: Aop_def entry_def\<close>)
next
  case (Suc w)
  have grafts:
    "\<forall>z\<in>W w.
      based z \<longrightarrow>
      graft [(0, Suc w)] z \<in> W (Suc w)"
  proof (intro ballI impI)
    fix z
    assume zW: "z \<in> W w"
    have sub:
      "W w \<subseteq> W (Suc w)"
      by (rule W_mono) simp
    have zW': "z \<in> W (Suc w)"
      using sub zW by blast
    show
      "graft [(0, Suc w)] z
        \<in> W (Suc w)"
      using zW'
      by (simp add: graft_Om)
  qed
  show ?thesis
    by (rule A1_intro)
       (use domT_Om[where m=w]
          grafts Suc in
        \<open>auto simp: Aop_def\<close>)
qed

definition Wstar :: "pairseq set" where
  "Wstar =
    {R. argOK R \<longrightarrow>
      (\<forall>v. (0, v) # R \<in> W v)}"

fun tow ::
  "nat \<Rightarrow> pairseq \<Rightarrow> nat \<Rightarrow>
   pairseq"
where
  "tow v R 0 = []"
| "tow v R (Suc k) =
    (0, v) # graft R (tow v R k)"

lemma graft_cons:
  assumes Rne: "R \<noteq> []"
  shows
    "graft ((0, v) # R) z =
      (0, v) # graft R z"
proof -
  have
    "graft ([(0, v)] @ R) z =
      [(0, v)] @ graft R z"
    by (rule graft_append[OF Rne])
  then show ?thesis by simp
qed

lemma entry_cons:
  "entry (p # R) i (j + 1) =
    entry R i j"
proof -
  have
    "entry ([p] @ R) i
        (length [p] + j) =
      entry R i j"
    by (rule entry_append_right)
  then show ?thesis
    by (simp add: add.commute)
qed

lemma nextR_cons:
  "nextR (p # R) i
      (j0 + 1) (j1 + 1)
    \<longleftrightarrow> nextR R i j0 j1"
proof -
  have
    "nextR ([p] @ R) i
        (length [p] + j0)
        (length [p] + j1)
      \<longleftrightarrow>
     nextR R i j0 j1"
    by (rule nextR_append_right)
  then show ?thesis
    by (simp add: add.commute)
qed

lemma le0_cons:
  "le0 (p # R) (j0 + 1) (j1 + 1)
    \<longleftrightarrow> le0 R j0 j1"
proof -
  have
    "le0 ([p] @ R)
        (length [p] + j0)
        (length [p] + j1)
      \<longleftrightarrow>
     le0 R j0 j1"
    by (rule le0_append_right)
  then show ?thesis
    by (simp add: add.commute)
qed

lemma idx1_cons:
  "idx1 (p # R) (j + 1) =
    idx1 R j"
proof -
  have
    "idx1 ([p] @ R)
        (length [p] + j) =
      idx1 R j"
    by (rule idx1_append_right)
  then show ?thesis
    by (simp add: add.commute)
qed

lemma hasParent_zero_iff:
  assumes bM: "b < length M"
  shows
    "hasParent M 0 b
      \<longleftrightarrow>
     (\<exists>k. k < b \<and>
       entry M 0 k < entry M 0 b)"
proof
  assume hp: "hasParent M 0 b"
  then obtain k where rel:
    "nextR M 0 k b"
    unfolding hasParent_def by blast
  have n0: "nextrel0 M k b"
    using rel unfolding nextR_def by simp
  show
    "\<exists>k. k < b \<and>
      entry M 0 k < entry M 0 b"
    using n0 unfolding nextrel0_def
    by blast
next
  assume ex:
    "\<exists>k. k < b \<and>
      entry M 0 k < entry M 0 b"
  let ?C =
    "{k. k < b \<and>
      entry M 0 k < entry M 0 b}"
  obtain k where kC: "k \<in> ?C"
    using ex by blast
  have fin: "finite ?C"
    by (rule finite_subset[
          of ?C "{..<b}"])
       auto
  have Cne: "?C \<noteq> {}"
    using kC by auto
  let ?g = "Max ?C"
  have gC: "?g \<in> ?C"
    by (rule Max_in[OF fin Cne])
  have gmax:
    "\<forall>q\<in>?C. q \<le> ?g"
    by (intro ballI)
       (rule Max_ge[OF fin])
  have edge0:
    "nextrel0 M ?g b"
    unfolding nextrel0_def
  proof (intro conjI)
    show "?g < length M"
      using gC bM by auto
    show "b < length M" by (rule bM)
    show "?g < b" using gC by simp
    show
      "entry M 0 ?g < entry M 0 b"
      using gC by simp
    show
      "\<forall>j. ?g < j \<and> j < b
        \<longrightarrow>
        entry M 0 b \<le> entry M 0 j"
    proof (intro allI impI)
      fix j
      assume j:
        "?g < j \<and> j < b"
      show
        "entry M 0 b \<le> entry M 0 j"
      proof (rule ccontr)
        assume
          "\<not> entry M 0 b
            \<le> entry M 0 j"
        then have "j \<in> ?C"
          using j by simp
        then have "j \<le> ?g"
          by (rule gmax[rule_format])
        then show False using j by simp
      qed
    qed
  qed
  have unique:
    "\<forall>y. nextrel0 M y b
      \<longrightarrow> y = ?g"
  proof (intro allI impI)
    fix y
    assume yn: "nextrel0 M y b"
    have yC: "y \<in> ?C"
      using yn unfolding nextrel0_def
      by blast
    have yg: "y \<le> ?g"
      by (rule gmax[rule_format, OF yC])
    show "y = ?g"
    proof (rule ccontr)
      assume "y \<noteq> ?g"
      then have yg': "y < ?g"
        using yg by simp
      have valley:
        "entry M 0 b \<le> entry M 0 ?g"
        using yn yg' gC
        unfolding nextrel0_def by blast
      have strict:
        "entry M 0 ?g < entry M 0 b"
        using gC by simp
      show False using valley strict by simp
    qed
  qed
  show "hasParent M 0 b"
    unfolding hasParent_def
  proof (rule ex1I[
      of _ ?g])
    show "nextR M 0 ?g b"
      using edge0
      unfolding nextR_def by simp
    fix y
    assume "nextR M 0 y b"
    then have "nextrel0 M y b"
      unfolding nextR_def by simp
    then show "y = ?g"
      by (rule unique[rule_format])
  qed
qed

lemma le0_cons_zero:
  assumes ok: "argOK R"
  shows
    "\<forall>j. j < length R
      \<longrightarrow>
      le0 ((0, v) # R) 0 (j + 1)"
proof (intro allI impI)
  fix j
  assume jR: "j < length R"
  show "le0 ((0, v) # R) 0 (j + 1)"
    using jR
  proof (induction j rule: less_induct)
    case (less j)
    let ?M = "(0, v) # R"
    have bound: "j + 1 < length ?M"
      using less.prems by simp
    have positive:
      "0 < entry ?M 0 (j + 1)"
    proof -
      have pair:
        "(entry R 0 j, entry R 1 j)
          \<in> set R"
        by (rule entry_pair_mem[
              OF less.prems])
      have okall:
        "\<forall>p\<in>set R. 0 < fst p"
        using ok unfolding argOK_def .
      have "0 < entry R 0 j"
        using okall pair by auto
      then show ?thesis
        using entry_cons[
          of "(0, v)" R 0 j]
        by simp
    qed
    have ex:
      "\<exists>k. k < j + 1 \<and>
        entry ?M 0 k <
          entry ?M 0 (j + 1)"
      using positive
      by (intro exI[of _ 0])
         (simp add: entry_def)
    have hp_iff:
      "hasParent ?M 0 (j + 1)
        \<longleftrightarrow>
       (\<exists>k. k < j + 1 \<and>
         entry ?M 0 k <
           entry ?M 0 (j + 1))"
      by (rule hasParent_zero_iff[
            OF bound])
    have hp: "hasParent ?M 0 (j + 1)"
      using hp_iff ex by blast
    then obtain k where rel:
      "nextR ?M 0 k (j + 1)"
      unfolding hasParent_def by blast
    have edge:
      "nextrel0 ?M k (j + 1)"
      using rel unfolding nextR_def
      by simp
    show ?case
    proof (cases "k = 0")
      case True
      have rt:
        "(nextrel0 ?M)\<^sup>*\<^sup>*
          0 (j + 1)"
        using edge True by simp
      show ?thesis
        unfolding le0_def
        using bound rt by simp
    next
      case False
      obtain k' where k: "k = k' + 1"
        using False by (cases k) auto
      have klt: "k' < j"
        using edge k
        unfolding nextrel0_def by simp
      have kR: "k' < length R"
        using klt less.prems by simp
      have prev:
        "le0 ?M 0 (k' + 1)"
        by (rule less.IH[OF klt kR])
      have rtprev:
        "(nextrel0 ?M)\<^sup>*\<^sup>*
          0 (k' + 1)"
        using prev unfolding le0_def
        by blast
      have rt:
        "(nextrel0 ?M)\<^sup>*\<^sup>*
          0 (j + 1)"
        by (rule rtranclp.rtrancl_into_rtrancl[
              OF rtprev])
           (use edge k in simp)
      show ?thesis
        unfolding le0_def
        using bound rt by simp
    qed
  qed
qed

lemma len_succ:
  assumes Rne: "R \<noteq> []"
  shows
    "length R = (length R - 1) + 1"
  using Rne by (cases R) simp_all

lemma entry_cons_last:
  assumes Rne: "R \<noteq> []"
  shows
    "entry (p # R) i (length R) =
      entry R i (length R - 1)"
  using entry_cons[
      of p R i "length R - 1"]
    len_succ[OF Rne]
  by simp

lemma le0_cons_last:
  assumes Rne: "R \<noteq> []"
  shows
    "le0 (p # R) (j + 1) (length R)
      \<longleftrightarrow>
     le0 R j (length R - 1)"
  using le0_cons[
      of p R j "length R - 1"]
    len_succ[OF Rne]
  by simp

lemma nextR_cons_last:
  assumes Rne: "R \<noteq> []"
  shows
    "nextR (p # R) i (j + 1) (length R)
      \<longleftrightarrow>
     nextR R i j (length R - 1)"
  using nextR_cons[
      of p R i j "length R - 1"]
    len_succ[OF Rne]
  by simp

lemma idx1_cons_last:
  assumes Rne: "R \<noteq> []"
  shows
    "idx1 (p # R) (length R) =
      idx1 R (length R - 1)"
  using idx1_cons[
      of p R "length R - 1"]
    len_succ[OF Rne]
  by simp

lemma cons_len_lt:
  "length R < length (p # R)"
  by simp

lemma hasParent_cons_one:
  assumes ok: "argOK R"
    and Rne: "R \<noteq> []"
    and parent_or:
      "hasParent R 1 (length R - 1)
       \<or>
       v < entry R 1 (length R - 1)"
  shows
    "hasParent ((0, v) # R) 1
      (length R)"
proof -
  have bound:
    "length R <
      length ((0, v) # R)"
    by simp
  have main_iff:
    "hasParent ((0, v) # R) 1
        (length R)
      \<longleftrightarrow>
     (\<exists>j0.
       r1cand ((0, v) # R)
        (length R) j0)"
    by (rule hasParent_one_iff[OF bound])
  show ?thesis
    using main_iff
  proof (rule iffD2)
    from parent_or show
      "\<exists>j0.
        r1cand ((0, v) # R)
          (length R) j0"
    proof
      assume hp:
        "hasParent R 1 (length R - 1)"
      have Rbound:
        "length R - 1 < length R"
        using Rne by simp
      have R_iff:
        "hasParent R 1 (length R - 1)
          \<longleftrightarrow>
         (\<exists>j0.
           r1cand R (length R - 1) j0)"
        by (rule hasParent_one_iff[
              OF Rbound])
      obtain j where cand:
        "r1cand R (length R - 1) j"
        using R_iff hp by blast
      have jl: "j < length R - 1"
        using cand
        unfolding r1cand_def by blast
      have lt: "j + 1 < length R"
        using jl by presburger
      have le:
        "le0 ((0, v) # R)
          (j + 1) (length R)"
        using cand le0_cons_last[
            OF Rne, of "(0, v)" j]
        unfolding r1cand_def by blast
      have row:
        "entry ((0, v) # R) 1 (j + 1) <
         entry ((0, v) # R) 1 (length R)"
      proof -
        have ej:
          "entry ((0, v) # R) 1 (j + 1) =
            entry R 1 j"
          by (rule entry_cons)
        have elast:
          "entry ((0, v) # R) 1
              (length R) =
            entry R 1 (length R - 1)"
          by (rule entry_cons_last[
                OF Rne])
        have strict:
          "entry R 1 j <
            entry R 1 (length R - 1)"
          using cand
          unfolding r1cand_def by blast
        show ?thesis
          using strict ej elast by simp
      qed
      show ?thesis
        unfolding r1cand_def
        using lt le row by blast
    next
      assume low:
        "v < entry R 1 (length R - 1)"
      have le:
        "le0 ((0, v) # R) 0 (length R)"
      proof -
        have raw:
          "le0 ((0, v) # R) 0
            ((length R - 1) + 1)"
          by (rule le0_cons_zero[
                OF ok, rule_format])
             (use Rne in simp)
        show ?thesis
          using raw len_succ[OF Rne]
          by simp
      qed
      have row:
        "entry ((0, v) # R) 1 0 <
         entry ((0, v) # R) 1 (length R)"
        using low entry_cons_last[
            OF Rne, of "(0, v)" 1]
        by (simp add: entry_def)
      show ?thesis
        unfolding r1cand_def
        by (rule exI[of _ 0])
           (use Rne le row in simp)
    qed
  qed
qed

lemma oper_root_tiling:
  assumes long:
      "length M - 1 \<noteq> 0"
    and nz:
      "\<not>
       (entry M 0 (length M - 1) = 0
        \<and>
        entry M 1 (length M - 1) = 0)"
    and hp:
      "hasParent M
        (idx1 M (length M - 1))
        (length M - 1)"
    and par:
      "parent M
        (idx1 M (length M - 1))
        (length M - 1) = 0"
  shows
    "oper M n =
      concat
        (map
          (\<lambda>k.
            map
              (\<lambda>p.
                (fst p +
                  k *
                    (if
                      0 <
                        idx1 M
                          (length M - 1)
                     then
                      entry M 0
                          (length M - 1) -
                      entry M 0 0
                     else 0),
                 snd p))
              (butlast M))
          [0..<n])"
proof -
  let ?d =
    "if 0 < idx1 M (length M - 1)
     then
       entry M 0 (length M - 1) -
       entry M 0 0
     else 0"
  have len:
    "length M - 1 \<le> length M"
    by simp
  have entries_take:
    "map
      (\<lambda>j. (entry M 0 j, entry M 1 j))
      [0..<length M - 1] =
     take (length M - 1) M"
    by (rule map_range_entry_eq_take[
          OF len])
  have entries:
    "map
      (\<lambda>j. (entry M 0 j, entry M 1 j))
      [0..<length M - 1] =
     butlast M"
    using entries_take
    by (simp add: butlast_conv_take)
  have raw:
    "oper M n =
      concat
        (map
          (\<lambda>k.
            map
              (\<lambda>j.
                (entry M 0 j + k * ?d,
                 entry M 1 j))
              [0..<length M - 1])
          [0..<n])"
    using oper_bad_unfold[
        OF long nz hp, of n]
      par
    by simp
  have blocks:
    "\<forall>k\<in>set [0..<n].
      map
        (\<lambda>j.
          (entry M 0 j + k * ?d,
           entry M 1 j))
        [0..<length M - 1] =
      map
        (\<lambda>p.
          (fst p + k * ?d, snd p))
        (butlast M)"
  proof (intro ballI)
    fix k
    show
      "map
        (\<lambda>j.
          (entry M 0 j + k * ?d,
           entry M 1 j))
        [0..<length M - 1] =
       map
        (\<lambda>p.
          (fst p + k * ?d, snd p))
        (butlast M)"
    proof -
      have mapped:
        "map
          (\<lambda>p.
            (fst p + k * ?d, snd p))
          (map
            (\<lambda>j.
              (entry M 0 j, entry M 1 j))
            [0..<length M - 1]) =
         map
          (\<lambda>p.
            (fst p + k * ?d, snd p))
          (butlast M)"
        using entries by simp
      show ?thesis
        using mapped
        by (simp add: map_map o_def)
    qed
  qed
  have outer:
    "map
      (\<lambda>k.
        map
          (\<lambda>j.
            (entry M 0 j + k * ?d,
             entry M 1 j))
          [0..<length M - 1])
      [0..<n] =
     map
      (\<lambda>k.
        map
          (\<lambda>p.
            (fst p + k * ?d, snd p))
          (butlast M))
      [0..<n]"
    by (rule map_cong)
       (use blocks in auto)
  show ?thesis
  proof -
    from raw have
      "oper M n =
        concat
          (map
            (\<lambda>k.
              map
                (\<lambda>j.
                  (entry M 0 j + k * ?d,
                   entry M 1 j))
                [0..<length M - 1])
            [0..<n])" .
    also have "... =
      concat
        (map
          (\<lambda>k.
            map
              (\<lambda>p.
                (fst p + k * ?d, snd p))
              (butlast M))
          [0..<n])"
      by (rule arg_cong[OF outer])
    finally show ?thesis .
  qed
qed

lemma oper_cons_nat:
  assumes ok: "argOK R"
    and Rne: "R \<noteq> []"
    and hp:
      "hasParent R
        (idx1 R (length R - 1))
        (length R - 1)"
  shows
    "oper ((0, v) # R) n =
      (0, v) # oper R n"
proof -
  let ?i = "idx1 R (length R - 1)"
  let ?r =
    "parent R ?i (length R - 1)"
  let ?M = "(0, v) # R"
  have nrR:
    "nextR R ?i ?r (length R - 1)"
    by (rule parent_nextR[OF hp])
  have rlt:
    "?r < length R - 1"
    by (rule nextR_index_lt[OF nrR])
  have longR:
    "length R - 1 \<noteq> 0"
    using rlt by simp
  have lastR:
    "length R - 1 < length R"
    using Rne by simp
  have pair:
    "(entry R 0 (length R - 1),
      entry R 1 (length R - 1))
      \<in> set R"
    by (rule entry_pair_mem[OF lastR])
  have xpos:
    "0 < entry R 0 (length R - 1)"
    using ok pair
    unfolding argOK_def by auto
  have nzR:
    "\<not>
      (entry R 0 (length R - 1) = 0
       \<and>
       entry R 1 (length R - 1) = 0)"
    using xpos by auto
  have lastM:
    "length ?M - 1 = length R"
    by simp
  have e0:
    "entry ?M 0 (length R) =
      entry R 0 (length R - 1)"
    by (rule entry_cons_last[OF Rne])
  have e1:
    "entry ?M 1 (length R) =
      entry R 1 (length R - 1)"
    by (rule entry_cons_last[OF Rne])
  have longM:
    "length ?M - 1 \<noteq> 0"
    using Rne by simp
  have nzM:
    "\<not>
      (entry ?M 0 (length ?M - 1) = 0
       \<and>
       entry ?M 1 (length ?M - 1) = 0)"
    using lastM e0 xpos by auto
  have idxM:
    "idx1 ?M (length ?M - 1) = ?i"
    using lastM idx1_cons_last[
        OF Rne, of "(0, v)"]
    by simp
  have noroot:
    "\<not> nextR ?M ?i 0 (length R)"
  proof
    assume root:
      "nextR ?M ?i 0 (length R)"
    show False
    proof (cases "?i = 0")
      case i0: True
      have root0:
        "nextrel0 ?M 0 (length R)"
        using root i0
        unfolding nextR_def by simp
      have nr0:
        "nextrel0 R ?r (length R - 1)"
        using nrR i0
        unfolding nextR_def by simp
      have between:
        "0 < ?r + 1 \<and>
          ?r + 1 < length R"
        using rlt by simp
      have allv:
        "\<forall>j.
          0 < j \<and> j < length R
          \<longrightarrow>
          entry ?M 0 (length R)
            \<le> entry ?M 0 j"
        using root0
        unfolding nextrel0_def by auto
      have valley:
        "entry ?M 0 (length R)
          \<le> entry ?M 0 (?r + 1)"
        by (rule allv[rule_format,
              OF between])
      have strict:
        "entry R 0 ?r <
          entry R 0 (length R - 1)"
        using nr0
        unfolding nextrel0_def by blast
      have er:
        "entry ?M 0 (?r + 1) =
          entry R 0 ?r"
        by (rule entry_cons)
      show False
        using valley strict e0 er by simp
    next
      case inot: False
      have root1:
        "nextrel1 ?M 0 (length R)"
        using root inot
        unfolding nextR_def by simp
      have nr1:
        "nextrel1 R ?r (length R - 1)"
        using nrR inot
        unfolding nextR_def by simp
      have ler:
        "le0 ?M (?r + 1) (length R)"
        using le0_cons_last[
            OF Rne, of "(0, v)" ?r]
          nr1
        unfolding nextrel1_def by blast
      have between:
        "0 < ?r + 1 \<and>
          le0 ?M (?r + 1) (length R)"
        using ler by simp
      have allv:
        "\<forall>j.
          0 < j \<and>
          le0 ?M j (length R)
          \<longrightarrow>
          entry ?M 1 (length R)
            \<le> entry ?M 1 j"
        using root1
        unfolding nextrel1_def by auto
      have valley:
        "entry ?M 1 (length R)
          \<le> entry ?M 1 (?r + 1)"
        by (rule allv[rule_format,
              OF between])
      have strict:
        "entry R 1 ?r <
          entry R 1 (length R - 1)"
        using nr1
        unfolding nextrel1_def by blast
      have er:
        "entry ?M 1 (?r + 1) =
          entry R 1 ?r"
        by (rule entry_cons)
      show False
        using valley strict e1 er by simp
    qed
  qed
  have uniqR:
    "\<forall>y. nextR R ?i y
        (length R - 1)
      \<longrightarrow> y = ?r"
    using hp nrR
    unfolding hasParent_def by blast
  have uniqM:
    "\<forall>y. nextR ?M ?i y
        (length R)
      \<longrightarrow> y = ?r + 1"
  proof (intro allI impI)
    fix y
    assume yrel:
      "nextR ?M ?i y (length R)"
    show "y = ?r + 1"
    proof (cases "y = 0")
      case True
      then show ?thesis
        using yrel noroot by blast
    next
      case False
      obtain y' where y: "y = y' + 1"
        using False by (cases y) auto
      have yR:
        "nextR R ?i y' (length R - 1)"
        using nextR_cons_last[
            OF Rne, of "(0, v)" ?i y']
          yrel y by simp
      have "y' = ?r"
        by (rule uniqR[rule_format, OF yR])
      then show ?thesis using y by simp
    qed
  qed
  have nrM:
    "nextR ?M ?i (?r + 1) (length R)"
    using nextR_cons_last[
        OF Rne, of "(0, v)" ?i ?r]
      nrR by simp
  have hpM0:
    "hasParent ?M ?i (length R)"
    unfolding hasParent_def
  proof (rule ex1I[of _ "?r + 1"])
    show "nextR ?M ?i (?r + 1) (length R)"
      by (rule nrM)
    fix y
    assume
      "nextR ?M ?i y (length R)"
    then show "y = ?r + 1"
      by (rule uniqM[rule_format])
  qed
  have hpM:
    "hasParent ?M
      (idx1 ?M (length ?M - 1))
      (length ?M - 1)"
    using idxM lastM hpM0 by simp
  have parM:
    "parent ?M
      (idx1 ?M (length ?M - 1))
      (length ?M - 1) = ?r + 1"
  proof -
    have chosen:
      "nextR ?M ?i
        (parent ?M ?i (length R))
        (length R)"
      using hpM idxM lastM
      by (simp add: parent_nextR)
    show ?thesis
      using uniqM chosen idxM lastM
      by simp
  qed
  have idxM0:
    "idx1 ?M (length R) = ?i"
    using idxM lastM by simp
  have parM0:
    "parent ?M ?i (length R) =
      ?r + 1"
    using parM idxM lastM by simp
  have lastSuc:
    "Suc (length R - 1) = length R"
    using Rne by (cases R) simp_all
  have ranges0:
    "map Suc [?r..<length R - 1] =
      [Suc ?r..<Suc (length R - 1)]"
    by (rule map_Suc_upt)
  have ranges1:
    "map Suc [?r..<length R - 1] =
      [?r + 1..<length R]"
    using ranges0 lastSuc
    by (metis Suc_eq_plus1)
  have ranges:
    "[?r + 1..<length R] =
      map Suc [?r..<length R - 1]"
    by (rule sym[OF ranges1])
  note opM =
    oper_bad_unfold[
      OF longM nzM hpM, of n]
  note opR =
    oper_bad_unfold[
      OF longR nzR hp, of n]
  have er0:
    "entry ?M 0 (?r + 1) =
      entry R 0 ?r"
    by (rule entry_cons)
  have delta:
    "(if
       0 < idx1 ?M (length ?M - 1)
      then
       entry ?M 0 (length ?M - 1) -
       entry ?M 0
        (parent ?M
          (idx1 ?M (length ?M - 1))
          (length ?M - 1))
      else 0) =
     (if 0 < ?i
      then
       entry R 0 (length R - 1) -
       entry R 0 ?r
      else 0)"
    using idxM lastM parM e0 er0
    by simp
  have block:
    "\<forall>k\<in>set [0..<n].
      map
        (\<lambda>j.
          (entry ?M 0 j +
            k *
             (if
               0 <
                idx1 ?M (length ?M - 1)
              then
               entry ?M 0 (length ?M - 1) -
               entry ?M 0
                (parent ?M
                  (idx1 ?M (length ?M - 1))
                  (length ?M - 1))
              else 0),
           entry ?M 1 j))
        [?r + 1..<length R] =
      map
        (\<lambda>j.
          (entry R 0 j +
            k *
             (if 0 < ?i
              then
               entry R 0 (length R - 1) -
               entry R 0 ?r
              else 0),
           entry R 1 j))
        [?r..<length R - 1]"
  proof (intro ballI)
    fix k
    have mapped:
      "map
        (\<lambda>j.
          (entry ?M 0 j +
            k *
             (if
               0 <
                idx1 ?M (length ?M - 1)
              then
               entry ?M 0 (length ?M - 1) -
               entry ?M 0
                (parent ?M
                  (idx1 ?M (length ?M - 1))
                  (length ?M - 1))
              else 0),
           entry ?M 1 j))
        (map Suc
          [?r..<length R - 1]) =
       map
        (\<lambda>j.
          (entry R 0 j +
            k *
             (if 0 < ?i
              then
               entry R 0 (length R - 1) -
               entry R 0 ?r
              else 0),
           entry R 1 j))
        [?r..<length R - 1]"
      apply (simp only: map_map o_def)
      apply (rule map_cong)
       apply simp
      subgoal for j
      proof -
        have ej0:
          "entry ?M 0 (Suc j) =
            entry R 0 j"
          using entry_cons[
            of "(0, v)" R 0 j]
          by simp
        have ej1:
          "entry ?M 1 (Suc j) =
            entry R 1 j"
          using entry_cons[
            of "(0, v)" R 1 j]
          by simp
        show ?thesis
          using delta ej0 ej1 by simp
      qed
      done
    show
      "map
        (\<lambda>j.
          (entry ?M 0 j +
            k *
             (if
               0 <
                idx1 ?M (length ?M - 1)
              then
               entry ?M 0 (length ?M - 1) -
               entry ?M 0
                (parent ?M
                  (idx1 ?M (length ?M - 1))
                  (length ?M - 1))
              else 0),
           entry ?M 1 j))
        [?r + 1..<length R] =
       map
        (\<lambda>j.
          (entry R 0 j +
            k *
             (if 0 < ?i
              then
               entry R 0 (length R - 1) -
               entry R 0 ?r
              else 0),
           entry R 1 j))
        [?r..<length R - 1]"
      using mapped ranges by simp
  qed
  have outer:
    "map
      (\<lambda>k.
        map
          (\<lambda>j.
            (entry ?M 0 j +
              k *
               (if
                 0 <
                  idx1 ?M (length ?M - 1)
                then
                 entry ?M 0 (length ?M - 1) -
                 entry ?M 0
                  (parent ?M
                    (idx1 ?M (length ?M - 1))
                    (length ?M - 1))
                else 0),
             entry ?M 1 j))
          [?r + 1..<length R])
      [0..<n] =
     map
      (\<lambda>k.
        map
          (\<lambda>j.
            (entry R 0 j +
              k *
               (if 0 < ?i
                then
                 entry R 0 (length R - 1) -
                 entry R 0 ?r
                else 0),
             entry R 1 j))
          [?r..<length R - 1])
      [0..<n]"
    by (rule map_cong)
       (use block in auto)
  have prefix:
    "take (?r + 1) ?M =
      (0, v) # take ?r R"
    by simp
  note opM0 =
    opM[unfolded lastM idxM0 parM0]
  have concat_eq:
    "concat
      (map
        (\<lambda>k.
          map
            (\<lambda>j.
              (entry ?M 0 j +
                k *
                 (if
                   0 <
                    idx1 ?M (length ?M - 1)
                  then
                   entry ?M 0 (length ?M - 1) -
                   entry ?M 0
                    (parent ?M
                      (idx1 ?M (length ?M - 1))
                      (length ?M - 1))
                  else 0),
               entry ?M 1 j))
            [?r + 1..<length R])
        [0..<n]) =
     concat
      (map
        (\<lambda>k.
          map
            (\<lambda>j.
              (entry R 0 j +
                k *
                 (if 0 < ?i
                  then
                   entry R 0 (length R - 1) -
                   entry R 0 ?r
                  else 0),
               entry R 1 j))
            [?r..<length R - 1])
        [0..<n])"
    by (rule arg_cong[OF outer])
  note concat_eq0 =
    concat_eq[unfolded lastM idxM0 parM0]
  have normM:
    "oper ?M n =
      (0, v) #
       (take ?r R @
        concat
          (map
            (\<lambda>k.
              map
                (\<lambda>j.
                  (entry R 0 j +
                    k *
                     (if 0 < ?i
                      then
                       entry R 0
                         (length R - 1) -
                       entry R 0 ?r
                      else 0),
                   entry R 1 j))
                [?r..<length R - 1])
            [0..<n]))"
    using opM0
    by (simp only: prefix concat_eq0
          append_Cons)
  show ?thesis
    using normM opR by simp
qed

lemma oper_cons_succ:
  assumes ok: "argOK R"
    and Rne: "R \<noteq> []"
    and row: "entry R 1 (length R - 1) = 0"
    and nop:
      "\<not> hasParent R 0 (length R - 1)"
  shows
    "oper ((0, v) # R) n =
      concat
        (map
          (\<lambda>_. (0, v) # butlast R)
          [0..<n])"
proof -
  let ?M = "(0, v) # R"
  have lastR:
    "length R - 1 < length R"
    using Rne by simp
  have pair:
    "(entry R 0 (length R - 1),
      entry R 1 (length R - 1))
      \<in> set R"
    by (rule entry_pair_mem[OF lastR])
  have xpos:
    "0 < entry R 0 (length R - 1)"
    using ok pair
    unfolding argOK_def by auto
  have lastM:
    "length ?M - 1 = length R"
    by simp
  have e0:
    "entry ?M 0 (length R) =
      entry R 0 (length R - 1)"
    by (rule entry_cons_last[OF Rne])
  have longM:
    "length ?M - 1 \<noteq> 0"
    using Rne by simp
  have nzM:
    "\<not>
      (entry ?M 0 (length ?M - 1) = 0
       \<and>
       entry ?M 1 (length ?M - 1) = 0)"
    using lastM e0 xpos by auto
  have idx:
    "idx1 ?M (length ?M - 1) = 0"
    using lastM idx1_cons_last[
        OF Rne, of "(0, v)"]
      row
    unfolding idx1_def by simp
  have allge:
    "\<forall>k. k < length R - 1
      \<longrightarrow>
      entry R 0 (length R - 1)
        \<le> entry R 0 k"
  proof (intro allI impI)
    fix k
    assume klt: "k < length R - 1"
    show
      "entry R 0 (length R - 1)
        \<le> entry R 0 k"
    proof (rule ccontr)
      assume notle:
        "\<not> entry R 0 (length R - 1)
          \<le> entry R 0 k"
      have ex:
        "\<exists>j. j < length R - 1
          \<and>
          entry R 0 j <
            entry R 0 (length R - 1)"
        using klt notle by auto
      have iff:
        "hasParent R 0 (length R - 1)
          \<longleftrightarrow>
         (\<exists>j. j < length R - 1
           \<and>
           entry R 0 j <
             entry R 0 (length R - 1))"
        by (rule hasParent_zero_iff[
              OF lastR])
      show False using nop iff ex by blast
    qed
  qed
  have root_edge:
    "nextrel0 ?M 0 (length R)"
    unfolding nextrel0_def
  proof (intro conjI)
    show "0 < length ?M" by simp
    show "length R < length ?M" by simp
    show "0 < length R"
      using Rne by simp
    show
      "entry ?M 0 0 <
        entry ?M 0 (length R)"
      using xpos e0
      by (simp add: entry_def)
    show
      "\<forall>j. 0 < j \<and> j < length R
        \<longrightarrow>
        entry ?M 0 (length R)
          \<le> entry ?M 0 j"
    proof (intro allI impI)
      fix j
      assume j:
        "0 < j \<and> j < length R"
      obtain k where jk: "j = k + 1"
        using j by (cases j) auto
      have klt: "k < length R - 1"
        using j jk by presburger
      have ej:
        "entry ?M 0 j = entry R 0 k"
        using entry_cons[
            of "(0, v)" R 0 k]
          jk by simp
      show
        "entry ?M 0 (length R)
          \<le> entry ?M 0 j"
        using allge[rule_format, OF klt]
          e0 ej by simp
    qed
  qed
  have uniq:
    "\<forall>y. nextR ?M 0 y (length R)
      \<longrightarrow> y = 0"
  proof (intro allI impI)
    fix y
    assume rel:
      "nextR ?M 0 y (length R)"
    show "y = 0"
    proof (rule ccontr)
      assume "y \<noteq> 0"
      obtain k where y: "y = k + 1"
        using \<open>y \<noteq> 0\<close>
        by (cases y) auto
      have relR:
        "nextR R 0 k (length R - 1)"
        using nextR_cons_last[
            OF Rne, of "(0, v)" 0 k]
          rel y by simp
      have n0:
        "nextrel0 R k (length R - 1)"
        using relR unfolding nextR_def
        by simp
      have ge:
        "entry R 0 (length R - 1)
          \<le> entry R 0 k"
        using allge n0
        unfolding nextrel0_def by blast
      have lt:
        "entry R 0 k <
          entry R 0 (length R - 1)"
        using n0
        unfolding nextrel0_def by blast
      show False using ge lt by simp
    qed
  qed
  have nr:
    "nextR ?M 0 0 (length R)"
    using root_edge
    unfolding nextR_def by simp
  have hp0:
    "hasParent ?M 0 (length R)"
    unfolding hasParent_def
  proof (rule ex1I[of _ 0])
    show "nextR ?M 0 0 (length R)"
      by (rule nr)
    fix y
    assume "nextR ?M 0 y (length R)"
    then show "y = 0"
      by (rule uniq[rule_format])
  qed
  have hp:
    "hasParent ?M
      (idx1 ?M (length ?M - 1))
      (length ?M - 1)"
    using idx lastM hp0 by simp
  have par:
    "parent ?M
      (idx1 ?M (length ?M - 1))
      (length ?M - 1) = 0"
  proof -
    have chosen:
      "nextR ?M 0
        (parent ?M 0 (length R))
        (length R)"
      by (rule parent_nextR[OF hp0])
    have "parent ?M 0 (length R) = 0"
      by (rule uniq[rule_format, OF chosen])
    then show ?thesis using idx lastM
      by simp
  qed
  have tail:
    "butlast ?M = (0, v) # butlast R"
    using Rne by (cases R) simp_all
  have tiled:
    "oper ?M n =
      concat
        (map
          (\<lambda>k.
            map
              (\<lambda>p.
                (fst p +
                  k *
                   (if
                     0 <
                      idx1 ?M
                        (length ?M - 1)
                    then
                     entry ?M 0
                         (length ?M - 1) -
                     entry ?M 0 0
                    else 0),
                 snd p))
              (butlast ?M))
          [0..<n])"
    by (rule oper_root_tiling[
          OF longM nzM hp par])
  show ?thesis
    using tiled idx tail
    by simp
qed

lemma oper_cons_tower:
  assumes ok: "argOK R"
    and dom: "domT R m"
    and vm: "v \<le> m"
  shows
    "oper ((0, v) # R) n =
      tow v R n"
proof -
  let ?M = "(0, v) # R"
  have Rne: "R \<noteq> []"
    using dom not_domT_nil[
      of m] by blast
  have lastR:
    "length R - 1 < length R"
    using Rne by simp
  have pair:
    "(entry R 0 (length R - 1),
      entry R 1 (length R - 1))
      \<in> set R"
    by (rule entry_pair_mem[OF lastR])
  have xpos:
    "0 < entry R 0 (length R - 1)"
    using ok pair
    unfolding argOK_def by auto
  have row:
    "entry R 1 (length R - 1) =
      m + 1"
    using dom unfolding domT_def by blast
  have lastM:
    "length ?M - 1 = length R"
    by simp
  have e0:
    "entry ?M 0 (length R) =
      entry R 0 (length R - 1)"
    by (rule entry_cons_last[OF Rne])
  have longM:
    "length ?M - 1 \<noteq> 0"
    using Rne by simp
  have nzM:
    "\<not>
      (entry ?M 0 (length ?M - 1) = 0
       \<and>
       entry ?M 1 (length ?M - 1) = 0)"
    using lastM e0 xpos by auto
  have idx:
    "idx1 ?M (length ?M - 1) = 1"
    using lastM idx1_cons_last[
        OF Rne, of "(0, v)"]
      row
    unfolding idx1_def by simp
  have uniq:
    "\<forall>y. nextR ?M 1 y (length R)
      \<longrightarrow> y = 0"
  proof (intro allI impI)
    fix y
    assume rel:
      "nextR ?M 1 y (length R)"
    show "y = 0"
    proof (rule ccontr)
      assume "y \<noteq> 0"
      obtain k where y: "y = k + 1"
        using \<open>y \<noteq> 0\<close>
        by (cases y) auto
      have relR:
        "nextR R 1 k (length R - 1)"
        using nextR_cons_last[
            OF Rne, of "(0, v)" 1 k]
          rel y by simp
      have n1:
        "nextrel1 R k (length R - 1)"
        using relR unfolding nextR_def
        by simp
      have cand:
        "r1cand R (length R - 1) k"
        using n1
        unfolding nextrel1_def
          r1cand_def by blast
      have iff:
        "hasParent R 1 (length R - 1)
          \<longleftrightarrow>
         (\<exists>j.
           r1cand R (length R - 1) j)"
        by (rule hasParent_one_iff[
              OF lastR])
      have "hasParent R 1 (length R - 1)"
        using iff cand by blast
      then show False
        using dom unfolding domT_def by blast
    qed
  qed
  have low:
    "v < entry R 1 (length R - 1)"
    using row vm by simp
  have hp1:
    "hasParent ?M 1 (length R)"
    by (rule hasParent_cons_one[
          OF ok Rne])
       (rule disjI2[OF low])
  have hp:
    "hasParent ?M
      (idx1 ?M (length ?M - 1))
      (length ?M - 1)"
    using hp1 idx lastM by simp
  have par:
    "parent ?M
      (idx1 ?M (length ?M - 1))
      (length ?M - 1) = 0"
  proof -
    have chosen:
      "nextR ?M 1
        (parent ?M 1 (length R))
        (length R)"
      by (rule parent_nextR[OF hp1])
    have "parent ?M 1 (length R) = 0"
      by (rule uniq[rule_format, OF chosen])
    then show ?thesis
      using idx lastM by simp
  qed
  have tail:
    "butlast ?M =
      (0, v) # butlast R"
    using Rne by (cases R) simp_all
  have root0:
    "entry ?M 0 0 = 0"
    by (simp add: entry_def)
  have tiled0:
    "oper ?M n =
      concat
        (map
          (\<lambda>k.
            map
              (\<lambda>p.
                (fst p +
                  k *
                    (entry R 0
                      (length R - 1)),
                 snd p))
              ((0, v) # butlast R))
          [0..<n])"
  proof -
    have raw:
      "oper ?M n =
        concat
          (map
            (\<lambda>k.
              map
                (\<lambda>p.
                  (fst p +
                    k *
                     (if
                       0 <
                        idx1 ?M
                          (length ?M - 1)
                      then
                       entry ?M 0
                           (length ?M - 1) -
                       entry ?M 0 0
                      else 0),
                   snd p))
                (butlast ?M))
            [0..<n])"
      by (rule oper_root_tiling[
            OF longM nzM hp par])
    show ?thesis
      using raw idx lastM e0
        root0 tail by simp
  qed
  let ?x =
    "entry R 0 (length R - 1)"
  let ?D = "(0, v) # butlast R"
  have tiles:
    "\<forall>q.
      concat
        (map
          (\<lambda>k.
            map
              (\<lambda>p.
                (fst p + k * ?x, snd p))
              ?D)
          [0..<q]) =
      tow v R q"
  proof
    fix q
    show
      "concat
        (map
          (\<lambda>k.
            map
              (\<lambda>p.
                (fst p + k * ?x, snd p))
              ?D)
          [0..<q]) =
       tow v R q"
    proof (induction q)
      case 0
      show ?case by simp
    next
      case (Suc q)
      have upt:
        "[0..<Suc q] =
          0 # map Suc [0..<q]"
        using map_upt_Suc[
          of "\<lambda>x. x" q]
        by simp
      let ?sh =
        "\<lambda>p.
          (fst p + ?x, snd p)"
      have shifted:
        "map ?sh
          (concat
            (map
              (\<lambda>k.
                map
                  (\<lambda>p.
                    (fst p + k * ?x,
                     snd p))
                  ?D)
              [0..<q])) =
         concat
          (map
            (\<lambda>k.
              map
                (\<lambda>p.
                  (fst p +
                    Suc k * ?x,
                   snd p))
                ?D)
            [0..<q])"
        by (simp add: map_concat
              map_map o_def
              add.assoc
              add.commute
              add.left_commute)
      have graft:
        "?D @ map ?sh (tow v R q) =
          (0, v) #
            graft R (tow v R q)"
        unfolding graft_def
        by simp
      have comps:
        "map
          ((\<lambda>k.
            map
              (\<lambda>p.
                (fst p + k * ?x,
                 snd p))
              ?D) \<circ> Suc)
          [0..<q] =
         map
          (\<lambda>k.
            map
              (\<lambda>p.
                (fst p + Suc k * ?x,
                 snd p))
              ?D)
          [0..<q]"
        by (simp add: o_def)
      have rest:
        "concat
          (map
            (\<lambda>k.
              map
                (\<lambda>p.
                  (fst p + Suc k * ?x,
                   snd p))
                ?D)
            [0..<q]) =
         map ?sh (tow v R q)"
        using shifted Suc.IH by simp
      have comp_concat:
        "concat
          (map
            ((\<lambda>k.
              map
                (\<lambda>p.
                  (fst p + k * ?x,
                   snd p))
                ?D) \<circ> Suc)
            [0..<q]) =
         concat
          (map
            (\<lambda>k.
              map
                (\<lambda>p.
                  (fst p + Suc k * ?x,
                   snd p))
                ?D)
            [0..<q])"
        by (rule arg_cong[OF comps])
      have rest_comp:
        "concat
          (map
            ((\<lambda>k.
              map
                (\<lambda>p.
                  (fst p + k * ?x,
                   snd p))
                ?D) \<circ> Suc)
            [0..<q]) =
         map ?sh (tow v R q)"
        using comp_concat rest by simp
      show ?case
        using upt rest_comp graft
        by simp
    qed
  qed
  show ?thesis
    using tiled0 tiles[rule_format,
      of n] by simp
qed

lemma domT_cons_of_lt:
  assumes ok: "argOK R"
    and dom: "domT R m"
    and mv: "m < v"
  shows
    "domT ((0, v) # R) m"
proof -
  have Rne: "R \<noteq> []"
    using dom not_domT_nil[
      of m] by blast
  have last:
    "length ((0, v) # R) - 1 =
      length R"
    by simp
  have entry:
    "entry ((0, v) # R) 1 (length R) =
      entry R 1 (length R - 1)"
    by (rule entry_cons_last[OF Rne])
  have rowval:
    "entry R 1 (length R - 1) =
      m + 1"
    using dom unfolding domT_def by blast
  have nop:
    "\<not> hasParent ((0, v) # R) 1
      (length R)"
  proof
    assume hp:
      "hasParent ((0, v) # R) 1
        (length R)"
    have bound:
      "length R <
        length ((0, v) # R)"
      by simp
    have iff:
      "hasParent ((0, v) # R) 1
          (length R)
        \<longleftrightarrow>
       (\<exists>j.
         r1cand ((0, v) # R)
          (length R) j)"
      by (rule hasParent_one_iff[
            OF bound])
    obtain j where cand:
      "r1cand ((0, v) # R)
        (length R) j"
      using iff hp by blast
    show False
    proof (cases "j = 0")
      case True
      have strictj:
        "entry ((0, v) # R) 1 j <
          entry ((0, v) # R) 1
            (length R)"
        using cand
        unfolding r1cand_def by blast
      have strict:
        "entry ((0, v) # R) 1 0 <
          entry ((0, v) # R) 1
            (length R)"
        using strictj True by simp
      show False
        using strict entry rowval mv True
        by (simp add: entry_def)
    next
      case False
      obtain k where j: "j = k + 1"
        using False by (cases j) auto
      have le:
        "le0 R k (length R - 1)"
        using cand le0_cons_last[
            OF Rne, of "(0, v)" k]
          j
        unfolding r1cand_def by blast
      have strict:
        "entry R 1 k <
          entry R 1 (length R - 1)"
        using cand entry_cons[
            of "(0, v)" R 1 k]
          entry j
        unfolding r1cand_def by auto
      have klt: "k < length R - 1"
        using cand j
        unfolding r1cand_def
        by (simp add: less_diff_conv)
      have candR:
        "r1cand R (length R - 1) k"
        unfolding r1cand_def
        using klt le strict by blast
      have Rbound:
        "length R - 1 < length R"
        using Rne by simp
      have Riff:
        "hasParent R 1 (length R - 1)
          \<longleftrightarrow>
         (\<exists>j.
           r1cand R (length R - 1) j)"
        by (rule hasParent_one_iff[
              OF Rbound])
      have "hasParent R 1 (length R - 1)"
        using Riff candR by blast
      then show False
        using dom unfolding domT_def by blast
    qed
  qed
  show ?thesis
    unfolding domT_def
    using last entry rowval nop by simp
qed

lemma argOK_oper:
  assumes ok: "argOK R"
  shows "argOK (oper R n)"
proof -
  have ge0:
    "\<forall>p\<in>set R. 1 \<le> fst p"
    using ok unfolding argOK_def
    by auto
  have ge:
    "\<forall>p\<in>set (oper R n).
      1 \<le> fst p"
    by (rule oper_mem_ge[OF ge0])
  show ?thesis
    using ge unfolding argOK_def
    by auto
qed

lemma argOK_graft:
  assumes Rne: "R \<noteq> []"
    and ok: "argOK R"
  shows "argOK (graft R z)"
proof -
  have ge0:
    "\<forall>p\<in>set R. 1 \<le> fst p"
    using ok unfolding argOK_def
    by auto
  have ge:
    "\<forall>p\<in>set (graft R z).
      1 \<le> fst p"
    by (rule graft_mem_ge[OF Rne ge0])
  show ?thesis
    using ge unfolding argOK_def
    by auto
qed

lemma argOK_dropLast:
  assumes ok: "argOK R"
  shows "argOK (butlast R)"
  using ok
  unfolding argOK_def
  by (auto dest: in_set_butlastD)

lemma based_cons:
  "based ((0, v) # R)"
  unfolding based_def entry_def
  by simp

lemma rsum_self_cons:
  "\<forall>p\<in>set ((0, v) # R).
    entry ((0, v) # R) 0 0
      \<le> fst p"
  unfolding entry_def
  by simp

lemma W_flatMap_copies:
  assumes QW: "Q \<in> W u"
    and rooted:
      "\<forall>p\<in>set Q.
        entry Q 0 0 \<le> fst p"
  shows
    "\<forall>n.
      concat (map (\<lambda>_. Q) [0..<n])
        \<in> W u"
proof (intro allI)
  fix n
  show
    "concat (map (\<lambda>_. Q) [0..<n])
      \<in> W u"
  proof (induction n)
    case 0
    show ?case by (simp add: W_nil)
  next
    case (Suc n)
    have upt:
      "[0..<Suc n] = [0..<n] @ [n]"
      by (rule upt_Suc_append) simp
    have rs:
      "rsum
        (concat (map (\<lambda>_. Q) [0..<n]))
        Q"
      unfolding rsum_def
      using rooted by auto
    show ?case
      using W_add[
          OF Suc.IH QW rs]
        upt by simp
  qed
qed

lemma Wstar_closed:
  "\<forall>u R.
    Aop W u Wstar R
      \<longrightarrow> R \<in> Wstar"
proof (intro allI impI)
  fix u R
  assume AR: "Aop W u Wstar R"
  show "R \<in> Wstar"
    unfolding Wstar_def mem_Collect_eq
  proof (intro impI allI)
    assume ok: "argOK R"
    fix v
    show "(0, v) # R \<in> W v"
    proof (cases "R = []")
      case True
      then show ?thesis
        using Om_mem_W[of v] by simp
    next
      case Rne: False
      let ?M = "(0, v) # R"
      have last:
        "length ?M - 1 = length R"
        by simp
      have e1:
        "entry ?M 1 (length ?M - 1) =
          entry R 1 (length R - 1)"
        using last entry_cons_last[
            OF Rne, of "(0, v)" 1]
        by simp
      have nat_iff:
        "natDom ?M
          \<longleftrightarrow>
         entry ?M 1 (length ?M - 1) = 0
          \<or>
         hasParent ?M 1 (length ?M - 1)"
        by (rule natDom_iff)
      have nat_parent:
        "hasParent ?M 1 (length R)
          \<longrightarrow> natDom ?M"
      proof (intro impI)
        assume hp:
          "hasParent ?M 1 (length R)"
        show "natDom ?M"
        proof (rule nat_iff[THEN iffD2],
            rule disjI2)
          show
            "hasParent ?M 1
              (length ?M - 1)"
            using hp last by simp
        qed
      qed
      have nat_zero:
        "entry R 1 (length R - 1) = 0
          \<longrightarrow> natDom ?M"
      proof (intro impI)
        assume zero:
          "entry R 1 (length R - 1) = 0"
        show "natDom ?M"
        proof (rule nat_iff[THEN iffD2],
            rule disjI1)
          show
            "entry ?M 1
              (length ?M - 1) = 0"
            using zero e1 by simp
        qed
      qed
      have branches:
        "(length R \<le> 1 \<and>
            entry R 1 0 = 0) \<or>
         (natDom R \<and>
            (\<forall>n. 1 \<le> n
              \<longrightarrow> oper R n \<in> Wstar)) \<or>
         (\<exists>m<u.
            domT R m \<and>
            (\<forall>z\<in>W m.
              based z \<longrightarrow>
              graft R z \<in> Wstar))"
        using AR unfolding Aop_def by blast
      from branches show ?thesis
      proof
        assume base:
          "length R \<le> 1 \<and>
            entry R 1 0 = 0"
        have len1: "length R = 1"
          using base Rne by (cases R) auto
        have row0:
          "entry R 1 (length R - 1) = 0"
          using base len1 by simp
        have nop:
          "\<not> hasParent R 0
            (length R - 1)"
          using len1 no_hasParent_at_zero[
              where M=R and i=0]
          by simp
        obtain q where R_single: "R = [q]"
          using len1 by (cases R) auto
        have tail: "butlast R = []"
          using R_single by simp
        have ops:
          "\<forall>n. 1 \<le> n
            \<longrightarrow> oper ?M n \<in> W v"
        proof (intro allI impI)
          fix n :: nat
          assume "1 \<le> n"
          have op:
            "oper ?M n =
              concat
                (map
                  (\<lambda>_. (0, v) # butlast R)
                  [0..<n])"
            by (rule oper_cons_succ[
                  OF ok Rne row0 nop])
          have copies:
            "concat
              (map
                (\<lambda>_. [(0, v)])
                [0..<n]) \<in> W v"
          proof -
            have root:
              "\<forall>p\<in>set ([(0, v)]).
                entry [(0, v)] 0 0
                  \<le> fst p"
              by (rule rsum_self_cons)
            note all =
              W_flatMap_copies[
                OF Om_mem_W root]
            show ?thesis
              by (rule all[rule_format])
          qed
          show "oper ?M n \<in> W v"
            using op copies tail by simp
        qed
        show ?thesis
          by (rule A1_intro)
             (use nat_zero[rule_format,
                 OF row0] ops in
               \<open>auto simp: Aop_def\<close>)
      next
        assume rest:
          "(natDom R \<and>
              (\<forall>n. 1 \<le> n
                \<longrightarrow>
                oper R n \<in> Wstar)) \<or>
           (\<exists>m<u.
              domT R m \<and>
              (\<forall>z\<in>W m.
                based z \<longrightarrow>
                graft R z \<in> Wstar))"
        from rest show ?thesis
        proof
          assume nat:
            "natDom R \<and>
              (\<forall>n. 1 \<le> n
                \<longrightarrow>
                oper R n \<in> Wstar)"
          show ?thesis
          proof (cases
            "hasParent R
              (idx1 R (length R - 1))
              (length R - 1)")
            case hp: True
            have natM: "natDom ?M"
            proof (cases
              "entry R 1 (length R - 1) = 0")
              case True
              show ?thesis
                by (rule nat_zero[
                      rule_format, OF True])
            next
              case False
              have idx:
                "idx1 R (length R - 1) = 1"
                using False
                unfolding idx1_def by simp
              have parent1:
                "hasParent R 1
                  (length R - 1)"
                using hp idx by simp
              have hpM:
                "hasParent ?M 1 (length R)"
                by (rule hasParent_cons_one[
                      OF ok Rne])
                   (rule disjI1[OF parent1])
              show ?thesis
                by (rule nat_parent[
                      rule_format, OF hpM])
            qed
            have ops:
              "\<forall>n. 1 \<le> n
                \<longrightarrow> oper ?M n \<in> W v"
            proof (intro allI impI)
              fix n :: nat
              assume n1: "1 \<le> n"
              have op:
                "oper ?M n =
                  (0, v) # oper R n"
                by (rule oper_cons_nat[
                      OF ok Rne hp])
              have memstar:
                "oper R n \<in> Wstar"
                using nat n1 by blast
              have mem:
                "(0, v) # oper R n \<in> W v"
                using memstar
                  argOK_oper[OF ok,
                    where n=n]
                unfolding Wstar_def by blast
              show "oper ?M n \<in> W v"
                using op mem by simp
            qed
            show ?thesis
              by (rule A1_intro)
                 (use natM ops in
                   \<open>auto simp: Aop_def\<close>)
          next
            case hp: False
            have row0:
              "entry R 1 (length R - 1) = 0"
            proof (rule ccontr)
              assume nz:
                "entry R 1 (length R - 1)
                  \<noteq> 0"
              have idx:
                "idx1 R (length R - 1) = 1"
                using nz
                unfolding idx1_def by simp
              have nop1:
                "\<not> hasParent R 1
                  (length R - 1)"
                using hp idx by simp
              have eq:
                "entry R 1 (length R - 1) =
                  (entry R 1 (length R - 1) - 1)
                    + 1"
                using nz by presburger
              have dom:
                "domT R
                  (entry R 1 (length R - 1) - 1)"
                unfolding domT_def
                using eq nop1 by simp
              have nd:
                "\<not> domT R
                  (entry R 1 (length R - 1) - 1)"
                using nat unfolding natDom_def
                by blast
              show False using dom nd by simp
            qed
            have nop0:
              "\<not> hasParent R 0
                (length R - 1)"
            proof
              assume parent0:
                "hasParent R 0
                  (length R - 1)"
              have idx:
                "idx1 R (length R - 1) = 0"
                using row0
                unfolding idx1_def by simp
              show False using hp parent0 idx
                by simp
            qed
            have qW:
              "(0, v) # butlast R \<in> W v"
            proof (cases "2 \<le> length R")
              case long: True
              have memstar:
                "oper R 1 \<in> Wstar"
                using nat by simp
              have long0:
                "length R - 1 \<noteq> 0"
                using long by simp
              have pred:
                "oper R 1 = butlast R"
              proof -
                have op:
                  "oper R 1 = Pred R"
                proof (cases
                  "entry R 0 (length R - 1) = 0
                   \<and>
                   entry R 1 (length R - 1) = 0")
                  case True
                  show ?thesis
                    by (rule oper_eq_pred_of_zero[
                          OF long0 True])
                next
                  case False
                  show ?thesis
                    by (rule oper_eq_pred_of_noParent[
                          OF long0 False hp])
                qed
                show ?thesis
                  using op long
                  unfolding Pred_def by simp
              qed
              have okop: "argOK (oper R 1)"
                using argOK_dropLast[OF ok]
                  pred by simp
              have mem:
                "(0, v) # oper R 1 \<in> W v"
                using memstar okop
                unfolding Wstar_def by blast
              show ?thesis using mem pred by simp
            next
              case False
              have len1: "length R = 1"
              proof -
                have pos: "0 < length R"
                  using Rne by simp
                have less: "length R < 2"
                  using False by simp
                show ?thesis
                  using pos less by presburger
              qed
              obtain q where R_single: "R = [q]"
                using len1 by (cases R) auto
              have tail: "butlast R = []"
                using R_single by simp
              show ?thesis
                using Om_mem_W[of v] tail
                by simp
            qed
            have ops:
              "\<forall>n. 1 \<le> n
                \<longrightarrow> oper ?M n \<in> W v"
            proof (intro allI impI)
              fix n :: nat
              assume "1 \<le> n"
              have op:
                "oper ?M n =
                  concat
                    (map
                      (\<lambda>_. (0, v) # butlast R)
                      [0..<n])"
                by (rule oper_cons_succ[
                      OF ok Rne row0 nop0])
              have copies:
                "concat
                  (map
                    (\<lambda>_. (0, v) # butlast R)
                    [0..<n]) \<in> W v"
              proof -
                have root:
                  "\<forall>p\<in>
                    set ((0, v) # butlast R).
                    entry ((0, v) # butlast R)
                      0 0 \<le> fst p"
                  by (rule rsum_self_cons)
                note all =
                  W_flatMap_copies[
                    OF qW root]
                show ?thesis
                  by (rule all[rule_format])
              qed
              show "oper ?M n \<in> W v"
                using op copies by simp
            qed
            show ?thesis
              by (rule A1_intro)
                 (use nat_zero[rule_format,
                     OF row0] ops in
                   \<open>auto simp: Aop_def\<close>)
          qed
        next
          assume gr:
            "\<exists>m<u.
              domT R m \<and>
              (\<forall>z\<in>W m.
                based z \<longrightarrow>
                graft R z \<in> Wstar)"
          obtain m where mu: "m < u"
            and dom: "domT R m"
            and grstar:
              "\<forall>z\<in>W m.
                based z \<longrightarrow>
                graft R z \<in> Wstar"
            using gr by blast
          show ?thesis
          proof (cases "v \<le> m")
            case vm: True
            have towers:
              "\<forall>k. tow v R k \<in> W v"
            proof (intro allI)
              fix k
              show "tow v R k \<in> W v"
              proof (induction k)
                case 0
                show ?case by (simp add: W_nil)
              next
                case (Suc k)
                have based:
                  "based (tow v R k)"
                  by (cases k)
                     (simp_all add: based_cons)
                have sub: "W v \<subseteq> W m"
                  by (rule W_mono[OF vm])
                have lift:
                  "tow v R k \<in> W m"
                  using sub Suc.IH by blast
                have memstar:
                  "graft R (tow v R k)
                    \<in> Wstar"
                  using grstar lift based by blast
                have mem:
                  "(0, v) #
                    graft R (tow v R k)
                    \<in> W v"
                  using memstar
                    argOK_graft[
                      OF Rne ok,
                      where z="tow v R k"]
                  unfolding Wstar_def by blast
                show ?case using mem by simp
              qed
            qed
            have hpM:
              "hasParent ?M 1 (length R)"
            proof (rule hasParent_cons_one[
                OF ok Rne])
              show
                "hasParent R 1 (length R - 1)
                 \<or>
                 v < entry R 1 (length R - 1)"
                apply (rule disjI2)
                using dom vm
                unfolding domT_def
                by auto
            qed
            have natM: "natDom ?M"
              by (rule nat_parent[
                    rule_format, OF hpM])
            have ops:
              "\<forall>n. 1 \<le> n
                \<longrightarrow> oper ?M n \<in> W v"
            proof (intro allI impI)
              fix n :: nat
              assume "1 \<le> n"
              have op:
                "oper ?M n = tow v R n"
                by (rule oper_cons_tower[
                      OF ok dom vm])
              have tn: "tow v R n \<in> W v"
                by (rule towers[rule_format])
              show "oper ?M n \<in> W v"
                using op tn by simp
            qed
            show ?thesis
              by (rule A1_intro)
                 (use natM ops in
                   \<open>auto simp: Aop_def\<close>)
          next
            case False
            have mv: "m < v"
              using False by simp
            have domM: "domT ?M m"
              by (rule domT_cons_of_lt[
                    OF ok dom mv])
            have grafts:
              "\<forall>z\<in>W m.
                based z \<longrightarrow>
                graft ?M z \<in> W v"
            proof (intro ballI impI)
              fix z
              assume zW: "z \<in> W m"
                and bz: "based z"
              have memstar:
                "graft R z \<in> Wstar"
                using grstar zW bz by blast
              have mem:
                "(0, v) # graft R z \<in> W v"
                using memstar
                  argOK_graft[
                    OF Rne ok, where z=z]
                unfolding Wstar_def by blast
              show "graft ?M z \<in> W v"
                using graft_cons[
                    OF Rne, of v z]
                  mem by simp
            qed
            show ?thesis
              by (rule A1_intro)
                 (use mv domM grafts in
                   \<open>auto simp: Aop_def\<close>)
          qed
        qed
      qed
    qed
  qed
qed

lemma tree_shift:
  fixes p0 :: "nat \<times> nat"
    and R :: pairseq
  assumes ge:
    "\<forall>q\<in>set R.
      fst p0 \<le> fst q"
  shows
    "map
      (\<lambda>q.
        (fst q + fst p0, snd q))
      ((0, snd p0) #
        map
          (\<lambda>q.
            (fst q - fst p0, snd q))
          R) =
     p0 # R"
proof -
  have tail:
    "map
      (\<lambda>q.
        (fst q + fst p0, snd q))
      (map
        (\<lambda>q.
          (fst q - fst p0, snd q))
        R) = R"
    by (rule map_sub_add[
          where X=R and c="fst p0",
          OF ge])
  show ?thesis
    using tail by (cases p0) simp
qed

lemma mem_of_Aclosed_aux:
  assumes len: "length M \<le> N"
    and closed:
      "\<forall>u M'.
        Aop W u X M'
          \<longrightarrow> M' \<in> X"
  shows "M \<in> X"
  using len closed
proof (induction N arbitrary: M X)
  case 0
  then show ?case
    unfolding Aop_def entry_def
    by auto
next
  case (Suc N)
  show ?case
  proof (cases "M = []")
    case True
    have base:
      "Aop W 0 X []"
      unfolding Aop_def entry_def
      by simp
    show ?thesis
      using Suc.prems base True by blast
  next
    case Mne: False
    obtain A Q where M:
        "M = A @ Q"
      and Qne: "Q \<noteq> []"
      and rs: "rsum A Q"
      and tail:
        "\<forall>p\<in>set (tl Q).
          entry Q 0 0 < fst p"
      using split_lastMin[OF Mne]
      by blast
    have total:
      "length A + length Q \<le> Suc N"
      using Suc.prems M by simp
    show ?thesis
    proof (cases "A = []")
      case True
      obtain p0 R where Q: "Q = p0 # R"
        using Qne by (cases Q) auto
      have strict:
        "\<forall>q\<in>set R.
          fst p0 < fst q"
      proof (intro ballI)
        fix q
        assume qR: "q \<in> set R"
        have qtail: "q \<in> set (tl Q)"
          using Q qR by simp
        have e:
          "entry Q 0 0 = fst p0"
          using Q by (simp add: entry_def)
        show "fst p0 < fst q"
          using tail qtail e by simp
      qed
      let ?R0 =
        "map
          (\<lambda>q.
            (fst q - fst p0, snd q))
          R"
      have ok0: "argOK ?R0"
        unfolding argOK_def
      proof (intro ballI)
        fix q
        assume q0: "q \<in> set ?R0"
        then obtain r where rR: "r \<in> set R"
          and q:
            "q =
              (fst r - fst p0, snd r)"
          by auto
        show "0 < fst q"
          using strict[rule_format, OF rR]
            q by simp
      qed
      have len0: "length ?R0 \<le> N"
        using total True Q by simp
      have mem0: "?R0 \<in> Wstar"
        by (rule Suc.IH[
              OF len0 Wstar_closed])
      have root:
        "(0, snd p0) # ?R0
          \<in> W (snd p0)"
        using mem0 ok0
        unfolding Wstar_def by blast
      have shifted:
        "map
          (\<lambda>q.
            (fst q + fst p0, snd q))
          ((0, snd p0) # ?R0)
          \<in> W (snd p0)"
        by (rule W_shift[OF root])
      have tree:
        "p0 # R \<in> W (snd p0)"
      proof -
        have ge:
          "\<forall>q\<in>set R.
            fst p0 \<le> fst q"
          using strict by auto
        have eq:
          "map
            (\<lambda>q.
              (fst q + fst p0, snd q))
            ((0, snd p0) # ?R0) =
           p0 # R"
          by (rule tree_shift[OF ge])
        show ?thesis using shifted eq by simp
      qed
      have level_closed:
        "\<forall>B.
          Aop W (snd p0) X B
            \<longrightarrow> B \<in> X"
        using Suc.prems(2) by blast
      have sub: "W (snd p0) \<subseteq> X"
        by (rule A2'[OF level_closed])
      have "p0 # R \<in> X"
        using sub tree by blast
      then show ?thesis
        using M True Q by simp
    next
      case Ane: False
      have Apos: "0 < length A"
        using Ane by simp
      have Qpos: "0 < length Q"
        using Qne by simp
      have Alen: "length A \<le> N"
        using total Qpos by presburger
      have Qlen: "length Q \<le> N"
        using total Apos by presburger
      have AX: "A \<in> X"
        by (rule Suc.IH[
              OF Alen Suc.prems(2)])
      have xa_closed:
        "\<forall>u B.
          Aop W u (XA A X) B
            \<longrightarrow> B \<in> XA A X"
      proof (intro allI impI)
        fix u B
        assume op: "Aop W u (XA A X) B"
        have level_closed:
          "\<forall>C. Aop W u X C
            \<longrightarrow> C \<in> X"
          using Suc.prems(2) by blast
        show "B \<in> XA A X"
          by (rule XA_closed[
                OF level_closed AX,
                rule_format, OF op])
      qed
      have QXA: "Q \<in> XA A X"
        by (rule Suc.IH[
              OF Qlen xa_closed])
      have AQ: "A @ Q \<in> X"
        using QXA rs
        unfolding XA_def by simp
      show ?thesis using AQ M by simp
    qed
  qed
qed

lemma mem_of_Aclosed:
  assumes closed:
    "\<forall>u M.
      Aop W u X M \<longrightarrow> M \<in> X"
  shows "\<forall>M. M \<in> X"
  by (intro allI)
     (rule mem_of_Aclosed_aux[
       OF order_refl closed])

lemma mem_Wstar:
  "R \<in> Wstar"
  by (rule mem_of_Aclosed[
        OF Wstar_closed, rule_format])

lemma mem_W_of_bound_aux:
  assumes len: "length M \<le> N"
    and bound:
      "\<forall>p\<in>set M. snd p \<le> u"
  shows "M \<in> W u"
  using len bound
proof (induction N arbitrary: M)
  case 0
  then have "M = []" by simp
  then show ?case by (simp add: W_nil)
next
  case (Suc N)
  show ?case
  proof (cases "M = []")
    case True
    then show ?thesis by (simp add: W_nil)
  next
    case Mne: False
    obtain A Q where M:
        "M = A @ Q"
      and Qne: "Q \<noteq> []"
      and rs: "rsum A Q"
      and tail:
        "\<forall>p\<in>set (tl Q).
          entry Q 0 0 < fst p"
      using split_lastMin[OF Mne]
      by blast
    obtain p0 R where Q: "Q = p0 # R"
      using Qne by (cases Q) auto
    have total:
      "length A + length Q \<le> Suc N"
      using Suc.prems M by simp
    have strict:
      "\<forall>q\<in>set R.
        fst p0 < fst q"
    proof (intro ballI)
      fix q
      assume qR: "q \<in> set R"
      have qtail: "q \<in> set (tl Q)"
        using Q qR by simp
      have e:
        "entry Q 0 0 = fst p0"
        using Q by (simp add: entry_def)
      show "fst p0 < fst q"
        using tail qtail e by simp
    qed
    let ?R0 =
      "map
        (\<lambda>q.
          (fst q - fst p0, snd q))
        R"
    have ok0: "argOK ?R0"
      unfolding argOK_def
    proof (intro ballI)
      fix q
      assume "q \<in> set ?R0"
      then obtain r where rR: "r \<in> set R"
        and q:
          "q =
            (fst r - fst p0, snd r)"
        by auto
      show "0 < fst q"
        using strict[rule_format, OF rR]
          q by simp
    qed
    have star: "?R0 \<in> Wstar"
      by (rule mem_Wstar)
    have root:
      "(0, snd p0) # ?R0
        \<in> W (snd p0)"
      using star ok0
      unfolding Wstar_def by blast
    have shifted:
      "map
        (\<lambda>q.
          (fst q + fst p0, snd q))
        ((0, snd p0) # ?R0)
        \<in> W (snd p0)"
      by (rule W_shift[OF root])
    have ge:
      "\<forall>q\<in>set R.
        fst p0 \<le> fst q"
      using strict by auto
    have eq:
      "map
        (\<lambda>q.
          (fst q + fst p0, snd q))
        ((0, snd p0) # ?R0) =
       p0 # R"
      by (rule tree_shift[OF ge])
    have tree0:
      "p0 # R \<in> W (snd p0)"
      using shifted eq by simp
    have p0M: "p0 \<in> set M"
      using M Q by simp
    have p0u: "snd p0 \<le> u"
      using Suc.prems(2) p0M by blast
    have sub: "W (snd p0) \<subseteq> W u"
      by (rule W_mono[OF p0u])
    have tree: "p0 # R \<in> W u"
      using sub tree0 by blast
    show ?thesis
    proof (cases "A = []")
      case True
      show ?thesis
        using M Q True tree by simp
    next
      case Ane: False
      have Apos: "0 < length A"
        using Ane by simp
      have Qpos: "0 < length Q"
        using Qne by simp
      have Alen: "length A \<le> N"
        using total Qpos by presburger
      have Abound:
        "\<forall>p\<in>set A. snd p \<le> u"
        using Suc.prems(2) M by auto
      have AW: "A \<in> W u"
        by (rule Suc.IH[OF Alen Abound])
      have QW: "Q \<in> W u"
        using tree Q by simp
      have AQ: "A @ Q \<in> W u"
        by (rule W_add[OF AW QW rs])
      show ?thesis using AQ M by simp
    qed
  qed
qed

lemma mem_W_of_bound:
  assumes bound:
    "\<forall>p\<in>set M. snd p \<le> u"
  shows "M \<in> W u"
  by (rule mem_W_of_bound_aux[
        OF order_refl bound])

lemma le_maxr1:
  "\<forall>p\<in>set S. snd p \<le> maxr1 S"
proof (induction S)
  case Nil
  show ?case by simp
next
  case (Cons q S)
  show ?case
  proof (intro ballI)
    fix p
    assume p: "p \<in> set (q # S)"
    show "snd p \<le> maxr1 (q # S)"
    proof (cases "p = q")
      case True
      then show ?thesis
        by (simp add: maxr1_cons)
    next
      case False
      have pS: "p \<in> set S"
        using p False by simp
      have "snd p \<le> maxr1 S"
        by (rule Cons.IH[rule_format,
              OF pS])
      also have "... \<le>
        max (snd q) (maxr1 S)"
        by simp
      finally show ?thesis
        by (simp add: maxr1_cons)
    qed
  qed
qed

lemma mem_W_maxr1:
  "M \<in> W (maxr1 M)"
  by (rule mem_W_of_bound[
        OF le_maxr1])

lemma W_membership:
  assumes "ST_PS M"
  shows "\<exists>u. M \<in> W u"
  using mem_W_maxr1[
    of M] by blast

lemma wf_of_cofinality_and_membership:
  assumes cof:
    "\<And>M N.
      ST_PS M \<Longrightarrow> ST_PS N \<Longrightarrow>
      translate N <o translate M \<Longrightarrow>
      \<exists>n. 1 \<le> n \<and>
        translate N \<le>o translate (M\<lbrakk>n\<rbrakk>)"
    and mem:
    "\<And>M. ST_PS M \<Longrightarrow>
      \<exists>u. M \<in> W u"
  shows "wfp Rst"
proof (rule accp_wfpI, intro allI)
  fix M
  show "Wellfounded.accp Rst M"
  proof (cases "ST_PS M")
    case True
    obtain u where Mu: "M \<in> W u"
      using mem[OF True] by blast
    have all_acc:
      "\<forall>N. N \<in> W u \<longrightarrow>
        Wellfounded.accp Rst N"
    proof (rule acc_of_W)
      fix A B
      assume Ast: "ST_PS A"
        and Bst: "ST_PS B"
        and lt: "translate B <o translate A"
      show
        "\<exists>n. 1 \<le> n \<and>
          translate B \<le>o
            translate (A\<lbrakk>n\<rbrakk>)"
        by (rule cof[OF Ast Bst lt])
    qed
    show ?thesis
      by (rule all_acc[rule_format,
            OF Mu])
  next
    case False
    show ?thesis
    proof (rule accp.accI)
      fix N
      assume "Rst N M"
      then have "ST_PS M"
        unfolding Rst_def by simp
      with False show
        "Wellfounded.accp Rst N"
        by contradiction
    qed
  qed
qed

lemma wf_olt_ST_PS_of_cofinality:
  assumes cof:
    "\<And>M N.
      ST_PS M \<Longrightarrow> ST_PS N \<Longrightarrow>
      translate N <o translate M \<Longrightarrow>
      \<exists>n. 1 \<le> n \<and>
        translate N \<le>o translate (M\<lbrakk>n\<rbrakk>)"
  shows
    "wfp
      (\<lambda>a b.
        ST_PS a \<and> ST_PS b \<and>
        translate a <o translate b)"
  using wf_of_cofinality_and_membership[
      OF cof W_membership]
  unfolding Rst_def .

end
