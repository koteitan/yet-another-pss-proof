theory Final
  imports ArgDom Wset Reduction
begin

lemma acc_Rnf_of_acc_PS:
  assumes acc:
    "Wellfounded.accp
      (\<lambda>a b.
        ST_PS a \<and> ST_PS b \<and>
        translate a <o translate b)
      M"
    and Mst: "ST_PS M"
  shows
    "Wellfounded.accp Rnf (translate M)"
proof -
  have transfer:
    "\<And>X.
      Wellfounded.accp
        (\<lambda>a b.
          ST_PS a \<and> ST_PS b \<and>
          translate a <o translate b)
        X
      \<Longrightarrow>
      ST_PS X \<longrightarrow>
        Wellfounded.accp Rnf
          (translate X)"
  proof -
    fix X
    assume Xacc:
      "Wellfounded.accp
        (\<lambda>a b.
          ST_PS a \<and> ST_PS b \<and>
          translate a <o translate b)
        X"
    show
      "ST_PS X \<longrightarrow>
        Wellfounded.accp Rnf
          (translate X)"
    proof (rule accp_induct[OF Xacc])
      fix X
      assume Xacc:
        "Wellfounded.accp
          (\<lambda>a b.
            ST_PS a \<and> ST_PS b \<and>
            translate a <o translate b)
          X"
        and ih:
        "\<forall>Y.
          (ST_PS Y \<and> ST_PS X \<and>
            translate Y <o translate X)
          \<longrightarrow>
          ST_PS Y \<longrightarrow>
            Wellfounded.accp Rnf
              (translate Y)"
      show
        "ST_PS X \<longrightarrow>
          Wellfounded.accp Rnf
            (translate X)"
      proof
        assume Xst: "ST_PS X"
        show
          "Wellfounded.accp Rnf
            (translate X)"
        proof (rule accp.accI)
          fix v
          assume rv:
            "Rnf v (translate X)"
          have vlt:
              "v <o translate X"
            and vNF: "v \<in> NF"
            using rv unfolding Rnf_def
            by blast+
          obtain Y where
              Yst: "ST_PS Y"
            and Yeq: "translate Y = v"
            using vNF unfolding NF_def
            by blast
          have rel:
            "ST_PS Y \<and> ST_PS X \<and>
              translate Y <o translate X"
            using Yst Xst vlt Yeq by simp
          have
            "Wellfounded.accp Rnf
              (translate Y)"
            using ih rel Yst by blast
          then show
            "Wellfounded.accp Rnf v"
            using Yeq by simp
        qed
      qed
    qed
  qed
  show ?thesis
    by (rule transfer[OF acc, rule_format,
          OF Mst])
qed

lemma wf_Rnf_of_wf_PS:
  assumes wf:
    "wfp
      (\<lambda>a b.
        ST_PS a \<and> ST_PS b \<and>
        translate a <o translate b)"
  shows "wfp Rnf"
proof (rule accp_wfpI, intro allI)
  fix u
  show "Wellfounded.accp Rnf u"
  proof (cases "u \<in> NF")
    case True
    obtain M where
        Mst: "ST_PS M"
      and eq: "translate M = u"
      using True unfolding NF_def by blast
    have Macc:
      "Wellfounded.accp
        (\<lambda>a b.
          ST_PS a \<and> ST_PS b \<and>
          translate a <o translate b)
        M"
      by (rule accp_wfpD[OF wf])
    have
      "Wellfounded.accp Rnf
        (translate M)"
      by (rule acc_Rnf_of_acc_PS[
            OF Macc Mst])
    then show ?thesis using eq by simp
  next
    case False
    show ?thesis
    proof (rule accp.accI)
      fix v
      assume "Rnf v u"
      then have "u \<in> NF"
        unfolding Rnf_def by simp
      with False show
        "Wellfounded.accp Rnf v"
        by contradiction
    qed
  qed
qed

lemma pss_cofinality_holds:
  assumes Mst: "ST_PS M"
    and Nst: "ST_PS N"
    and lt: "translate N <o translate M"
  shows
    "\<exists>n. 1 \<le> n \<and>
      translate N \<le>o
        translate (M\<lbrakk>n\<rbrakk>)"
  by (rule pss_cofinality_of_core[
        OF argDomCore_holds
          Mst Nst lt])

lemma wf_olt_ST_PS_holds:
  "wfp
    (\<lambda>a b.
      ST_PS a \<and> ST_PS b \<and>
      translate a <o translate b)"
proof (rule wf_olt_ST_PS_of_cofinality)
  fix M N
  assume Mst: "ST_PS M"
    and Nst: "ST_PS N"
    and lt: "translate N <o translate M"
  show
    "\<exists>n. 1 \<le> n \<and>
      translate N \<le>o
        translate (M\<lbrakk>n\<rbrakk>)"
    by (rule pss_cofinality_holds[
          OF Mst Nst lt])
qed

lemma wf_Rnf_holds:
  "wfp Rnf"
  by (rule wf_Rnf_of_wf_PS[
        OF wf_olt_ST_PS_holds])

theorem PSS_terminates_unconditional:
  "wfp stepRel"
  by (rule step_terminates[
        OF wf_Rnf_holds])

theorem no_infinite_expansion_holds:
  "\<not> (\<exists>S :: nat \<Rightarrow> pairseq.
    (\<forall>i. ST_PS (S i)) \<and>
    (\<forall>i. step (S i)
      (S (i + 1))))"
  by (rule no_infinite_expansion[
        OF wf_Rnf_holds])

end
