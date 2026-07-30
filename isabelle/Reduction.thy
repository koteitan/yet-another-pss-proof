theory Reduction
  imports Decrease
begin

definition NF :: "three set" where
  "NF = {t. \<exists>M. ST_PS M \<and> translate M = t}"

definition Rnf :: "three \<Rightarrow> three \<Rightarrow> bool" where
  "Rnf v u \<longleftrightarrow> v <o u \<and> u \<in> NF \<and> v \<in> NF"

definition stepRel :: "pairseq \<Rightarrow> pairseq \<Rightarrow> bool" where
  "stepRel T M \<longleftrightarrow> ST_PS M \<and> step M T"

lemma step_terminates_cond:
  assumes dec:
    "\<And>M n. \<lbrakk>ST_PS M; 1 < length M; 1 \<le> n\<rbrakk> \<Longrightarrow>
      translate (M\<lbrakk>n\<rbrakk>) <o translate M"
    and wfimg: "wfp Rnf"
  shows "wfp stepRel"
proof (rule wfp_if_convertible_to_wfp[OF wfimg, where f=translate])
  fix T M
  assume "stepRel T M"
  then have stM: "ST_PS M" and st: "step M T"
    by (auto simp: stepRel_def)
  from st show "Rnf (translate T) (translate M)"
  proof cases
    case (step_oper n)
    have stT: "ST_PS (M\<lbrakk>n\<rbrakk>)"
      by (rule ST_PS.oper[OF stM step_oper(3)])
    show ?thesis
      using step_oper(1) dec[OF stM step_oper(2) step_oper(3)] stM stT
      by (auto simp: Rnf_def NF_def)
  qed
qed

lemma no_infinite_expansion_cond:
  assumes dec:
    "\<And>M n. \<lbrakk>ST_PS M; 1 < length M; 1 \<le> n\<rbrakk> \<Longrightarrow>
      translate (M\<lbrakk>n\<rbrakk>) <o translate M"
    and wfimg: "wfp Rnf"
  shows "\<not> (\<exists>S :: nat \<Rightarrow> pairseq.
    (\<forall>i. ST_PS (S i)) \<and> (\<forall>i. step (S i) (S (i + 1))))"
proof
  assume "\<exists>S :: nat \<Rightarrow> pairseq.
    (\<forall>i. ST_PS (S i)) \<and> (\<forall>i. step (S i) (S (i + 1)))"
  then obtain S :: "nat \<Rightarrow> pairseq" where
    stS: "\<forall>i. ST_PS (S i)"
    and steps: "\<forall>i. step (S i) (S (i + 1))"
    by blast
  have wf: "wfp stepRel"
    by (rule step_terminates_cond[OF dec wfimg])
  have nonempty: "range S \<noteq> {}" by auto
  from wf have minall:
    "\<forall>B. B \<noteq> {} \<longrightarrow>
      (\<exists>z\<in>B. \<forall>y. stepRel y z \<longrightarrow> y \<notin> B)"
    by (simp only: wfp_iff_ex_minimal)
  have minrange:
    "\<exists>z\<in>range S. \<forall>y. stepRel y z \<longrightarrow> y \<notin> range S"
    using minall[rule_format, of "range S"] nonempty by blast
  then obtain z where
    z: "z \<in> range S"
    and minimal: "\<forall>y. stepRel y z \<longrightarrow> y \<notin> range S"
    by blast
  from z obtain i where zi: "z = S i" by blast
  have "stepRel (S (i + 1)) z"
    using stS steps zi by (auto simp: stepRel_def)
  moreover have "S (i + 1) \<in> range S" by blast
  ultimately show False using minimal by blast
qed

lemma step_terminates:
  assumes "wfp Rnf"
  shows "wfp stepRel"
proof (rule step_terminates_cond[OF _ assms])
  fix M :: pairseq and n :: nat
  assume "ST_PS M" "1 < length M" "1 \<le> n"
  show "translate (M\<lbrakk>n\<rbrakk>) <o translate M"
    by (rule m_step_decreases[OF \<open>1 < length M\<close> \<open>1 \<le> n\<close>])
qed

lemma no_infinite_expansion:
  assumes "wfp Rnf"
  shows "\<not> (\<exists>S :: nat \<Rightarrow> pairseq.
    (\<forall>i. ST_PS (S i)) \<and> (\<forall>i. step (S i) (S (i + 1))))"
proof (rule no_infinite_expansion_cond[OF _ assms])
  fix M :: pairseq and n :: nat
  assume "ST_PS M" "1 < length M" "1 \<le> n"
  show "translate (M\<lbrakk>n\<rbrakk>) <o translate M"
    by (rule m_step_decreases[OF \<open>1 < length M\<close> \<open>1 \<le> n\<close>])
qed

end
