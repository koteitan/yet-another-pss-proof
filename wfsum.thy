theory wfsum
  imports wf "HOL-Library.Multiset"
begin

text \<open>Sum-layer reduction (to be merged into \<open>wf.thy\<close> once green): within-level WF
  reduces to argument-level WF via the multiset extension (Dershowitz\<dash>Manna), as
  in the PrSS proof.  An \<open>NF\<close> term is a non-increasing sum \<open>p\<^bsub>0\<^esub>(b\<^sub>1)+\<dots>+p\<^bsub>0\<^esub>(b\<^sub>k)\<close>
  (head subscript \<open>0\<close> by \<open>inv2\<close>, sibling subscripts \<open>\<le> 0\<close> by \<open>cnf_tops_le\<close>,
  non-increasing by \<open>cnf\<close>); on such sums \<open><o\<close> is lex on the argument lists, which
  embeds into the multiset extension of the argument order.\<close>

fun sargs :: "three \<Rightarrow> three list" where
  "sargs Z = []"
| "sargs (P a b c) = b # sargs c"

abbreviation margs :: "three \<Rightarrow> three multiset" where
  "margs x \<equiv> mset (sargs x)"

lemma NF_lead0:
  assumes "x \<in> NF" and "x = P a b c" shows "a = 0"
proof -
  from assms(1) obtain M where M: "M \<in> ST_PS" "x = translate M" by auto
  have inv: "inv2 (map snd (incpref M))"
    using nfinv_ST_PS[OF M(1)] by (simp add: nfinv_def)
  have s0: "0 < length (map snd (incpref M)) \<and> map snd (incpref M) ! 0 = 0"
    using inv unfolding inv2_def by blast
  have sp: "spine x = map snd (incpref M)" using M(2) spine_translate_eq by simp
  have "spine x = a # spine b" using assms(2) by simp
  thus ?thesis using sp s0 by simp
qed

lemma cnf_NF: "x \<in> NF \<Longrightarrow> cnf x"
  using cnf_ST_PS by auto

lemma NF_zerotops:
  assumes "x \<in> NF" shows "\<forall>s \<in> set (tops x). s = 0"
proof (cases x)
  case Z thus ?thesis by simp
next
  case (P a b c)
  have a0: "a = 0" using NF_lead0[OF assms P] .
  have "\<forall>s \<in> set (tops c). s \<le> a"
    using cnf_tops_le cnf_NF[OF assms] P by blast
  hence "\<forall>s \<in> set (tops c). s = 0" using a0 by simp
  thus ?thesis using P a0 by simp
qed

lemma sargs_le_hd:
  "cnf x \<Longrightarrow> \<forall>s \<in> set (tops x). s = 0 \<Longrightarrow> x = P 0 b c \<Longrightarrow> k \<in> set (sargs c) \<Longrightarrow> k \<le>o b"
proof (induction c arbitrary: b x)
  case Z thus ?case by simp
next
  case (P e f g)
  have e0: "e = 0" using P.prems(2) P.prems(3) by simp
  have nlt: "\<not> (P 0 b Z <o P 0 f Z)"
    using P.prems(1) P.prems(3) e0 by simp
  hence nbf: "\<not> b <o f" by simp
  have fb: "f \<le>o b" using olt_total[of b f] nbf by blast
  have cnfc: "cnf (P e f g)" using P.prems(1) P.prems(3) by auto
  have topsc: "\<forall>s \<in> set (tops (P e f g)). s = 0"
    using P.prems(2) P.prems(3) by simp
  from P.prems(4) consider "k = f" | "k \<in> set (sargs g)" by auto
  thus ?case
  proof cases
    case 1 thus ?thesis using fb by simp
  next
    case 2
    have IHinst: "P e f g = P 0 f g \<Longrightarrow> k \<le>o f"
      by (rule P.IH(2)[OF cnfc topsc _ 2])
    have "k \<le>o f" using IHinst e0 by simp
    thus ?thesis using fb ole_olt_trans olt_trans by blast
  qed
qed

lemma sargs_noninc:
  "cnf x \<Longrightarrow> \<forall>s \<in> set (tops x). s = 0 \<Longrightarrow> sorted_wrt (\<lambda>b f. f \<le>o b) (sargs x)"
proof (induction x)
  case Z thus ?case by simp
next
  case (P a b c)
  have a0: "a = 0" using P.prems(2) by simp
  have cnfc: "cnf c" using P.prems(1) by (cases c) auto
  have topsc: "\<forall>s \<in> set (tops c). s = 0" using P.prems(2) by simp
  have hd_le: "\<forall>k \<in> set (sargs c). k \<le>o b"
    using sargs_le_hd[OF P.prems(1)] P.prems(2) a0 by blast
  show ?case using P.IH(2)[OF cnfc topsc] hd_le by simp
qed

lemma olt_sum_decomp:
  assumes "\<forall>s \<in> set (tops x). s = 0" and "\<forall>s \<in> set (tops y). s = 0" and "x <o y"
  shows "\<exists>pre bs fs. sargs x = pre @ bs \<and> sargs y = pre @ fs \<and>
           ((bs = [] \<and> fs \<noteq> []) \<or> (bs \<noteq> [] \<and> fs \<noteq> [] \<and> hd bs <o hd fs))"
  using assms
proof (induction x arbitrary: y)
  case Z
  then obtain e f g where y: "y = P e f g" using olt_Z_iff by (cases y) auto
  have "sargs Z = [] @ [] \<and> sargs y = [] @ sargs y \<and>
          (([] = [] \<and> sargs y \<noteq> []) \<or> ([] \<noteq> [] \<and> sargs y \<noteq> [] \<and> hd [] <o hd (sargs y)))"
    using y by simp
  thus ?case by blast
next
  case (P a b c)
  have "y \<noteq> Z" using P.prems(3) not_olt_Z by blast
  then obtain e f g where y: "y = P e f g" by (cases y) auto
  have a0: "a = 0" using P.prems(1) by simp
  have e0: "e = 0" using P.prems(2) y by simp
  from P.prems(3) have disj: "b <o f \<or> (b = f \<and> c <o g)"
    unfolding y using a0 e0 by simp
  show ?case
  proof (cases "b <o f")
    case True
    have "sargs (P a b c) = [] @ (b # sargs c) \<and> sargs y = [] @ (f # sargs g) \<and>
            ((b # sargs c = [] \<and> f # sargs g \<noteq> []) \<or>
             (b # sargs c \<noteq> [] \<and> f # sargs g \<noteq> [] \<and> hd (b # sargs c) <o hd (f # sargs g)))"
      using y True by simp
    thus ?thesis by blast
  next
    case False
    have bf: "b = f" and cg: "c <o g" using disj False by auto
    have topsc: "\<forall>s \<in> set (tops c). s = 0" using P.prems(1) by simp
    have topsg: "\<forall>s \<in> set (tops g). s = 0" using P.prems(2) y by simp
    obtain pre bs fs where IH: "sargs c = pre @ bs" "sargs g = pre @ fs"
        "((bs = [] \<and> fs \<noteq> []) \<or> (bs \<noteq> [] \<and> fs \<noteq> [] \<and> hd bs <o hd fs))"
      using P.IH(2)[OF topsc topsg cg] by blast
    have "sargs (P a b c) = (b # pre) @ bs \<and> sargs y = (b # pre) @ fs \<and>
            ((bs = [] \<and> fs \<noteq> []) \<or> (bs \<noteq> [] \<and> fs \<noteq> [] \<and> hd bs <o hd fs))"
      using y IH bf by simp
    thus ?thesis by blast
  qed
qed

lemma sorted_suffix_le_hd:
  assumes sw: "sorted_wrt (\<lambda>b f. f \<le>o b) (pre @ bs)"
    and kbs: "k \<in> set bs" and ne: "bs \<noteq> []"
  shows "k \<le>o hd bs"
proof -
  have swbs: "sorted_wrt (\<lambda>b f. f \<le>o b) bs"
    using sw by (metis sorted_wrt_append)
  obtain h t where ht: "bs = h # t" using ne by (cases bs) auto
  have tl_le: "\<forall>z \<in> set t. z \<le>o h" using swbs ht by simp
  from kbs ht consider "k = h" | "k \<in> set t" by auto
  thus ?thesis
  proof cases
    case 1 thus ?thesis using ht by simp
  next
    case 2 thus ?thesis using tl_le ht by simp
  qed
qed

lemma olt_sum_mult:
  assumes t0x: "\<forall>s \<in> set (tops x). s = 0" and t0y: "\<forall>s \<in> set (tops y). s = 0"
    and cx: "cnf x" and lt: "x <o y"
    and bx: "set (sargs x) \<subseteq> A" and byy: "set (sargs y) \<subseteq> A"
  shows "(margs x, margs y) \<in> mult {(b,f). b <o f \<and> b \<in> A \<and> f \<in> A}"
proof -
  let ?r = "{(b,f). b <o f \<and> b \<in> A \<and> f \<in> A}"
  obtain pre bs fs where d1: "sargs x = pre @ bs" and d2: "sargs y = pre @ fs"
    and d3: "(bs = [] \<and> fs \<noteq> []) \<or> (bs \<noteq> [] \<and> fs \<noteq> [] \<and> hd bs <o hd fs)"
    using olt_sum_decomp[OF t0x t0y lt] by blast
  have fs_ne: "fs \<noteq> []" using d3 by blast
  have Jne: "mset fs \<noteq> {#}" using fs_ne by simp
  have dom: "\<forall>k \<in> set_mset (mset bs). \<exists>j \<in> set_mset (mset fs). (k, j) \<in> ?r"
  proof
    fix k assume "k \<in> set_mset (mset bs)"
    hence kbs: "k \<in> set bs" by simp
    have bs_ne: "bs \<noteq> []" using kbs by auto
    have hdlt: "hd bs <o hd fs" using d3 bs_ne by blast
    have sw: "sorted_wrt (\<lambda>b f. f \<le>o b) (sargs x)" using sargs_noninc[OF cx t0x] .
    have khd: "k \<le>o hd bs"
      by (rule sorted_suffix_le_hd[OF sw[unfolded d1] kbs bs_ne])
    have klt: "k <o hd fs" using khd hdlt ole_olt_trans by blast
    have kA: "k \<in> A" using kbs d1 bx by auto
    have hA: "hd fs \<in> A" using fs_ne d2 byy by auto
    have "hd fs \<in> set_mset (mset fs)" using fs_ne by simp
    thus "\<exists>j \<in> set_mset (mset fs). (k, j) \<in> ?r" using klt kA hA by auto
  qed
  have "(mset pre + mset bs, mset pre + mset fs) \<in> mult ?r"
    by (rule one_step_implies_mult[OF Jne dom])
  thus ?thesis using d1 d2 by simp
qed

subsection \<open>The general sum peel: \<open><o\<close> on \<^emph>\<open>any\<close> CNF sums embeds into the multiset
  extension of the order on the summand singletons (no zero-tops needed)\<close>

fun summands :: "three \<Rightarrow> three list" where
  "summands Z = []"
| "summands (P a b c) = P a b Z # summands c"

lemma summands_shape: "s \<in> set (summands x) \<Longrightarrow> \<exists>a c. s = P a c Z"
  by (induction x) auto

lemma summands_le_hd:
  "cnf x \<Longrightarrow> x = P a b c \<Longrightarrow> k \<in> set (summands c) \<Longrightarrow> k \<le>o P a b Z"
proof (induction c arbitrary: a b x)
  case Z thus ?case by simp
next
  case (P e f g)
  have nlt: "\<not> (P a b Z <o P e f Z)" using P.prems(1) P.prems(2) by auto
  have efab: "P e f Z \<le>o P a b Z" using olt_total[of "P a b Z" "P e f Z"] nlt by blast
  have cnfc: "cnf (P e f g)" using P.prems(1) P.prems(2) by auto
  from P.prems(3) consider "k = P e f Z" | "k \<in> set (summands g)" by auto
  thus ?case
  proof cases
    case 1 thus ?thesis using efab by simp
  next
    case 2
    have "k \<le>o P e f Z" by (rule P.IH(2)[OF cnfc refl 2])
    thus ?thesis using efab ole_olt_trans olt_trans by blast
  qed
qed

lemma summands_noninc:
  "cnf x \<Longrightarrow> sorted_wrt (\<lambda>s t. t \<le>o s) (summands x)"
proof (induction x)
  case Z thus ?case by simp
next
  case (P a b c)
  have cnfc: "cnf c" using P.prems by (cases c) auto
  have hd_le: "\<forall>k \<in> set (summands c). k \<le>o P a b Z"
    using summands_le_hd[OF P.prems refl] by blast
  show ?case using P.IH(2)[OF cnfc] hd_le by simp
qed

lemma olt_summands_decomp:
  assumes "x <o y"
  shows "\<exists>pre bs fs. summands x = pre @ bs \<and> summands y = pre @ fs \<and>
           ((bs = [] \<and> fs \<noteq> []) \<or> (bs \<noteq> [] \<and> fs \<noteq> [] \<and> hd bs <o hd fs))"
  using assms
proof (induction x arbitrary: y)
  case Z
  then obtain e f g where y: "y = P e f g" using olt_Z_iff by (cases y) auto
  have "summands Z = [] @ [] \<and> summands y = [] @ summands y \<and>
          (([] = [] \<and> summands y \<noteq> []) \<or>
           ([] \<noteq> [] \<and> summands y \<noteq> [] \<and> hd [] <o hd (summands y)))"
    using y by simp
  thus ?case by blast
next
  case (P a b c)
  have "y \<noteq> Z" using P.prems not_olt_Z by blast
  then obtain e f g where y: "y = P e f g" by (cases y) auto
  from P.prems have cases3: "a < e \<or> (a = e \<and> b <o f) \<or> (a = e \<and> b = f \<and> c <o g)"
    unfolding y by simp
  show ?case
  proof (cases "a = e \<and> b = f")
    case False
    have hdlt: "P a b Z <o P e f Z" using cases3 False by auto
    have "summands (P a b c) = [] @ (P a b Z # summands c) \<and>
          summands y = [] @ (P e f Z # summands g) \<and>
            ((P a b Z # summands c = [] \<and> P e f Z # summands g \<noteq> []) \<or>
             (P a b Z # summands c \<noteq> [] \<and> P e f Z # summands g \<noteq> [] \<and>
              hd (P a b Z # summands c) <o hd (P e f Z # summands g)))"
      using y hdlt by simp
    thus ?thesis by blast
  next
    case True
    have cg: "c <o g" using cases3 True olt_irrefl by auto
    obtain pre bs fs where IH: "summands c = pre @ bs" "summands g = pre @ fs"
        "((bs = [] \<and> fs \<noteq> []) \<or> (bs \<noteq> [] \<and> fs \<noteq> [] \<and> hd bs <o hd fs))"
      using P.IH(2)[OF cg] by blast
    have "summands (P a b c) = (P a b Z # pre) @ bs \<and> summands y = (P a b Z # pre) @ fs \<and>
            ((bs = [] \<and> fs \<noteq> []) \<or> (bs \<noteq> [] \<and> fs \<noteq> [] \<and> hd bs <o hd fs))"
      using y IH True by simp
    thus ?thesis by blast
  qed
qed

lemma olt_summands_mult:
  assumes cx: "cnf x" and lt: "x <o y"
    and bx: "set (summands x) \<subseteq> A" and byy: "set (summands y) \<subseteq> A"
  shows "(mset (summands x), mset (summands y)) \<in> mult {(s,t). s <o t \<and> s \<in> A \<and> t \<in> A}"
proof -
  let ?r = "{(s,t). s <o t \<and> s \<in> A \<and> t \<in> A}"
  obtain pre bs fs where d1: "summands x = pre @ bs" and d2: "summands y = pre @ fs"
    and d3: "(bs = [] \<and> fs \<noteq> []) \<or> (bs \<noteq> [] \<and> fs \<noteq> [] \<and> hd bs <o hd fs)"
    using olt_summands_decomp[OF lt] by blast
  have fs_ne: "fs \<noteq> []" using d3 by blast
  have Jne: "mset fs \<noteq> {#}" using fs_ne by simp
  have dom: "\<forall>k \<in> set_mset (mset bs). \<exists>j \<in> set_mset (mset fs). (k, j) \<in> ?r"
  proof
    fix k assume "k \<in> set_mset (mset bs)"
    hence kbs: "k \<in> set bs" by simp
    have bs_ne: "bs \<noteq> []" using kbs by auto
    have hdlt: "hd bs <o hd fs" using d3 bs_ne by blast
    have sw: "sorted_wrt (\<lambda>s t. t \<le>o s) (summands x)" using summands_noninc[OF cx] .
    have khd: "k \<le>o hd bs"
      by (rule sorted_suffix_le_hd[OF sw[unfolded d1] kbs bs_ne])
    have klt: "k <o hd fs" using khd hdlt ole_olt_trans by blast
    have kA: "k \<in> A" using kbs d1 bx by auto
    have hA: "hd fs \<in> A" using fs_ne d2 byy by auto
    have "hd fs \<in> set_mset (mset fs)" using fs_ne by simp
    thus "\<exists>j \<in> set_mset (mset fs). (k, j) \<in> ?r" using klt kA hA by auto
  qed
  have "(mset pre + mset bs, mset pre + mset fs) \<in> mult ?r"
    by (rule one_step_implies_mult[OF Jne dom])
  thus ?thesis using d1 d2 by simp
qed

subsection \<open>The level-\<open>m\<close> argument classes and the descent of the residual core\<close>

definition ArgsL :: "nat \<Rightarrow> three set" where
  "ArgsL m = (\<Union>x \<in> {t \<in> NF. maxsub t = m}. set (sargs x))"

lemma sargs_subset_ArgsL: "x \<in> NF \<Longrightarrow> maxsub x = m \<Longrightarrow> set (sargs x) \<subseteq> ArgsL m"
  unfolding ArgsL_def by auto

text \<open>\<open>cnf\<close> is hereditary along the sum arguments.\<close>

lemma cnf_sargs: "cnf x \<Longrightarrow> b \<in> set (sargs x) \<Longrightarrow> cnf b"
proof (induction x)
  case Z thus ?case by simp
next
  case (P a b' c)
  have cb: "cnf b'" using P.prems(1) by (cases c) auto
  have cc: "cnf c" using P.prems(1) by (cases c) auto
  from P.prems(2) consider "b = b'" | "b \<in> set (sargs c)" by auto
  thus ?case
  proof cases
    case 1 thus ?thesis using cb by simp
  next
    case 2 thus ?thesis using cc P.IH(2) by blast
  qed
qed

lemma cnf_ArgsL: "b \<in> ArgsL m \<Longrightarrow> cnf b"
  unfolding ArgsL_def using cnf_NF cnf_sargs by auto

text \<open>Summand singletons of the level-\<open>m\<close> arguments, and their arguments.\<close>

definition SingA :: "nat \<Rightarrow> three set" where
  "SingA m = (\<Union>b \<in> ArgsL m. set (summands b))"

definition ArgsA :: "nat \<Rightarrow> three set" where
  "ArgsA m = {c. \<exists>a. P a c Z \<in> SingA m}"

lemma summands_subset_SingA: "b \<in> ArgsL m \<Longrightarrow> set (summands b) \<subseteq> SingA m"
  unfolding SingA_def by auto

fun singdest :: "three \<Rightarrow> nat \<times> three" where
  "singdest Z = (0, Z)"
| "singdest (P a c d) = (a, c)"

subsection \<open>Level 0: the base of the ladder (PrSS-style accessibility)\<close>

text \<open>At level \<open>0\<close> all subscripts are \<open>0\<close>, so the singleton order never drops a
  subscript and the PrSS argument (hereditary multisets, Dershowitz\<dash>Manna
  accessibility) closes outright: \<open><o\<close> is WF on the class of CNF terms with
  \<open>maxsub = 0\<close>.  This is the base case of the level ladder; the induction step
  (level \<open>m\<close> from levels \<open>< m\<close>) is the Buchholz-collapse core, still open.\<close>

abbreviation lvl0 :: "three \<Rightarrow> bool" where
  "lvl0 t \<equiv> cnf t \<and> maxsub t = 0"

definition olt0 :: "three \<Rightarrow> three \<Rightarrow> bool" where
  "olt0 c f \<longleftrightarrow> c <o f \<and> lvl0 c \<and> lvl0 f"

lemma transp_olt0: "transp olt0"
  by (auto intro: olt_trans simp: transp_def olt0_def)

lemma cnf_summands: "cnf x \<Longrightarrow> s \<in> set (summands x) \<Longrightarrow> cnf s"
proof (induction x)
  case Z thus ?case by simp
next
  case (P a b c)
  have cb: "cnf b" using P.prems(1) by (cases c) auto
  have cc: "cnf c" using P.prems(1) by (cases c) auto
  from P.prems(2) consider "s = P a b Z" | "s \<in> set (summands c)" by auto
  thus ?case
  proof cases
    case 1 thus ?thesis using cb by simp
  next
    case 2 thus ?thesis using cc P.IH(2) by blast
  qed
qed

lemma maxsub_summands_le: "s \<in> set (summands x) \<Longrightarrow> maxsub s \<le> maxsub x"
proof (induction x)
  case Z thus ?case by simp
next
  case (P a b c)
  from P.prems consider "s = P a b Z" | "s \<in> set (summands c)" by auto
  thus ?case
  proof cases
    case 1 thus ?thesis by simp
  next
    case 2 thus ?thesis using P.IH(2) by fastforce
  qed
qed

lemma sargs_size: "b \<in> set (sargs x) \<Longrightarrow> size b < size x"
proof (induction x)
  case Z thus ?case by simp
next
  case (P a b' c)
  from P.prems consider "b = b'" | "b \<in> set (sargs c)" by auto
  thus ?case
  proof cases
    case 1 thus ?thesis by simp
  next
    case 2 thus ?thesis using P.IH(2)[OF 2] by simp
  qed
qed

text \<open>PrSS machinery: accessibility passes through the multiset extension.\<close>

definition rA0 :: "three \<Rightarrow> three \<Rightarrow> bool" where
  "rA0 x y \<longleftrightarrow> olt0 x y \<and> Wellfounded.accp olt0 x"

lemma rA0_le_olt0: "rA0 \<le> olt0"
  by (auto simp: rA0_def)

lemma wfp_rA0: "wfp rA0"
proof (rule accp_wfpI, rule allI)
  fix x
  have acc_imp: "Wellfounded.accp olt0 z \<Longrightarrow> Wellfounded.accp rA0 z" for z
    using accp_subset[OF rA0_le_olt0] by (auto simp: le_fun_def)
  show "Wellfounded.accp rA0 x"
  proof (rule accp.accI)
    fix y assume "rA0 y x"
    hence "Wellfounded.accp olt0 y" by (simp add: rA0_def)
    thus "Wellfounded.accp rA0 y" by (rule acc_imp)
  qed
qed

lemma wfp_multp_rA0: "wfp (multp rA0)"
  using wfp_rA0 by (rule wfp_multp)

lemma accp_multp_olt0:
  assumes "\<forall>x \<in># M. Wellfounded.accp olt0 x"
  shows "Wellfounded.accp (multp olt0) M"
proof -
  have "Wellfounded.accp (multp rA0) M"
    using wfp_multp_rA0 by (simp add: wfp_iff_accp)
  thus ?thesis using assms
  proof (induction M rule: accp_induct_rule)
    case (1 M)
    show ?case
    proof (rule accp.accI)
      fix N assume "multp olt0 N M"
      from multp_implies_one_step[OF transp_olt0 this]
      obtain I J K where dec: "M = I + J" "N = I + K" "J \<noteq> {#}"
        and Klt: "\<forall>k \<in># K. \<exists>x \<in># J. olt0 k x" by blast
      have accN: "\<forall>x \<in># N. Wellfounded.accp olt0 x"
      proof
        fix x assume "x \<in># N"
        then consider "x \<in># I" | "x \<in># K" using dec by auto
        thus "Wellfounded.accp olt0 x"
        proof cases
          case 1 thus ?thesis using "1.prems" dec by auto
        next
          case 2
          then obtain y where "y \<in># J" "olt0 x y" using Klt by blast
          hence "Wellfounded.accp olt0 y" using "1.prems" dec by auto
          thus ?thesis using \<open>olt0 x y\<close> by (rule accp_downward)
        qed
      qed
      have "\<forall>k \<in># K. \<exists>x \<in># J. rA0 k x"
      proof
        fix k assume "k \<in># K"
        then obtain x where "x \<in># J" "olt0 k x" using Klt by blast
        moreover have "Wellfounded.accp olt0 k"
          using accN \<open>k \<in># K\<close> dec by auto
        ultimately show "\<exists>x \<in># J. rA0 k x" by (auto simp: rA0_def)
      qed
      hence "multp rA0 N M"
        using dec one_step_implies_multp[of J K rA0 I] by simp
      thus "Wellfounded.accp (multp olt0) N"
        using "1.IH" accN by blast
    qed
  qed
qed

text \<open>The order embeds sums into multisets of summands (level-0 instance).\<close>

lemma olt0_summands_multp:
  assumes "olt0 w t"
  shows "multp olt0 (mset (summands w)) (mset (summands t))"
proof -
  have cw: "cnf w" and lw: "lvl0 w" and lt': "lvl0 t" and wt: "w <o t"
    using assms by (auto simp: olt0_def)
  have sub: "set (summands u) \<subseteq> {s. lvl0 s}" if u: "lvl0 u" for u
  proof
    fix s assume s: "s \<in> set (summands u)"
    have "cnf s" using cnf_summands s u by blast
    moreover have "maxsub s = 0" using maxsub_summands_le[OF s] u by simp
    ultimately show "s \<in> {s. lvl0 s}" by simp
  qed
  have "(mset (summands w), mset (summands t))
          \<in> mult {(s,t). s <o t \<and> s \<in> {s. lvl0 s} \<and> t \<in> {s. lvl0 s}}"
    by (rule olt_summands_mult[OF cw wt sub[OF lw] sub[OF lt']])
  moreover have "{(s,t). s <o t \<and> s \<in> {s. lvl0 s} \<and> t \<in> {s. lvl0 s}}
                   = {(x,y). olt0 x y}"
    by (auto simp: olt0_def)
  ultimately show ?thesis by (simp add: multp_def)
qed

lemma Z_acc0: "Wellfounded.accp olt0 Z"
proof (rule accp.accI)
  fix y assume "olt0 y Z"
  thus "Wellfounded.accp olt0 y" using not_olt_Z by (auto simp: olt0_def)
qed

text \<open>A sum is accessible once its summand multiset is.\<close>

lemma sum_acc_aux:
  "Wellfounded.accp (multp olt0) M \<Longrightarrow> lvl0 w \<Longrightarrow> mset (summands w) = M
     \<Longrightarrow> Wellfounded.accp olt0 w"
proof (induction M arbitrary: w rule: accp_induct_rule)
  case (1 M)
  show ?case
  proof (rule accp.accI)
    fix v assume v: "olt0 v w"
    have lv: "lvl0 v" using v by (simp add: olt0_def)
    have "multp olt0 (mset (summands v)) (mset (summands w))"
      by (rule olt0_summands_multp[OF v])
    hence step: "multp olt0 (mset (summands v)) M" using "1.prems"(2) by simp
    show "Wellfounded.accp olt0 v"
      by (rule "1.IH"[OF step lv refl])
  qed
qed

lemma sum_acc:
  assumes "lvl0 v" "Wellfounded.accp (multp olt0) (mset (summands v))"
  shows "Wellfounded.accp olt0 v"
  by (rule sum_acc_aux[OF assms(2) assms(1) refl])

text \<open>The level-0 singleton constructor preserves accessibility (no subscript can
  drop below \<open>0\<close>, so all predecessors of \<open>p\<^bsub>0\<^esub>(b)\<close> are sums of \<open>p\<^bsub>0\<^esub>(d\<^sub>i)\<close> with
  \<open>d\<^sub>i <\<^sub>o b\<close>: accessible by the accessibility induction on \<open>b\<close>).\<close>

lemma sing0_acc:
  "Wellfounded.accp olt0 b \<Longrightarrow> lvl0 b \<Longrightarrow> Wellfounded.accp olt0 (P 0 b Z)"
proof (induction b rule: accp_induct_rule)
  case (1 b)
  show ?case
  proof (rule accp.accI)
    fix v assume v: "olt0 v (P 0 b Z)"
    have lv: "lvl0 v" and vlt: "v <o P 0 b Z" using v by (auto simp: olt0_def)
    show "Wellfounded.accp olt0 v"
    proof (cases v)
      case Z thus ?thesis using Z_acc0 by simp
    next
      case (P a d e)
      have a0: "a = 0" using lv P by simp
      have dlt: "d <o b" using vlt P a0 not_olt_Z by auto
      have ld: "lvl0 d" using lv P by (cases e) auto
      have dacc: "olt0 d b" using dlt ld "1.prems" by (simp add: olt0_def)
      \<comment> \<open>every summand of \<open>v\<close> is \<open>p\<^bsub>0\<^esub>(d\<^sub>i)\<close> with \<open>d\<^sub>i \<le>\<^sub>o d <\<^sub>o b\<close>, hence accessible
          by the accessibility induction hypothesis on \<open>b\<close>\<close>
      have summacc: "\<forall>s \<in># mset (summands v). Wellfounded.accp olt0 s"
      proof
        fix s assume "s \<in># mset (summands v)"
        hence sv: "s \<in> set (summands v)" by simp
        obtain a' d' where s: "s = P a' d' Z" using summands_shape[OF sv] by blast
        have ls: "lvl0 s" using cnf_summands maxsub_summands_le sv lv by fastforce
        have a'0: "a' = 0" using ls s by simp
        have cnfv: "cnf v" using lv by simp
        have vP: "v = P 0 d e" using P a0 by simp
        have d'le: "s \<le>o P 0 d Z"
        proof -
          from sv vP consider "s = P 0 d Z" | "s \<in> set (summands e)" by auto
          thus ?thesis
          proof cases
            case 1 thus ?thesis by simp
          next
            case 2 show ?thesis by (rule summands_le_hd[OF cnfv vP 2])
          qed
        qed
        have "d' \<le>o d" using d'le s a'0 by auto
        hence d'b: "d' <o b" using dlt ole_olt_trans by blast
        have ld': "lvl0 d'" using ls s a'0 by (cases "d' = Z") auto
        have "olt0 d' b" using d'b ld' "1.prems" by (simp add: olt0_def)
        hence "Wellfounded.accp olt0 (P 0 d' Z)"
          using "1.IH" ld' by blast
        thus "Wellfounded.accp olt0 s" using s a'0 by simp
      qed
      have "Wellfounded.accp (multp olt0) (mset (summands v))"
        by (rule accp_multp_olt0[OF summacc])
      thus ?thesis by (rule sum_acc[OF lv, rotated])
    qed
  qed
qed

text \<open>\<^bold>\<open>Master\<close>: every level-0 CNF term is accessible (strong induction on size;
  the sum arguments are proper subterms).\<close>

lemma lvl0_acc: "lvl0 t \<Longrightarrow> Wellfounded.accp olt0 t"
proof (induction t rule: measure_induct_rule[where f = size])
  case (less t)
  show ?case
  proof (cases t)
    case Z thus ?thesis using Z_acc0 by simp
  next
    case (P a b c)
    have summacc: "\<forall>s \<in># mset (summands t). Wellfounded.accp olt0 s"
    proof
      fix s assume "s \<in># mset (summands t)"
      hence sv: "s \<in> set (summands t)" by simp
      obtain a' d' where s: "s = P a' d' Z" using summands_shape[OF sv] by blast
      have ls: "lvl0 s" using cnf_summands maxsub_summands_le sv less.prems by fastforce
      have a'0: "a' = 0" using ls s by simp
      have ld': "lvl0 d'" using ls s a'0 by (cases "d' = Z") auto
      \<comment> \<open>\<open>d'\<close> is a sum argument of \<open>t\<close>, hence a proper subterm\<close>
      have "d' \<in> set (sargs t)"
      proof -
        have "set (summands t) = (\<lambda>(a,b). P a b Z) ` set (zip (tops t) (sargs t))"
          by (induction t) auto
        thus ?thesis using sv s
          by (force dest: set_zip_rightD)
      qed
      hence "size d' < size t" by (rule sargs_size)
      hence "Wellfounded.accp olt0 d'" using less.IH ld' by blast
      hence "Wellfounded.accp olt0 (P 0 d' Z)" using sing0_acc ld' by blast
      thus "Wellfounded.accp olt0 s" using s a'0 by simp
    qed
    have "Wellfounded.accp (multp olt0) (mset (summands t))"
      by (rule accp_multp_olt0[OF summacc])
    thus ?thesis by (rule sum_acc[OF less.prems, rotated])
  qed
qed

theorem wf_olt0: "wf {(c,f). c <o f \<and> lvl0 c \<and> lvl0 f}"
proof -
  have "wfp olt0"
  proof (rule accp_wfpI, rule allI)
    fix x
    show "Wellfounded.accp olt0 x"
    proof (cases "lvl0 x")
      case True thus ?thesis by (rule lvl0_acc)
    next
      case False
      show ?thesis
      proof (rule accp.accI)
        fix y assume "olt0 y x"
        hence "lvl0 x" by (simp add: olt0_def)
        thus "Wellfounded.accp olt0 y" using False by simp
      qed
    qed
  qed
  hence "wf {(x,y). olt0 x y}" by (simp add: wfp_def)
  moreover have "{(x,y). olt0 x y} = {(c,f). c <o f \<and> lvl0 c \<and> lvl0 f}"
    by (auto simp: olt0_def)
  ultimately show ?thesis by simp
qed

text \<open>\<^bold>\<open>The residual core\<close>, two levels in: WF of \<open><o\<close> on the arguments (of any
  subscript) occurring inside the level-\<open>m\<close> sum arguments.  The level-\<open>0\<close>
  instance follows from the base theorem \<open>wf_olt0\<close>; the induction step (level
  \<open>m\<close> from levels \<open>< m\<close>) is the Buchholz-collapse core, still open.\<close>

lemma wf_ArgsA:
  "wf {(c,f). c <o f \<and> c \<in> ArgsA m \<and> f \<in> ArgsA m}"
  sorry

lemma wf_SingA:
  "wf {(s,t). s <o t \<and> s \<in> SingA m \<and> t \<in> SingA m}"
proof (rule wf_subset[OF wf_inv_image[OF wf_lex_prod[OF wf_less_than wf_ArgsA[of m]], of singdest]])
  show "{(s,t). s <o t \<and> s \<in> SingA m \<and> t \<in> SingA m}
          \<subseteq> inv_image (less_than <*lex*> {(c,f). c <o f \<and> c \<in> ArgsA m \<and> f \<in> ArgsA m}) singdest"
  proof (rule subrelI)
    fix s t assume st: "(s,t) \<in> {(s,t). s <o t \<and> s \<in> SingA m \<and> t \<in> SingA m}"
    then have lt: "s <o t" and sS: "s \<in> SingA m" and tS: "t \<in> SingA m" by auto
    obtain a c where s: "s = P a c Z"
      using sS summands_shape unfolding SingA_def by blast
    obtain e f where t: "t = P e f Z"
      using tS summands_shape unfolding SingA_def by blast
    have cA: "c \<in> ArgsA m" using sS s unfolding ArgsA_def by auto
    have fA: "f \<in> ArgsA m" using tS t unfolding ArgsA_def by auto
    have "a < e \<or> (a = e \<and> c <o f)" using lt unfolding s t by auto
    thus "(s,t) \<in> inv_image (less_than <*lex*> {(c,f). c <o f \<and> c \<in> ArgsA m \<and> f \<in> ArgsA m}) singdest"
      using s t cA fA by (auto simp: inv_image_def)
  qed
qed

lemma wf_ArgsL:
  "wf {(b,f). b <o f \<and> b \<in> ArgsL m \<and> f \<in> ArgsL m}"
proof (rule wf_subset[OF wf_inv_image[OF wf_mult[OF wf_SingA[of m]], of "\<lambda>b. mset (summands b)"]])
  show "{(b,f). b <o f \<and> b \<in> ArgsL m \<and> f \<in> ArgsL m}
          \<subseteq> inv_image (mult {(s,t). s <o t \<and> s \<in> SingA m \<and> t \<in> SingA m}) (\<lambda>b. mset (summands b))"
  proof (rule subrelI)
    fix b f assume "(b,f) \<in> {(b,f). b <o f \<and> b \<in> ArgsL m \<and> f \<in> ArgsL m}"
    then have lt: "b <o f" and bA: "b \<in> ArgsL m" and fA: "f \<in> ArgsL m" by auto
    have "(mset (summands b), mset (summands f))
            \<in> mult {(s,t). s <o t \<and> s \<in> SingA m \<and> t \<in> SingA m}"
      by (rule olt_summands_mult[OF cnf_ArgsL[OF bA] lt
            summands_subset_SingA[OF bA] summands_subset_SingA[OF fA]])
    thus "(b,f) \<in> inv_image (mult {(s,t). s <o t \<and> s \<in> SingA m \<and> t \<in> SingA m})
                    (\<lambda>b. mset (summands b))"
      by (simp add: inv_image_def)
  qed
qed

lemma wf_level_from_args:
  "wf {(w,x). w <o x \<and> x \<in> NF \<and> w \<in> NF \<and> maxsub w = m \<and> maxsub x = m}"
proof (rule wf_subset[OF wf_inv_image[OF wf_mult[OF wf_ArgsL[of m]], of margs]])
  show "{(w,x). w <o x \<and> x \<in> NF \<and> w \<in> NF \<and> maxsub w = m \<and> maxsub x = m}
          \<subseteq> inv_image (mult {(b,f). b <o f \<and> b \<in> ArgsL m \<and> f \<in> ArgsL m}) margs"
  proof (rule subrelI)
    fix w x assume "(w,x) \<in> {(w,x). w <o x \<and> x \<in> NF \<and> w \<in> NF \<and> maxsub w = m \<and> maxsub x = m}"
    then have lt: "w <o x" and xNF: "x \<in> NF" and wNF: "w \<in> NF"
      and mw: "maxsub w = m" and mx: "maxsub x = m" by auto
    have "(margs w, margs x) \<in> mult {(b,f). b <o f \<and> b \<in> ArgsL m \<and> f \<in> ArgsL m}"
      by (rule olt_sum_mult[OF NF_zerotops[OF wNF] NF_zerotops[OF xNF] cnf_NF[OF wNF] lt
            sargs_subset_ArgsL[OF wNF mw] sargs_subset_ArgsL[OF xNF mx]])
    thus "(w,x) \<in> inv_image (mult {(b,f). b <o f \<and> b \<in> ArgsL m \<and> f \<in> ArgsL m}) margs"
      by (simp add: inv_image_def)
  qed
qed

theorem wfE_from_args:
  "wf {(w,x). w <o x \<and> x \<in> NF \<and> w \<in> NF \<and> maxsub w = maxsub x}"
proof -
  define r where "r \<equiv> \<lambda>m. {(w,x). w <o x \<and> x \<in> NF \<and> w \<in> NF \<and> maxsub w = m \<and> maxsub x = m}"
  have eq: "{(w,x). w <o x \<and> x \<in> NF \<and> w \<in> NF \<and> maxsub w = maxsub x} = (\<Union>m. r m)"
    unfolding r_def by auto
  show ?thesis unfolding eq
  proof (rule wf_UN)
    show "wf (r m)" for m unfolding r_def by (rule wf_level_from_args)
    fix m k assume "r m \<noteq> r k"
    hence "m \<noteq> k" by auto
    thus "Domain (r m) \<inter> Range (r k) = {}" unfolding r_def by auto
  qed
qed

subsection \<open>Top-level: PSS termination, modulo the argument core\<close>

theorem wf_Rnf: "wf Rnf"
  by (rule wf_Rnf_from_within_level[OF wfE_from_args])

text \<open>\<^bold>\<open>PSS termination\<close> (pure-lex, ordinal-free), modulo \<open>wf_ArgsL\<close> \<dash> the sole
  remaining obligation of the whole development: WF of \<open><o\<close> on the level-\<open>m\<close>
  argument class (the Buchholz collapse core).\<close>

theorem PSS_terminates: "wf {(T,M). M \<in> ST_PS \<and> step M T}"
  by (rule step_terminates[OF wf_Rnf])

end
