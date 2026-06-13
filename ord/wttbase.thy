theory wttbase
  imports otembed "YAPSS.wf" "YAPSS.wtt"
begin

text \<open>
  \<^bold>\<open>The \<open>maxr1 = 0\<close> base of the level induction\<close> (memo 続88).  When all row-1
  values are \<open>0\<close>, every subscript of the translate is \<open>0\<close>, no re-climb is
  possible, and the (cnf) translate is already a Buchholz OT term (\<open>wf3\<close>).
  Hence the \<open>maxr1 = 0\<close> fragment terminates directly via \<open>wf_olt_wf3\<close>, with no
  \<open>nrm\<close> and no value-comparison crux.  This is the bottom of the \<open>diag_acc\<close>
  level induction; the crux lives strictly at \<open>maxr1 \<ge> 2\<close> (續86).
\<close>

text \<open>An argument sits strictly below its own principal (all-zero subscripts).\<close>

lemma olt_arg_principal0:
  "subs (P 0 b c) \<subseteq> {0} \<Longrightarrow> olt b (P 0 b c)"
proof (induction b arbitrary: c)
  case Z
  show ?case by simp
next
  case (P a f g)
  have a0: "a = 0" using P.prems by auto
  have sf: "subs (P 0 f g) \<subseteq> {0}" using P.prems a0 by auto
  have "olt f (P 0 f g)" by (rule P.IH(1)[OF sf])
  thus ?case using a0 by simp
qed

text \<open>A tail sits strictly below the whole principal sum (cnf, all-zero subs).\<close>

lemma olt_tail_principal0:
  "cnf (P 0 b c) \<Longrightarrow> subs (P 0 b c) \<subseteq> {0} \<Longrightarrow> olt c (P 0 b c)"
proof (induction c arbitrary: b)
  case Z
  show ?case by simp
next
  case (P e f g)
  have e0: "e = 0" using P.prems(2) by auto
  have ndom: "\<not> olt b f" using P.prems(1) e0 by auto
  have cnffg: "cnf (P 0 f g)" using P.prems(1) e0 by auto
  have sfg: "subs (P 0 f g) \<subseteq> {0}" using P.prems(2) e0 by auto
  show ?case
  proof (cases "olt f b")
    case True
    thus ?thesis using e0 by simp
  next
    case False
    hence fb: "f = b" using ndom olt_total by blast
    have og: "olt g (P 0 f g)" by (rule P.IH(2)[OF cnffg sfg])
    show ?thesis using e0 fb og by simp
  qed
qed

text \<open>OT3 for all-zero-subscript cnf terms: every level-0 critical is below.\<close>

lemma OT3all:
  "cnf t \<Longrightarrow> wf3 t \<Longrightarrow> subs t \<subseteq> {0} \<Longrightarrow> \<forall>x \<in> Gterm 0 t. olt x t"
proof (induction t)
  case Z
  show ?case by simp
next
  case (P a b c)
  have a0: "a = 0" using P.prems(3) by auto
  have cnfb: "cnf b" using P.prems(1) by (cases c) auto
  have cnfc: "cnf c" using P.prems(1) by (cases c) auto
  have wfb: "wf3 b" and wfc: "wf3 c" and ot3b: "\<forall>x \<in> Gterm a b. olt x b"
    using P.prems(2) by auto
  have sb: "subs b \<subseteq> {0}" and sc: "subs c \<subseteq> {0}" using P.prems(3) by auto
  have sbc: "subs (P 0 b c) \<subseteq> {0}" using P.prems(3) a0 by auto
  have argb: "olt b (P 0 b c)" by (rule olt_arg_principal0[OF sbc])
  have tailc: "olt c (P 0 b c)"
    by (rule olt_tail_principal0[OF _ sbc]) (use P.prems(1) a0 in simp)
  have Gc: "\<forall>x \<in> Gterm 0 c. olt x c" by (rule P.IH(2)[OF cnfc wfc sc])
  have "Gterm 0 (P 0 b c) = insert b (Gterm 0 b) \<union> Gterm 0 c" by simp
  thus ?case
  proof -
    have "\<forall>x \<in> insert b (Gterm 0 b) \<union> Gterm 0 c. olt x (P 0 b c)"
    proof
      fix x assume "x \<in> insert b (Gterm 0 b) \<union> Gterm 0 c"
      then consider "x = b" | "x \<in> Gterm 0 b" | "x \<in> Gterm 0 c" by auto
      thus "olt x (P 0 b c)"
      proof cases
        case 1 thus ?thesis using argb by simp
      next
        case 2
        hence "olt x b" using ot3b a0 by simp
        thus ?thesis using argb olt_trans by blast
      next
        case 3
        hence "olt x c" using Gc by simp
        thus ?thesis using tailc olt_trans by blast
      qed
    qed
    thus ?thesis using a0 by simp
  qed
qed

text \<open>Main base lemma: an all-zero-subscript cnf term is a Buchholz OT term.\<close>

lemma wf3_of_cnf_subs0:
  "cnf t \<Longrightarrow> subs t \<subseteq> {0} \<Longrightarrow> wf3 t"
proof (induction t)
  case Z
  show ?case by simp
next
  case (P a b c)
  have a0: "a = 0" using P.prems(2) by auto
  have cnfb: "cnf b" using P.prems(1) by (cases c) auto
  have cnfc: "cnf c" using P.prems(1) by (cases c) auto
  have sb: "subs b \<subseteq> {0}" and sc: "subs c \<subseteq> {0}" using P.prems(2) by auto
  have wfb: "wf3 b" by (rule P.IH(1)[OF cnfb sb])
  have wfc: "wf3 c" by (rule P.IH(2)[OF cnfc sc])
  have ot3: "\<forall>x \<in> Gterm a b. olt x b"
    using OT3all[OF cnfb wfb sb] a0 by simp
  have hd: "hdle c (P a b Z)"
  proof (cases c)
    case Z thus ?thesis by simp
  next
    case (P e f g)
    have e0: "e = 0" using P.prems(2) P by auto
    have "\<not> olt b f" using P.prems(1) a0 P e0 by auto
    hence "olt f b \<or> f = b" using olt_total by blast
    thus ?thesis using a0 P e0 by auto
  qed
  show ?case using wfb wfc ot3 hd a0 by simp
qed

text \<open>Consequence for standard forms: a \<open>maxr1 = 0\<close> standard form translates
  into the Buchholz OT (\<open>wf3\<close>) \<dash> the crux-free base level.\<close>

lemma wf3_translate_subs0:
  assumes M: "M \<in> ST_PS" and z: "\<forall>p \<in> set M. snd p = 0"
  shows "wf3 (translate M)"
proof -
  have "cnf (translate M)" by (rule cnf_ST_PS[OF M])
  moreover have "subs (translate M) \<subseteq> {0}"
    using subs_translate[of M] z by auto
  ultimately show ?thesis by (rule wf3_of_cnf_subs0)
qed

text \<open>\<^bold>\<open>The \<open>maxr1 = 0\<close> fragment is accessible\<close> (crux-free).  Its game stays
  in the all-zero-row-1 fragment (\<open>oper_snd_subset\<close>), where \<open>translate\<close> lands
  in \<open>wf3\<close> and strictly decreases (\<open>m_step_decreases\<close>), so termination follows
  from \<open>wf_olt_wf3\<close> with no \<open>nrm\<close>.  The fragment closure facts (below) are the
  ingredients; the accessibility assembly via \<open>wf_induct\<close> is the next step.\<close>

lemma subs0_step_closed:
  assumes "M \<in> ST_PS" and "\<forall>p \<in> set M. snd p = 0" and "step M T"
  shows "T \<in> ST_PS \<and> (\<forall>p \<in> set T. snd p = 0)"
proof
  show TST: "T \<in> ST_PS" using assms(1,3) by (rule step_in_ST_PS)
  from assms(3) obtain n where TM: "T = M[n]" by (auto elim!: step.cases)
  show "\<forall>p \<in> set T. snd p = 0"
  proof
    fix q assume "q \<in> set T"
    hence "snd q \<in> snd ` set (M[n])" using TM by auto
    hence "snd q \<in> snd ` set M" using oper_snd_subset by blast
    thus "snd q = 0" using assms(2) by auto
  qed
qed

lemma subs0_step_decreases:
  assumes "M \<in> ST_PS" and "\<forall>p \<in> set M. snd p = 0" and "step M T"
  shows "(translate T, translate M) \<in> {(w,x). olt w x \<and> wf3 w \<and> wf3 x}"
proof -
  from assms(3) obtain n where L: "1 < Lng M" and n: "1 \<le> n" and TM: "T = M[n]"
    by (auto elim!: step.cases)
  have TST: "T \<in> ST_PS" using assms(1,3) by (rule step_in_ST_PS)
  have Tz: "\<forall>p \<in> set T. snd p = 0"
    using subs0_step_closed[OF assms] by simp
  have "olt (translate T) (translate M)" using m_step_decreases[OF L n] TM by simp
  moreover have "wf3 (translate M)" by (rule wf3_translate_subs0[OF assms(1,2)])
  moreover have "wf3 (translate T)" by (rule wf3_translate_subs0[OF TST Tz])
  ultimately show ?thesis by simp
qed

end



