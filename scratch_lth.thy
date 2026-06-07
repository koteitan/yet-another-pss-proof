theory scratch_lth
  imports wflevel
begin

text \<open>Scratch: attempt the collapse-closure lemma L_Th
      "d accessible \<Longrightarrow> Th s d accessible" by acc-induction on d,
      to isolate exactly the residual p<s predecessor case.\<close>

lemma L_Th_naive:
  assumes "d \<in> Wellfounded.acc oltRw" "wfo d"
  shows "Th s d \<in> Wellfounded.acc oltRw"
proof -
  from assms(1) have "wfo d \<longrightarrow> (\<forall>s. Th s d \<in> Wellfounded.acc oltRw)"
  proof (induction set: Wellfounded.acc)
  case (1 d)
  note d_acc = "1.hyps"     \<comment> \<open>d \<in> acc oltRw\<close>
  note IH = "1.IH"          \<comment> \<open>\<And>y. (y,d)\<in>oltRw \<Longrightarrow> wfo y \<longrightarrow> (\<forall>s. Th s y \<in> acc oltRw)\<close>
  have pred_acc: "\<And>y. (y, d) \<in> oltRw \<Longrightarrow> y \<in> Wellfounded.acc oltRw"
    using d_acc by (blast intro: acc_downward)
  show ?case
  proof
    assume wd: "wfo d"
    show "\<forall>s. Th s d \<in> Wellfounded.acc oltRw"
    proof
      fix s
      show "Th s d \<in> Wellfounded.acc oltRw"
      proof (rule accI)
    fix r assume rR: "(r, Th s d) \<in> oltRw"
    hence rlt: "r <\<^sub>o Th s d" and wr: "wfo r" by auto
    \<comment> \<open>helper: a wfo principal dominated by a critical subterm of d is accessible\<close>
    have dom_acc: "\<And>q. wfo q \<Longrightarrow> isH q \<Longrightarrow> (\<exists>\<gamma>\<in>Kn s d. q \<le>\<^sub>o \<gamma>) \<Longrightarrow> q \<in> Wellfounded.acc oltRw"
    proof -
      fix q assume wq: "wfo q" and hq: "isH q" and ex: "\<exists>\<gamma>\<in>Kn s d. q \<le>\<^sub>o \<gamma>"
      from ex obtain \<gamma> where g: "\<gamma> \<in> Kn s d" "q \<le>\<^sub>o \<gamma>" by auto
      have wg: "wfo \<gamma>" using wfo_Kn[OF wd g(1)] .
      have gd: "\<gamma> \<le>\<^sub>o d" using Kn_le_self[OF g(1)] .
      have g_acc: "\<gamma> \<in> Wellfounded.acc oltRw"
      proof (cases "\<gamma> = d")
        case True thus ?thesis by (simp add: d_acc)
      next
        case False
        with gd have "\<gamma> <\<^sub>o d" by simp
        hence "(\<gamma>, d) \<in> oltRw" using wg wd by simp
        thus ?thesis by (rule pred_acc)
      qed
      show "q \<in> Wellfounded.acc oltRw"
      proof (cases "q = \<gamma>")
        case True thus ?thesis by (simp add: g_acc)
      next
        case False
        with g(2) have "q <\<^sub>o \<gamma>" by simp
        hence qg: "(q, \<gamma>) \<in> oltRw" using wq wg by simp
        show ?thesis by (rule acc_downward[OF g_acc qg])
      qed
    qed
    show "r \<in> Wellfounded.acc oltRw"
    proof (cases r)
      case (Om m)
      have "Om m <\<^sub>o Th s d" using rlt Om by simp
      hence "\<exists>\<gamma>\<in>Kn s d. Om m \<le>\<^sub>o \<gamma>" by simp
      thus ?thesis using dom_acc[of "Om m"] wr Om by simp
    next
      case (Su xs)
      \<comment> \<open>sum predecessor: all summands principal and <o Th s d; lift via bag\<close>
      show ?thesis sorry
    next
      case (Th p e)
      have wpe: "wfo e" using wr Th by simp
      from rlt Th
      have disj: "(\<exists>\<gamma>\<in>Kn s d. Th p e \<le>\<^sub>o \<gamma>)
          \<or> ((\<forall>\<gamma>\<in>Kn p e. \<gamma> <\<^sub>o Th s d) \<and> (p < s \<or> (p = s \<and> e <\<^sub>o d)))" by simp
      from disj show ?thesis
      proof
        assume "\<exists>\<gamma>\<in>Kn s d. Th p e \<le>\<^sub>o \<gamma>"
        thus ?thesis using dom_acc[of "Th p e"] wr Th by simp
      next
        assume A: "(\<forall>\<gamma>\<in>Kn p e. \<gamma> <\<^sub>o Th s d) \<and> (p < s \<or> (p = s \<and> e <\<^sub>o d))"
        hence crit: "\<forall>\<gamma>\<in>Kn p e. \<gamma> <\<^sub>o Th s d" by simp
        from A consider (eq) "p = s" "e <\<^sub>o d" | (lt) "p < s" by auto
        thus ?thesis
        proof cases
          case eq
          \<comment> \<open>same subscript, smaller argument: main IH\<close>
          have ed: "(e, d) \<in> oltRw" using eq(2) wpe wd by simp
          have "Th s e \<in> Wellfounded.acc oltRw" using IH[OF ed] wpe by blast
          thus ?thesis using Th eq(1) by simp
        next
          case lt
          \<comment> \<open>THE GAP: p < s cross-subscript predecessor\<close>
          show ?thesis sorry
        qed
      qed
    qed
      qed
    qed
  qed
  qed
  thus ?thesis using assms(2) by blast
qed

end
