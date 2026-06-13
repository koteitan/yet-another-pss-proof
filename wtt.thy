theory wtt
  imports "proofs" "wf"
begin

text \<open>
  \<^bold>\<open>Direct termination, Buchholz-Hydra \<open>W = T\<close> style\<close> (memo 続79〜85).

  This route proves PSS termination \<^emph>\<open>without\<close> the order \<open><o\<close>, without
  \<open>translate\<close>, and without the value normalizer \<open>nrm\<close>.  It mirrors Buchholz
  1987 ("An independence result for \<open>(\<Pi>\<^sup>1\<^sub>1\<hyphen>CA)+BI\<close>"), where the Hercules/Hydra
  game is shown to terminate by a direct inductive argument that every term is
  in the "killable" set \<open>W = T\<close> (Theorems I/II, §2), using closure of \<open>W\<close> under
  sum (Lemma 2.4) and under the principal constructor (Lemma 2.5) \<dash> never
  comparing ordinal values.

  Caveat (memo 続78\<hyphen>84): the PSS principal \<open>p\<^bsub>a\<^esub>(b)\<close> is \<^emph>\<open>not\<close> Buchholz's
  \<open>\<psi>\<close>/\<open>D\<^bsub>v\<^esub>\<close>, so the literal \<open>[n]\<close>/\<open>dom\<close>/\<open>\<ll>\<^sub>k\<close> rules are not portable; only the
  \<^emph>\<open>method\<close> (direct accessibility induction, sum/principal closure) transfers.
  The value-comparison route (\<open>nrm_order_pres\<close>) is discarded: its core was the
  7th soundness incident (false at closure+5/+6, \<open>E6_value\<close>/\<open>ginv\<close>/\<open>nbcK\<close>).

  Status: the generation reduction below is proved; the irreducible core is
  \<open>diag_acc\<close> (the diagonal seeds are accessible), the entry point for the
  sum/principal closure lemmas.  \<^bold>\<open>\<open>diag_acc\<close> is an open obligation (sorry).\<close>
\<close>

abbreviation stepR :: "(pairseq \<times> pairseq) set" where
  "stepR \<equiv> {(T, M). M \<in> ST_PS \<and> step M T}"

text \<open>Generation induction: given that the diagonal seeds are accessible, every
  standard form is accessible.  Each expansion \<open>M \<rightarrow> M[n]\<close> only moves
  \<^emph>\<open>downward\<close> in \<open>stepR\<close>, so accessibility propagates from \<open>M\<close> to \<open>M[n]\<close>
  (\<open>acc_downward\<close>) along the \<open>ST_PS\<close> generation tree.  No order, no \<open>translate\<close>.\<close>

lemma direct_acc_of_ST_PS:
  assumes diagacc: "\<And>v. diagSeq 0 v \<in> Wellfounded.acc stepR"
    and "M \<in> ST_PS"
  shows "M \<in> Wellfounded.acc stepR"
  using \<open>M \<in> ST_PS\<close>
proof (induction M rule: ST_PS.induct)
  case (diag v)
  thus ?case using diagacc by simp
next
  case (oper M n)
  show ?case
  proof (cases "1 < Lng M")
    case False
    hence "M[n] = M" by (simp add: oper_eq_self_short)
    thus ?thesis using oper.IH by simp
  next
    case True
    have st: "step M (M[n])" using True oper.hyps(2) by (rule step.step_oper)
    have "(M[n], M) \<in> stepR" using oper.hyps(1) st by simp
    thus ?thesis using acc_downward[OF oper.IH] by blast
  qed
qed

text \<open>Termination of the whole one-step relation reduces to diagonal-seed
  accessibility (forms outside \<open>ST_PS\<close> have no \<open>stepR\<close>-predecessor).\<close>

theorem PSS_terminates_direct:
  assumes diagacc: "\<And>v. diagSeq 0 v \<in> Wellfounded.acc stepR"
  shows "wf stepR"
proof -
  have "x \<in> Wellfounded.acc stepR" for x
  proof (cases "x \<in> ST_PS")
    case True
    thus ?thesis using direct_acc_of_ST_PS[OF diagacc] by simp
  next
    case False
    show ?thesis
    proof (rule acc.accI)
      fix y assume "(y, x) \<in> stepR"
      hence "x \<in> ST_PS" by simp
      with False show "y \<in> Wellfounded.acc stepR" by simp
    qed
  qed
  thus "wf stepR" by (simp add: wf_iff_acc)
qed

text \<open>Base case: a form too short to expand has no \<open>stepR\<close>-successor, hence is
  trivially accessible.\<close>

lemma acc_short: "Lng M \<le> 1 \<Longrightarrow> M \<in> Wellfounded.acc stepR"
proof (rule acc.accI)
  fix y assume "(y, M) \<in> stepR"
  hence "step M y" by simp
  then have "1 < Lng M" by (cases rule: step.cases) auto
  moreover assume "Lng M \<le> 1"
  ultimately show "y \<in> Wellfounded.acc stepR" by simp
qed

text \<open>Level (max row-1) is non-increasing along a step: the expansion never
  raises the maximal subscript.  This underlies the level induction toward
  \<open>diag_acc\<close> (re-climb / the crux lives strictly at \<open>maxsub \<ge> 2\<close>; memo 続86).\<close>

lemma step_level_noninc:
  assumes M: "M \<in> ST_PS" and st: "step M T"
  shows "maxsub (translate T) \<le> maxsub (translate M)"
proof -
  from st obtain n where L: "1 < Lng M" and n: "1 \<le> n" and TM: "T = M[n]"
    by (auto elim!: step.cases)
  have T: "T \<in> ST_PS" using M st by (rule step_in_ST_PS)
  have dec: "olt (translate T) (translate M)"
    using m_step_decreases[OF L n] TM by simp
  have vNF: "translate T \<in> NF" using T by simp
  have uNF: "translate M \<in> NF" using M by simp
  show ?thesis by (rule maxsub_mono_NF'[OF vNF uNF dec])
qed

text \<open>\<^bold>\<open>The W = T core (OPEN).\<close>  Every diagonal seed is accessible.  To be
  proved by the PSS analogue of Buchholz's sum/principal closure (Lemmas
  2.4/2.5), inducting on the block/nesting structure of the standard form
  (the bad-branch copy \<open>M[n] = G @ B\<^sup>n\<close> is killed because each block \<open>B\<close> and
  the prefix \<open>G\<close> are, and termination composes).  This replaces the discarded
  \<open>nrm_order_pres\<close>.\<close>

lemma diag_acc: "diagSeq 0 v \<in> Wellfounded.acc stepR"
  sorry

theorem PSS_terminates_wtt: "wf stepR"
  by (rule PSS_terminates_direct[OF diag_acc])

end
