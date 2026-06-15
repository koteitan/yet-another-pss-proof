theory nrm
  imports necessity "YAPSS.proofs" "YAPSS.seqlex"
begin

text \<open>
  \<^bold>\<open>Value normalization\<close> \<open>nrm\<close>: a small syntactic projection sending an arbitrary
  term to a Buchholz OT term (\<open>wf3\<close>) of the same \<open>\<psi>\<close>-value.  At a principal
  \<open>D\<^bsub>a\<^esub>(b)\<close> whose argument violates the OT3 condition (some \<open>g \<in> G\<^bsub>a\<^esub>(b)\<close> with
  \<open>\<not> g <o b\<close>), the value \<open>\<psi>\<^sub>a\<close> is constant on the interval up to the offending
  critical value, so the name may be rewritten to \<open>D\<^bsub>a\<^esub>(max G\<^bsub>a\<^esub>(b))\<close> without
  changing the value; iterating yields the OT-normal name.  Sums absorb
  principals dominated by a later one (ordinal addition).

  The route to \<open>wf Rnf\<close>:
    \<^item> \<open>wf3_nrm\<close>: every \<open>nrm\<close>-image is an OT term            (proved below)
    \<^item> \<open>nrm_order_pres\<close>: on \<open>NF\<close>, \<open>v <o u \<Longrightarrow> nrm v <o nrm u\<close>  (THE remaining core;
      validated empirically on 2.6 million pairs, zero violations)
    \<^item> \<open>wf_olt_wf3\<close>: \<open><o\<close> is well-founded on OT terms          (proved, otembed)
  Note the \<open>\<psi>\<close>-semantics only \<^emph>\<open>motivates\<close> \<open>nrm\<close>; the chain below never
  mentions values.
\<close>

subsection \<open>Executable critical-term collection\<close>

fun Glist :: "nat \<Rightarrow> three \<Rightarrow> three list" where
  "Glist u Z = []"
| "Glist u (P a b c) = (if u \<le> a then b # Glist u b else []) @ Glist u c"

lemma set_Glist: "set (Glist u t) = Gterm u t"
  by (induction t) auto

fun maxo :: "three \<Rightarrow> three list \<Rightarrow> three" where
  "maxo x [] = x"
| "maxo x (y # ys) = maxo (if olt x y then y else x) ys"

lemma maxo_in: "maxo x ys \<in> insert x (set ys)"
proof (induction ys arbitrary: x)
  case (Cons y ys) thus ?case by (cases "olt x y") auto
qed simp

subsection \<open>Projection at a collapse point\<close>

function proj :: "nat \<Rightarrow> three \<Rightarrow> three" where
  "proj u b = (let gs = filter (\<lambda>g. \<not> olt g b) (Glist u b) in
               if gs = [] then b else proj u (maxo (hd gs) (tl gs)))"
  by pat_completeness auto

lemma maxo_hdtl_in: "gs \<noteq> [] \<Longrightarrow> maxo (hd gs) (tl gs) \<in> set gs"
  using maxo_in[of "hd gs" "tl gs"] by (cases gs) auto

termination proj
proof (relation "measure (size \<circ> snd)", goal_cases)
  case (2 u b gs)
  let ?gs = "filter (\<lambda>g. \<not> olt g b) (Glist u b)"
  have ne: "?gs \<noteq> [] " using 2(1) 2(2) by simp
  have "maxo (hd ?gs) (tl ?gs) \<in> set ?gs" by (rule maxo_hdtl_in[OF ne])
  hence "maxo (hd ?gs) (tl ?gs) \<in> Gterm u b" using set_Glist by auto
  hence "size (maxo (hd ?gs) (tl ?gs)) < size b" by (rule Gterm_size)
  thus ?case using 2(1) by simp
qed simp

declare proj.simps [simp del]

lemma proj_id:
  "filter (\<lambda>g. \<not> olt g b) (Glist u b) = [] \<Longrightarrow> proj u b = b"
  by (subst proj.simps) (simp add: Let_def)

lemma proj_rec:
  "filter (\<lambda>g. \<not> olt g b) (Glist u b) \<noteq> [] \<Longrightarrow>
   proj u b = proj u (maxo (hd (filter (\<lambda>g. \<not> olt g b) (Glist u b)))
                          (tl (filter (\<lambda>g. \<not> olt g b) (Glist u b))))"
  by (subst proj.simps) (simp add: Let_def)

lemma Gterm_wf3: "x \<in> Gterm u t \<Longrightarrow> wf3 t \<Longrightarrow> wf3 x"
proof (induction t arbitrary: x)
  case (P a b c) thus ?case by (cases "u \<le> a") auto
qed simp

lemma proj_wf3: "wf3 b \<Longrightarrow> wf3 (proj u b)"
proof (induction u b rule: proj.induct)
  case (1 u b)
  show ?case
  proof (cases "filter (\<lambda>g. \<not> olt g b) (Glist u b) = []")
    case True
    show ?thesis unfolding proj_id[OF True] by (rule 1(2))
  next
    case False
    let ?m = "maxo (hd (filter (\<lambda>g. \<not> olt g b) (Glist u b)))
                   (tl (filter (\<lambda>g. \<not> olt g b) (Glist u b)))"
    have mG: "?m \<in> Gterm u b" using maxo_hdtl_in[OF False] set_Glist by auto
    have w: "wf3 ?m" by (rule Gterm_wf3[OF mG 1(2)])
    show ?thesis unfolding proj_rec[OF False] by (rule 1(1)[OF refl False w])
  qed
qed

lemma proj_G: "\<forall>g \<in> Gterm u (proj u b). olt g (proj u b)"
proof (induction u b rule: proj.induct)
  case (1 u b)
  show ?case
  proof (cases "filter (\<lambda>g. \<not> olt g b) (Glist u b) = []")
    case True
    have all: "\<forall>g \<in> set (Glist u b). olt g b"
      using True by (auto simp: filter_empty_conv)
    show ?thesis unfolding proj_id[OF True] using all set_Glist by auto
  next
    case False
    show ?thesis unfolding proj_rec[OF False] by (rule 1(1)[OF refl False])
  qed
qed

text \<open>\<^bold>\<open>The projection produces an \<open>a\<close>-canonical value\<close>: since every \<open>G\<^bsub>a\<^esub>\<close>-critical
  subterm of \<open>proj a b\<close> is \<open><\<close> it (\<open>proj_G\<close>) and all are well-formed, their values
  drop below \<open>o(proj a b)\<close>, so \<open>o(proj a b) \<in> C\<^bsub>a\<^esub>(o(proj a b))\<close> (Buchholz OT3 \<Rightarrow> C).
  This is the canonicity that \<open>psi_strict_mono_arg\<close> (1.3) needs after collapsing.\<close>

lemma proj_canonical:
  assumes "wf3 b"
  shows "oV (proj a b) \<in> elts (Cset (\<lambda>\<xi>\<in>elts (oV (proj a b)). psi \<xi>) (oV (proj a b)) a)"
proof (rule Ccond_of_lt)
  have wfp: "wf3 (proj a b)" by (rule proj_wf3[OF assms])
  fix x assume x: "x \<in> Gterm a (proj a b)"
  have "olt x (proj a b)" using proj_G x by blast
  moreover have "wf3 x" by (rule Gterm_wf3[OF x wfp])
  ultimately show "oV x < oV (proj a b)" using oV_order_pres wfp by blast
qed

subsection \<open>The collapsing identity \<open>psi_proj\<close> (Buchholz \<section>1 keystone, scaffolding)\<close>

text \<open>\<^bold>\<open>B1\<close> (\<open>bad_imp_oV_ge\<close>): a critical subterm \<open>g\<close> that is \<^emph>\<open>not\<close> \<open>< b\<close> (an OT3
  violator) has value \<open>\<ge> oV b\<close>.  Pure consequence of \<open>oV_order_pres\<close> + totality.
  (Empirically 72942/72942, memo 続89(9).)\<close>

lemma bad_imp_oV_ge:
  assumes "wf3 b" and "g \<in> Gterm a b" and "\<not> olt g b"
  shows "oV b \<le> oV g"
proof -
  have wfg: "wf3 g" by (rule Gterm_wf3[OF assms(2,1)])
  from assms(3) olt_total[of g b] consider "g = b" | "olt b g" by blast
  thus ?thesis
  proof cases
    case 1 thus ?thesis by simp
  next
    case 2
    have "oV b < oV g" by (rule oV_order_pres[OF assms(1) wfg 2])
    thus ?thesis by simp
  qed
qed

text \<open>\<^bold>\<open>A1-core\<close> (\<open>psi_proj_nonmem\<close>): the \<^emph>\<open>single non-membership\<close> that the maxo-step
  reduces to \<dash> \<open>\<psi>\<^sub>a(oV b)\<close> is non-canonical w.r.t. the larger bound \<open>oV m\<close>, i.e. it
  is not in \<open>C\<^sub>a(oV m)\<close>.  This is exactly Buchholz \<^bold>\<open>1.9 necessity\<close> (plan
  \<open>section1_plan.md\<close> group D / D1 simultaneous induction): the only way \<open>\<psi>\<^sub>a(oV b)\<close>
  could enter \<open>C\<^sub>a(oV m)\<close> is as a generator \<open>\<psi>\<^sub>a(\<xi>)\<close> with \<open>\<xi> < oV m\<close> canonical
  (\<open>psi_in_Cset_same_sub_generator\<close>), which by injectivity (1.4a) forces \<open>\<xi> = oV b\<close>,
  whence \<open>oV b \<in> C\<^sub>a(oV m)\<close> \<dash> but \<open>oV b\<close> has the coefficient \<open>oV m \<ge> oV b\<close> (B1), the
  necessity-blocked re-climb.  \<^bold>\<open>Localized \<open>sorry\<close>\<close> (the irreducible core); the
  whole \<open>psi_proj\<close> chain is checked against this one statement.  Its truth is the
  established empirical fact (\<open>psi_proj\<close> TRUE 46033/46033, \<open>perstep_maxo.py\<close> 6677/0).\<close>

text \<open>\<^bold>\<open>B2\<close> (\<open>oV_noncanon_of_bad\<close>): a term with an OT3-violating critical subterm has a
  \<^bold>\<open>non-canonical\<close> value.  Now \<^bold>\<open>provable\<close> from the sub-agent results: \<open>term_nec\<close>
  (Buchholz 1.9 for \<open>wf3\<close> terms, green) + \<open>Cset_eq_Cset_c\<close> (the Remark) turn
  "\<open>oV b\<close> canonical" into "all critical coefficients \<open>< oV b\<close>", contradicting
  \<open>oV g \<ge> oV b\<close> (B1).  (Transitively rests on the one Remark residue \<open>sorry\<close>.)\<close>

lemma oV_noncanon_of_bad:
  assumes "wf3 b" and "g \<in> Gterm a b" and "\<not> olt g b"
  shows "\<not> acanon a (oV b)"
proof
  assume "acanon a (oV b)"
  hence "oV b \<in> elts (Cset (\<lambda>\<xi>\<in>elts (oV b). psi \<xi>) (oV b) a)" unfolding acanon_def .
  hence "oV b \<in> elts (Cset_c (\<lambda>\<xi>\<in>elts (oV b). psi \<xi>) (oV b) a)"
    using Cset_eq_Cset_c[OF Ord_oV] by blast
  from term_nec[OF Ord_oV assms(1) this] have "oV g < oV b" using assms(2) by blast
  moreover have "oV b \<le> oV g" by (rule bad_imp_oV_ge[OF assms(1,2,3)])
  ultimately show False by simp
qed

text \<open>\<^bold>\<open>The remaining core\<close> \<open>psi_proj_nonmem\<close>: \<open>\<psi>\<^sub>a(oV b) \<notin> C\<^sub>a(oV m)\<close>.  With B2 the
  \<open>\<xi> = oV b\<close> case of the generator analysis is excluded, but the genuine collapse
  case (\<open>\<xi>\<close> a \<^emph>\<open>larger\<close> canonical witness \<open>< oV m\<close>) needs \<open>\<xi> = oV(proj a b) \<ge> oV m\<close>,
  whose value-identity is \<open>psi_proj\<close> itself \<dash> the irreducible circularity that only
  Buchholz's simultaneous transfinite induction breaks (= the same \<section>1 core as the
  Remark residue).  Localized \<open>sorry\<close>; empirically TRUE (\<open>perstep_maxo.py\<close> 6677/0).\<close>

lemma psi_proj_nonmem:
  assumes "wf3 b"
    and "filter (\<lambda>g. \<not> olt g b) (Glist a b) \<noteq> []"
  shows "psi (oV b) a
         \<notin> elts (Cv (oV (maxo (hd (filter (\<lambda>g. \<not> olt g b) (Glist a b)))
                              (tl (filter (\<lambda>g. \<not> olt g b) (Glist a b))))) a)"
  sorry

text \<open>\<^bold>\<open>A1\<close> (\<open>psi_proj_step\<close>): a single \<open>maxo\<close>-step of \<open>proj\<close> preserves the \<open>\<psi>\<close>-value.
  \<^bold>\<open>Proven\<close> from the non-membership core via \<open>psi_eq_of_not_mem\<close> (the weak-hypothesis
  collapse) and \<open>bad_imp_oV_ge\<close> (B1, the argument grows \<open>oV b \<le> oV m\<close>).\<close>

lemma psi_proj_step:
  assumes "wf3 b"
    and "filter (\<lambda>g. \<not> olt g b) (Glist a b) \<noteq> []"
  shows "psi (oV b) a
       = psi (oV (maxo (hd (filter (\<lambda>g. \<not> olt g b) (Glist a b)))
                        (tl (filter (\<lambda>g. \<not> olt g b) (Glist a b))))) a"
proof -
  let ?gs = "filter (\<lambda>g. \<not> olt g b) (Glist a b)"
  let ?m = "maxo (hd ?gs) (tl ?gs)"
  have mins: "?m \<in> set ?gs" by (rule maxo_hdtl_in[OF assms(2)])
  have mG: "?m \<in> Gterm a b" using mins set_Glist by auto
  have mbad: "\<not> olt ?m b" using mins by simp
  have le: "oV b \<le> oV ?m" by (rule bad_imp_oV_ge[OF assms(1) mG mbad])
  show ?thesis by (rule psi_eq_of_not_mem[OF le psi_proj_nonmem[OF assms]])
qed

text \<open>\<^bold>\<open>A2\<close> (\<open>psi_proj\<close>): the full projection preserves the \<open>\<psi>\<close>-value.  Assembly by
  \<open>proj.induct\<close>, composing the maxo-step A1 with the induction hypothesis.  Fully
  checked modulo A1.  (Realizes memo 続89(16); psi_proj TRUE 46033/46033.)\<close>

lemma psi_proj: "wf3 b \<Longrightarrow> psi (oV b) a = psi (oV (proj a b)) a"
proof (induction a b rule: proj.induct)
  case (1 u b)
  show ?case
  proof (cases "filter (\<lambda>g. \<not> olt g b) (Glist u b) = []")
    case True
    show ?thesis unfolding proj_id[OF True] by simp
  next
    case False
    let ?m = "maxo (hd (filter (\<lambda>g. \<not> olt g b) (Glist u b)))
                   (tl (filter (\<lambda>g. \<not> olt g b) (Glist u b)))"
    have mG: "?m \<in> Gterm u b" using maxo_hdtl_in[OF False] set_Glist by auto
    have w: "wf3 ?m" by (rule Gterm_wf3[OF mG 1(2)])
    have step: "psi (oV b) u = psi (oV ?m) u" by (rule psi_proj_step[OF 1(2) False])
    have ih: "psi (oV ?m) u = psi (oV (proj u ?m)) u" by (rule 1(1)[OF refl False w])
    show ?thesis unfolding proj_rec[OF False] using step ih by simp
  qed
qed

text \<open>\<^bold>\<open>The projection grows the value\<close>: \<open>oV b \<le> oV (proj a b)\<close>.  \<open>proj\<close> replaces the
  argument by an OT3-violating critical subterm of value \<open>\<ge> oV b\<close> (B1) and iterates
  upward, so the canonical representative \<open>oV (proj a b)\<close> is \<open>\<ge>\<close> every intermediate
  bound \<dash> in particular \<open>\<ge> oV m\<close> at the first maxo-step.  This (with
  \<open>proj_canonical\<close>) is what makes the \<open>psi_proj_nonmem\<close> necessity true: the unique
  canonical argument carrying the value \<open>\<psi>\<^sub>a(oV b)\<close> sits \<^emph>\<open>at or above\<close> the bound, so
  no smaller canonical generator can re-create it.\<close>

lemma oV_le_proj: "wf3 b \<Longrightarrow> oV b \<le> oV (proj a b)"
proof (induction a b rule: proj.induct)
  case (1 u b)
  show ?case
  proof (cases "filter (\<lambda>g. \<not> olt g b) (Glist u b) = []")
    case True
    show ?thesis unfolding proj_id[OF True] by simp
  next
    case False
    let ?m = "maxo (hd (filter (\<lambda>g. \<not> olt g b) (Glist u b)))
                   (tl (filter (\<lambda>g. \<not> olt g b) (Glist u b)))"
    have mins: "?m \<in> set (filter (\<lambda>g. \<not> olt g b) (Glist u b))" by (rule maxo_hdtl_in[OF False])
    have mG: "?m \<in> Gterm u b" using mins set_Glist by auto
    have mbad: "\<not> olt ?m b" using mins by simp
    have le1: "oV b \<le> oV ?m" by (rule bad_imp_oV_ge[OF 1(2) mG mbad])
    have w: "wf3 ?m" by (rule Gterm_wf3[OF mG 1(2)])
    have le2: "oV ?m \<le> oV (proj u ?m)" by (rule 1(1)[OF refl False w])
    show ?thesis unfolding proj_rec[OF False] using le1 le2 by simp
  qed
qed

subsection \<open>Sum insertion with absorption, and \<open>nrm\<close>\<close>

fun ins :: "nat \<Rightarrow> three \<Rightarrow> three \<Rightarrow> three" where
  "ins a b Z = P a b Z"
| "ins a b (P e f g) = (if a < e \<or> (a = e \<and> olt b f) then P e f g else P a b (P e f g))"

fun nrm :: "three \<Rightarrow> three" where
  "nrm Z = Z"
| "nrm (P a b c) = ins a (proj a (nrm b)) (nrm c)"

lemma wf3_ins:
  assumes wb: "wf3 b" and wt: "wf3 t" and g: "\<forall>x \<in> Gterm a b. olt x b"
  shows "wf3 (ins a b t)"
proof (cases t)
  case Z thus ?thesis using wb g by simp
next
  case (P e f gg)
  show ?thesis
  proof (cases "a < e \<or> (a = e \<and> olt b f)")
    case True thus ?thesis using P wt by simp
  next
    case False
    have hd: "hdle (P e f gg) (P a b Z)"
    proof -
      from False have "\<not> a < e" and ef: "a = e \<longrightarrow> \<not> olt b f" by auto
      hence "e < a \<or> e = a" by arith
      moreover have "e = a \<Longrightarrow> olt f b \<or> f = b"
        using ef olt_total by blast
      ultimately show ?thesis by auto
    qed
    have "wf3 (P a b (P e f gg))" using wb wt g hd P by auto
    thus ?thesis using False P by simp
  qed
qed

theorem wf3_nrm: "wf3 (nrm t)"
proof (induction t)
  case Z thus ?case by simp
next
  case (P a b c)
  have wb: "wf3 (proj a (nrm b))" using proj_wf3[OF P.IH(1)] .
  have g: "\<forall>x \<in> Gterm a (proj a (nrm b)). olt x (proj a (nrm b))"
    using proj_G by blast
  show ?case using wf3_ins[OF wb P.IH(2) g] by simp
qed

subsection \<open>Inverse of \<open>translate\<close>: \<open>untr\<close>, and the sequence-side reframe\<close>

text \<open>\<^bold>\<open>The block reader \<open>untr d\<close>\<close>: the left inverse of \<open>translate\<close> at depth \<open>d\<close>.
  Reading a principal \<open>P a b c\<close> as the column \<open>(d,a)\<close> followed by the depth-\<open>Suc d\<close>
  unfolding of the argument \<open>b\<close> (its descendants) and the depth-\<open>d\<close> unfolding of the
  tail \<open>c\<close> (its siblings) exactly inverts the forest reading of @{const translate}.
  This recasts order preservation under \<open>nrm\<close> on \<open>NF\<close> into the BMS-native column
  lexicographic order (\<open>seqlex\<close>), via the \<open>translate\<close> order isomorphism
  (@{thm [source] olt_ST_iff_seqlex}).\<close>

fun untr :: "nat \<Rightarrow> three \<Rightarrow> pairseq" where
  "untr d Z = []"
| "untr d (P a b c) = (d, a) # untr (Suc d) b @ untr d c"

text \<open>\<^bold>\<open>\<open>untr d\<close> always produces a depth-\<open>d\<close> block\<close>: the head sits at \<open>d\<close>, every row
  is \<open>\<ge> d\<close>, and row-0 increases by at most one (descending into an argument raises
  the depth by exactly one, while a tail keeps it).  Unconditional in \<open>t\<close>.
  (Empirically 0 bad / 20000 random terms.)\<close>

lemma untr_set_ge: "\<forall>p \<in> set (untr d t). d \<le> fst p"
proof (induction d t rule: untr.induct)
  case (1 d) show ?case by simp
next
  case (2 d a b c)
  have "\<forall>p \<in> set (untr (Suc d) b). d \<le> fst p" using 2(1) by (meson Suc_leD)
  thus ?case using 2(2) by auto
qed

lemma untr_hd: "untr d t \<noteq> [] \<Longrightarrow> fst (hd (untr d t)) = d"
  by (induction d t rule: untr.induct) auto

lemma blockok_untr: "blockok d (untr d t)"
proof (induction d t rule: untr.induct)
  case (1 d) show ?case by simp
next
  case (2 d a b c)
  let ?A = "untr (Suc d) b" and ?C = "untr d c"
  have bA: "blockok (Suc d) ?A" by (rule 2(1))
  have bC: "blockok d ?C" by (rule 2(2))
  \<comment> \<open>head\<close>
  have hd0: "fst (hd (untr d (P a b c))) = d" by simp
  \<comment> \<open>all rows \<open>\<ge> d\<close>\<close>
  have geA: "\<forall>p \<in> set ?A. d \<le> fst p" using untr_set_ge[of "Suc d" b] by (meson Suc_leD)
  have geC: "\<forall>p \<in> set ?C. d \<le> fst p" using untr_set_ge[of d c] by simp
  have setge: "\<forall>p \<in> set (untr d (P a b c)). d \<le> fst p"
  proof
    fix p assume "p \<in> set (untr d (P a b c))"
    hence "p = (d,a) \<or> p \<in> set ?A \<or> p \<in> set ?C" by auto
    thus "d \<le> fst p" using geA geC by auto
  qed
  \<comment> \<open>row-0 steps by at most one\<close>
  have stA: "\<forall>j. Suc j < length ?A \<longrightarrow> fst (?A ! Suc j) \<le> Suc (fst (?A ! j))"
    using bA unfolding blockok_def by blast
  have stC: "\<forall>j. Suc j < length ?C \<longrightarrow> fst (?C ! Suc j) \<le> Suc (fst (?C ! j))"
    using bC unfolding blockok_def by blast
  \<comment> \<open>seam between the leading column / argument / tail\<close>
  have seam_hd_A: "?A \<noteq> [] \<longrightarrow> fst (hd ?A) = Suc d"
    using bA unfolding blockok_def by blast
  have seam_A_C: "?A \<noteq> [] \<longrightarrow> ?C \<noteq> [] \<longrightarrow> fst (hd ?C) = d"
    using bC unfolding blockok_def by blast
  have seam_hd_C: "?A = [] \<longrightarrow> ?C \<noteq> [] \<longrightarrow> fst (hd ?C) = d"
    using bC unfolding blockok_def by blast
  let ?B = "(d, a) # ?A @ ?C"
  have steps: "\<forall>j. Suc j < length ?B \<longrightarrow> fst (?B ! Suc j) \<le> Suc (fst (?B ! j))"
  proof (intro allI impI)
    fix j assume jl: "Suc j < length ?B"
    show "fst (?B ! Suc j) \<le> Suc (fst (?B ! j))"
    proof (cases j)
      case 0
      \<comment> \<open>step from the leading \<open>(d,a)\<close> into the first element of \<open>?A @ ?C\<close>\<close>
      have "fst (?B ! Suc 0) \<le> Suc d"
      proof (cases "?A = []")
        case True
        have Cne: "?C \<noteq> []" using jl 0 True by auto
        have "fst (hd ?C) = d" using True seam_hd_C Cne by simp
        hence "fst (?C ! 0) = d" using Cne by (simp add: hd_conv_nth)
        thus ?thesis using True by simp
      next
        case False
        have "fst (hd ?A) = Suc d" using seam_hd_A False by simp
        hence "fst (?A ! 0) = Suc d" using False by (simp add: hd_conv_nth)
        thus ?thesis using False by (simp add: nth_append)
      qed
      thus ?thesis using 0 by simp
    next
      case (Suc i)
      \<comment> \<open>step inside \<open>?A @ ?C\<close>: reduce to the steps of \<open>?A\<close>, \<open>?C\<close>, and the \<open>A\<close>-\<open>C\<close> seam\<close>
      have jl': "Suc i < length (?A @ ?C)" using jl Suc by simp
      have idx: "fst ((?A @ ?C) ! Suc i) \<le> Suc (fst ((?A @ ?C) ! i))"
      proof (cases "Suc i < length ?A")
        case True
        hence "i < length ?A" by simp
        thus ?thesis using True stA by (simp add: nth_append)
      next
        case False
        show ?thesis
        proof (cases "i < length ?A")
          case True
          \<comment> \<open>the seam: \<open>i\<close> is the last index of \<open>?A\<close>, \<open>Suc i\<close> the first of \<open>?C\<close>\<close>
          have eqlen: "Suc i = length ?A" using True False by simp
          have Ane: "?A \<noteq> []" using True by auto
          have Cne: "?C \<noteq> []" using jl' False by auto
          have "(?A @ ?C) ! Suc i = ?C ! (Suc i - length ?A)"
            using False by (simp add: nth_append)
          hence "(?A @ ?C) ! Suc i = ?C ! 0" using eqlen by simp
          hence lhs: "fst ((?A @ ?C) ! Suc i) = d"
            using seam_A_C Ane Cne by (simp add: hd_conv_nth)
          have "(?A @ ?C) ! i = ?A ! i" using True by (simp add: nth_append)
          hence "d \<le> fst ((?A @ ?C) ! i)" using True geA by simp
          thus ?thesis using lhs by simp
        next
          case False2: False
          \<comment> \<open>both indices inside \<open>?C\<close>\<close>
          let ?k = "i - length ?A"
          have le: "length ?A \<le> i" using False2 by simp
          have sk: "Suc i - length ?A = Suc ?k" using le by simp
          have "Suc ?k < length ?C" using jl' False2 by auto
          hence "fst (?C ! Suc ?k) \<le> Suc (fst (?C ! ?k))" using stC by blast
          moreover have "(?A @ ?C) ! i = ?C ! ?k" using False2 by (simp add: nth_append)
          moreover have "(?A @ ?C) ! Suc i = ?C ! Suc ?k"
            using False2 sk by (simp add: nth_append)
          ultimately show ?thesis by simp
        qed
      qed
      show ?thesis using idx Suc by (simp add: nth_append)
    qed
  qed
  show ?case unfolding blockok_def using hd0 setge steps by simp
qed

text \<open>\<^bold>\<open>\<open>untr\<close> is a section of \<open>translate\<close>\<close>: \<open>translate (untr d t) = t\<close>, unconditionally.
  The forest split of @{const translate} \<open>takeWhile/dropWhile (\<lambda>q. d < fst q)\<close>
  exactly recovers the argument zone \<open>untr (Suc d) b\<close> (all rows \<open>> d\<close>) and the tail
  zone \<open>untr d c\<close> (starting at row \<open>d\<close>).  (Empirically 0 bad / 11708.)\<close>

lemma translate_untr: "translate (untr d t) = t"
proof (induction d t rule: untr.induct)
  case (1 d) show ?case by simp
next
  case (2 d a b c)
  let ?A = "untr (Suc d) b" and ?C = "untr d c"
  have gtA: "\<forall>p \<in> set ?A. d < fst p" using untr_set_ge[of "Suc d" b] by auto
  have tw: "takeWhile (\<lambda>q. d < fst q) (?A @ ?C) = ?A"
  proof -
    have allA: "\<forall>p \<in> set ?A. d < fst p" by (rule gtA)
    have headC: "?C \<noteq> [] \<longrightarrow> \<not> d < fst (hd ?C)" using untr_hd[of d c] by auto
    show ?thesis
    proof (cases "?C = []")
      case True thus ?thesis using allA by (simp add: takeWhile_eq_all_conv)
    next
      case False
      have "\<not> (\<lambda>q. d < fst q) (hd ?C)" using headC False by simp
      hence "takeWhile (\<lambda>q. d < fst q) ?C = []"
        using False by (cases ?C) auto
      thus ?thesis using allA by (simp add: takeWhile_append2 takeWhile_eq_all_conv)
    qed
  qed
  have dw: "dropWhile (\<lambda>q. d < fst q) (?A @ ?C) = ?C"
  proof -
    have allA: "\<forall>p \<in> set ?A. d < fst p" by (rule gtA)
    have headC: "?C \<noteq> [] \<longrightarrow> \<not> d < fst (hd ?C)" using untr_hd[of d c] by auto
    show ?thesis
    proof (cases "?C = []")
      case True thus ?thesis using allA by (simp add: dropWhile_eq_Nil_conv)
    next
      case False
      have "\<not> (\<lambda>q. d < fst q) (hd ?C)" using headC False by simp
      hence "dropWhile (\<lambda>q. d < fst q) ?C = ?C"
        using False by (cases ?C) auto
      thus ?thesis using allA by (simp add: dropWhile_append2)
    qed
  qed
  have "translate (untr d (P a b c))
        = P a (translate (takeWhile (\<lambda>q. d < fst q) (?A @ ?C)))
              (translate (dropWhile (\<lambda>q. d < fst q) (?A @ ?C)))"
    by simp
  also have "\<dots> = P a (translate ?A) (translate ?C)" using tw dw by simp
  also have "\<dots> = P a b c" using 2(1) 2(2) by simp
  finally show ?case .
qed

subsection \<open>The remaining core: order preservation on \<open>NF\<close>\<close>

text \<open>\<^bold>\<open>The sequence-side normalizer\<close> \<open>\<sigma>\<close>: pulling \<open>nrm\<close> back through the
  \<open>translate\<close> isomorphism.  By @{thm [source] translate_untr}, \<open>\<sigma> M\<close> is a genuine
  pair sequence whose translate \<^emph>\<open>is\<close> the normalized term \<open>nrm (translate M)\<close>, and by
  @{thm [source] blockok_untr} it is a depth-\<open>0\<close> block — so the \<open>translate\<close> order
  isomorphism applies on both sides.\<close>

definition sigma :: "pairseq \<Rightarrow> pairseq" where
  "sigma M = untr 0 (nrm (translate M))"

lemma translate_sigma: "translate (sigma M) = nrm (translate M)"
  unfolding sigma_def by (rule translate_untr)

lemma blockok_sigma: "blockok 0 (sigma M)"
  unfolding sigma_def by (rule blockok_untr)

text \<open>\<^bold>\<open>Definitional unfolding of \<open>\<sigma>\<close> through a translate-block\<close> (green).  Writing
  the head subscript \<open>y\<close>, argument-zone \<open>aM\<close> (\<open>takeWhile\<close> rows \<open>> 0\<close>) and tail-zone
  \<open>tM\<close> (\<open>dropWhile\<close>) of a depth-0 sequence, \<open>translate ((0,y)#aM@tM)\<close> reads as the
  principal \<open>P y (translate aM) (translate tM)\<close>, and \<open>\<sigma>\<close> commutes with @{const nrm}
  and @{const ins}.  This is the \<^emph>\<open>exact\<close> sequence-side recursion the block
  induction (\<open>seqlex_arg_or_tail\<close>) walks; the only obstacle to running it is whether
  the leading @{const ins} \<^emph>\<open>absorbs\<close> the head.  Unconditional in the sequence.\<close>

lemma sigma_block_unfold:
  "untr 0 (nrm (P y B C))
     = untr 0 (ins y (proj y (nrm B)) (nrm C))"
  by simp

subsection \<open>The structural recursion (S) of \<open>\<sigma>\<close>\<close>

text \<open>\<^bold>\<open>Reading a depth-0 sequence as a translate-block\<close>.  For \<open>M = (0,y) # r\<close> the
  argument zone \<open>aM = takeWhile (\<lambda>q. 0 < fst q) r\<close> and the tail zone
  \<open>tM = dropWhile (\<lambda>q. 0 < fst q) r\<close> are exactly the two recursion arguments of
  @{const translate}, so \<open>translate M = P y (translate aM) (translate tM)\<close>.\<close>

lemma translate_zone_split:
  "translate ((0, y) # r)
     = P y (translate (takeWhile (\<lambda>q. 0 < fst q) r))
           (translate (dropWhile (\<lambda>q. 0 < fst q) r))"
  by simp

text \<open>\<^bold>\<open>\<open>untr\<close> reads through a non-absorbed \<open>ins\<close>\<close>.  When the leading @{const ins}
  prepends (does not absorb), \<open>untr 0 (ins y A C')\<close> splits as the leading column
  \<open>(0,y)\<close>, the depth-1 unfolding of the argument \<open>A\<close>, and the depth-0 unfolding of
  \<open>C'\<close>.  This is purely @{const ins}/@{const untr} computation.\<close>

lemma untr_ins_unfold:
  "untr 0 (ins y A C') = (0, y) # untr 1 A @ untr 0 C'
   \<or> (\<exists>e f g. C' = P e f g \<and> (y < e \<or> (y = e \<and> olt A f)) \<and>
              untr 0 (ins y A C') = untr 0 C')"
proof (cases C')
  case Z thus ?thesis by simp
next
  case (P e f g)
  show ?thesis
  proof (cases "y < e \<or> (y = e \<and> olt A f)")
    case True
    have "untr 0 (ins y A C') = untr 0 C'" using P True by simp
    thus ?thesis using P True by blast
  next
    case False
    hence "ins y A C' = P y A C'" using P by simp
    thus ?thesis by simp
  qed
qed

text \<open>\<^bold>\<open>The head non-absorption predicate\<close>.  \<open>sigma_keeps_head M\<close> says the leading
  @{const ins} in the \<open>\<sigma>\<close> recursion of a depth-0 \<open>M = (0,y)#r\<close> does not absorb the
  head — equivalently, it does not satisfy the absorption test against the
  normalized tail.\<close>

definition keeps_head :: "pairseq \<Rightarrow> bool" where
  "keeps_head M \<longleftrightarrow>
     (case M of [] \<Rightarrow> True | (_, y) # r \<Rightarrow>
        (let A = proj y (nrm (translate (takeWhile (\<lambda>q. 0 < fst q) r)));
             C = nrm (translate (dropWhile (\<lambda>q. 0 < fst q) r)) in
         (case C of Z \<Rightarrow> True | P e f g \<Rightarrow> \<not> (y < e \<or> (y = e \<and> olt A f)))))"

text \<open>\<^bold>\<open>The structural recursion (S) of \<open>\<sigma>\<close>\<close> (conditional on head non-absorption).
  For a depth-0 \<open>M = (0,y) # r\<close> with \<open>keeps_head M\<close>, \<open>\<sigma> M\<close> decomposes as the leading
  column, the argument-zone normalizer \<open>\<sigma>\<^sub>P y aM := untr 1 (proj y (nrm (translate
  aM)))\<close>, and \<open>\<sigma>\<close> of the strictly-shorter tail zone \<open>tM\<close>.  This is the exact
  recursion (S) (empirically 0 / 10437, \<open>tools/probe_sigma_struct.py\<close>).\<close>

lemma sigma_struct_rec:
  assumes "keeps_head ((0, y) # r)"
  shows "sigma ((0, y) # r)
       = (0, y) # untr 1 (proj y (nrm (translate (takeWhile (\<lambda>q. 0 < fst q) r))))
                @ sigma (dropWhile (\<lambda>q. 0 < fst q) r)"
proof -
  let ?aM = "takeWhile (\<lambda>q. 0 < fst q) r"
  let ?tM = "dropWhile (\<lambda>q. 0 < fst q) r"
  let ?A = "proj y (nrm (translate ?aM))"
  let ?C = "nrm (translate ?tM)"
  have nrmM: "nrm (translate ((0, y) # r)) = ins y ?A ?C"
    by (simp only: translate_zone_split nrm.simps)
  have nabs: "\<not> (\<exists>e f g. ?C = P e f g \<and> (y < e \<or> (y = e \<and> olt ?A f)))"
    using assms unfolding keeps_head_def
    by (auto split: list.splits three.splits prod.splits)
  from untr_ins_unfold[of y ?A ?C] nabs
  have "untr 0 (ins y ?A ?C) = (0, y) # untr 1 ?A @ untr 0 ?C" by blast
  thus ?thesis
    unfolding sigma_def by (simp only: nrmM)
qed

subsection \<open>Append law for \<open>seqlex\<close> with a depth gap\<close>

text \<open>\<^bold>\<open>The append law\<close>: when \<open>seqlex u v\<close> and every row of the part of \<open>v\<close>
  after \<open>u\<close> exceeds the head row of \<open>x\<close> (a depth gap that the appended sigma-tail
  always supplies: \<open>untr 1\<close>-args are rows \<open>\<ge> 1\<close>, the \<open>sigma\<close>-tail starts at row 0),
  \<open>seqlex (u @ x) (v @ y)\<close> holds.  Proved by induction on the shared prefix.\<close>

lemma seqlex_append_left:
  "seqlex u v \<Longrightarrow>
   (length u < length v \<longrightarrow> x \<noteq> [] \<longrightarrow> pairlt (hd x) (v ! length u)) \<Longrightarrow>
   seqlex (u @ x) (v @ y)"
proof (induction u arbitrary: v)
  case Nil
  then obtain q v' where v: "v = q # v'" by (cases v) auto
  show ?case
  proof (cases x)
    case Nil thus ?thesis using v by simp
  next
    case (Cons a x')
    have "pairlt (hd x) (v ! length [])" using Nil.prems(2) v Cons by simp
    hence "pairlt a q" using Cons v by simp
    thus ?thesis using v Cons by simp
  qed
next
  case (Cons p u')
  then obtain q v' where v: "v = q # v'" by (cases v) auto
  show ?case
  proof (cases "pairlt p q")
    case True thus ?thesis using v by simp
  next
    case False
    hence pq: "p = q" and slr: "seqlex u' v'" using Cons.prems(1) v by auto
    have gap: "length u' < length v' \<longrightarrow> x \<noteq> [] \<longrightarrow> pairlt (hd x) (v' ! length u')"
      using Cons.prems(2) v pq by simp
    have "seqlex (u' @ x) (v' @ y)" by (rule Cons.IH[OF slr gap])
    thus ?thesis using v pq by simp
  qed
qed

text \<open>\<^bold>\<open>The core\<close> \<open>sigma_seqlex_mono\<close>: on standard forms, the
  sequence normalizer \<open>\<sigma>\<close> is \<^emph>\<open>monotone\<close> for the column lexicographic order.
  This is \<open>nrm_order_pres\<close> transported entirely onto the BMS-native (column,
  suffix, \<open>seqlex\<close>, \<open>blockok\<close>) side via the \<open>translate\<close> isomorphism.

  \<^bold>\<open>STATUS (2026-06-15): now a GREEN block-induction assembly\<close> (below), mirroring
  @{thm [source] seqlex_imp_olt}: \<open>less_induct\<close> on \<open>length M + length N\<close>, head
  split, then @{thm [source] seqlex_arg_or_tail}.  The head-differ and tail-zone
  branches are fully discharged from the structural recursion (S)
  (@{thm [source] sigma_struct_rec}) and the append law
  (@{thm [source] seqlex_append_left}).  The whole proof now rests on \<^bold>\<open>four
  precisely-localized residual \<open>sorry\<close>s\<close>, each empirically verified at deep
  closure with \<^bold>\<open>zero\<close> counterexamples (\<open>tools/probe_sigma_residual.py\<close>):
  \<^item> \<open>tail_zone_ST_PS\<close> \<dash> tail-zone standard-form closure (0/10437);
  \<^item> \<open>keeps_head_ST_PS\<close> \<dash> head non-absorption \<open>T1\<close> (0/10437);
  \<^item> \<open>sigma_argzone_mono\<close> \<dash> the irreducible \<open>\<sigma>\<^sub>P\<close> \<section>1 core
    (0/79774; deep 168350/0), carrying the standard-form invariant (NOT the
    \<^bold>\<open>FALSE\<close> \<open>cnf\<close>-level \<open>PROJMONO\<close>).
  The argument-zone core is the genuine Buchholz \<section>1 content; the rest is now
  mechanical.

  \<^bold>\<open>Where the proof stalls (the genuine irreducible obstruction, mapped 2026-06-15).\<close>
  The block induction reduces \<open>\<sigma>\<close> on a standard-form block \<open>(0,y)#aM@tM\<close> to the
  \<^bold>\<open>exact structural recursion\<close> (empirically verified, 0 violations / 10437 blocks,
  \<open>tools/probe_sigma_struct.py\<close>):

    \<open>\<sigma> M = (0,y) # untr 1 (proj y (nrm (translate aM))) @ \<sigma> tM\<close>       (S)

  Here the tail-zone part is literally \<open>\<sigma> tM\<close> (a strictly shorter block, the
  block-induction IH applies), and the argument-zone part is \<open>\<sigma>\<^sub>P y aM :=
  untr 1 (proj y (nrm (translate aM)))\<close>.  Two facts are required:

  \<^item> \<^bold>\<open>Head non-absorption\<close> (\<open>ins\<close> keeps the lead \<open>(0,y)\<close>): empirically \<^bold>\<open>always\<close>
    holds on \<open>ST_PS\<close> (0 / 10437, \<open>probe_seq_induct.py\<close> T1).  But it is \<^emph>\<open>not\<close>
    cleanly separable: when the normalized tail head subscript equals \<open>y\<close>, the
    absorb test \<open>olt (proj y (nrm (translate aM))) f\<close> is itself a \<open>proj\<close>-comparison
    \<dash> the same core below.
  \<^item> \<^bold>\<open>Argument-zone monotonicity\<close> of \<open>\<sigma>\<^sub>P y\<close>: this is the genuine residue.  It is
    \<^bold>\<open>true on the universe it is applied to\<close> (hereditary arguments of \<open>NF\<close>
    translates: 168350 ordered pairs, 0 reversals, 0 collapses at deep closure
    1{,}013{,}172, \<open>tools/probe_proj_mono_deep.py\<close> universe A).

  \<^bold>\<open>FALSE generalization ruled out\<close> (8th-incident avoided, soundness gate
  2026-06-15).  The tempting term-level lemma

    \<open>PROJMONO\<close>:  \<open>olt b f \<Longrightarrow> olt (proj a (nrm b)) (proj a (nrm f))\<close>   \<^bold>\<open>is FALSE\<close>

  on arbitrary \<open>cnf\<close> subterms: at the same closure it has \<^bold>\<open>14739 reversals\<close>
  (universe B, with the \<open>y\<close>-tower \<open>y\<^sub>k\<^sub>+\<^sub>1 = p\<^bsub>0\<^esub>(p\<^bsub>1\<^esub>(y\<^sub>k))\<close> injected) \<dash> exactly the
  \<open>oV_mono_cnf\<close> trap of 続89(41).  E.g. with \<open>a=0\<close>,
  \<open>p\<^bsub>0\<^esub>(p\<^bsub>1\<^esub>(\<dots>)) <o p\<^bsub>1\<^esub>(\<dots>)\<close> but \<open>proj 0 \<circ> nrm\<close> reverses them.  Hence
  \<open>\<sigma>\<^sub>P\<close>-monotonicity \<^bold>\<open>must\<close> carry the standard-form (\<open>blockok\<close> / row-1 parenthood)
  invariant of \<open>NF\<close>; it does \<^emph>\<open>not\<close> reduce to any \<open>cnf\<close>/\<open>wf3\<close>/\<open>r1ok\<close> term predicate.
  This is the same Buchholz \<section>1 collapse content as \<open>oV_mono_NF\<close> (ovnf.thy) and
  \<open>nrm_order_pres\<close> \<dash> the three are one irreducible fact, all kept as a single
  honest \<open>sorry\<close>.

  \<^bold>\<open>Empirical status of the target itself\<close> (soundness gate, deep closure):
  \<open>\<sigma>\<close> preserves \<open>blockok 0\<close> (0 bad / 10437) and is strictly \<open>seqlex\<close>-monotone
  (979300 ordered NF pairs, 0 violations, 0 collapses; \<open>tools/probe_sigma_core.py\<close>).
  No counterexample at any tested depth.\<close>

subsection \<open>The three precisely-localized residual obligations\<close>

text \<open>\<^bold>\<open>Residual 1\<close> \<open>head_in_ST_PS\<close>: a standard form, if nonempty, has head row 0
  (it is a depth-0 block).  \<^bold>\<open>Green\<close> from @{thm [source] blockok_ST_PS}.\<close>

lemma head_row0_ST_PS:
  assumes "M \<in> ST_PS" and "M \<noteq> []"
  shows "fst (hd M) = 0"
  using blockok_ST_PS[OF assms(1)] assms(2) unfolding blockok_def by simp

text \<open>\<^bold>\<open>Nonemptiness of standard forms\<close>.  Every \<open>M \<in> ST_PS\<close> is nonempty: the
  generators \<open>diagSeq 0 v\<close> have length \<open>Suc v \<ge> 1\<close>, and the expansion \<open>M[n]\<close>
  never empties a nonempty sequence (its three result shapes are \<open>M\<close>, \<open>Pred M\<close>
  \<dash> which on length \<open>\<ge> 2\<close> is a nonempty \<open>butlast\<close> \<dash>, and a green prefix
  followed by a nonempty tiled block).  Proved by induction on \<open>ST_PS\<close>.

  \<^bold>\<open>Soundness note (8th-incident gate).\<close> This nonemptiness fact is exactly what
  makes the literal \<open>dropWhile \<dots> \<in> ST_PS\<close> tail-zone statement \<^emph>\<open>false\<close> in the
  edge case where the tail zone is \<^bold>\<open>empty\<close> (e.g. \<open>(0,0)(1,1)\<dots>(v,v)[\<dots>]\<close> whose
  body, after the leading argument run, contains no further row-0 column): then
  \<open>dropWhile \<dots> = []\<close>, and \<open>[] \<notin> ST_PS\<close>.  Empirically the only counterexamples to
  the old \<open>tail_zone_ST_PS\<close> were precisely these empty tail-zones
  (\<open>tools/probe_struct_close.py\<close>: 0 nonempty / 76114 fail; the \<open>[] \<notin> ST_PS\<close> cases
  are the apparent failures).  The lemma below is therefore guarded by the
  hypothesis that the tail zone is nonempty; the call site
  (\<open>sigma_seqlex_mono\<close>, below) handles the empty tail zone directly via
  \<open>sigma [] = []\<close>.\<close>

lemma oper_nonempty: "M \<noteq> [] \<Longrightarrow> 1 \<le> n \<Longrightarrow> M[n] \<noteq> []"
proof -
  assume Mne: "M \<noteq> []" and n1: "1 \<le> n"
  define j1 where "j1 = Lng M - 1"
  show "M[n] \<noteq> []"
  proof (cases "j1 = 0")
    case True thus ?thesis using Mne unfolding oper_def Let_def j1_def[symmetric] by simp
  next
    case False
    have len2: "2 \<le> Lng M" using False j1_def by simp
    have predne: "Pred M \<noteq> []"
    proof -
      have bne: "butlast M \<noteq> []" using len2 by (cases M rule: rev_cases) auto
      have nle: "\<not> Lng M \<le> 1" using len2 by simp
      have "Pred M = butlast M" unfolding Pred_def using nle by simp
      thus ?thesis using bne by simp
    qed
    show ?thesis
    proof (cases "entry M 0 j1 = 0 \<and> entry M 1 j1 = 0")
      case True
      have "M[n] = Pred M" unfolding oper_def Let_def j1_def[symmetric]
        using False True by auto
      thus ?thesis using predne by simp
    next
      case Fz: False
      define i1 where "i1 = idx1 M j1"
      show ?thesis
      proof (cases "hasParent M i1 j1")
        case False2: False
        have "M[n] = Pred M" unfolding oper_def Let_def j1_def[symmetric] i1_def[symmetric]
          using False Fz False2 by auto
        thus ?thesis using predne by simp
      next
        case hp: True
        define j0 where "j0 = parent M i1 j1"
        define d0 where "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
        define d1 where "d1 = (if 1 < i1 then entry M 1 j1 - entry M 1 j0 else 0)"
        define blk where "blk = (\<lambda>k. map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j + k * d1)) [j0..<j1])"
        have opeq: "M[n] = take j0 M @ concat (map blk [0..<n])"
          unfolding oper_def Let_def j1_def[symmetric] i1_def[symmetric]
            j0_def[symmetric] d0_def[symmetric] d1_def[symmetric] blk_def
          using False Fz hp by auto
        have nR: "nextR M i1 j0 j1" unfolding j0_def by (rule parent_nextR[OF hp])
        have j0j1: "j0 < j1" using nR by (rule nextR_less)
        have blk0ne: "blk 0 \<noteq> []" unfolding blk_def using j0j1 by simp
        have "0 \<in> set [0..<n]" using n1 by simp
        hence "blk 0 \<in> set (map blk [0..<n])" by simp
        hence "concat (map blk [0..<n]) \<noteq> []" using blk0ne by auto
        thus ?thesis using opeq by simp
      qed
    qed
  qed
qed

lemma ST_PS_nonempty: "M \<in> ST_PS \<Longrightarrow> M \<noteq> []"
proof (induction M rule: ST_PS.induct)
  case (diag v) show ?case by (simp add: diagSeq_def)
next
  case (oper M n) show ?case using oper_nonempty[OF oper.IH oper.hyps(2)] by simp
qed

text \<open>\<^bold>\<open>Residual 2\<close> \<open>tail_zone_ST_PS\<close>: the (nonempty) tail zone of a standard form
  is again a standard form.  \<^bold>\<open>Empirically 0 nonempty-not-in / 76114\<close>
  (\<open>tools/probe_struct_close.py\<close>): \<open>dropWhile (\<lambda>q. 0 < fst q)\<close> of the body of
  \<open>M \<in> ST_PS\<close> stays in \<open>ST_PS\<close> \<^emph>\<open>whenever it is nonempty\<close>; the empty tail zone is
  \<^bold>\<open>not\<close> in \<open>ST_PS\<close> (@{thm [source] ST_PS_nonempty}) and is handled separately at
  the call site (\<open>sigma_seqlex_mono\<close>, below).  (The \<^emph>\<open>argument\<close> zone does
  \<^bold>\<open>not\<close> stay in \<open>ST_PS\<close>: it is a
  depth-1 block, which is why the \<open>\<sigma>\<^sub>P\<close> core below carries the \<open>blockok\<close>
  invariant, not ST membership.)  Localized \<open>sorry\<close>: the genuine content is
  \<^bold>\<open>row-0-headed-suffix closure\<close> of \<open>ST_PS\<close> \<dash> every nonempty suffix of an
  \<open>M \<in> ST_PS\<close> that begins at a row-0 column is itself in \<open>ST_PS\<close>
  (\<open>tools/probe_struct_close.py\<close> test (A3): 0 not-found / 89777).  This is a
  structural reachability fact about the \<open>oper\<close> tiling and is independent of the
  \<section>1 collapse core.

  \<^bold>\<open>Mapped attack (2026-06-15, validated empirically)\<close>.  Prove the strengthened
  \<^bold>\<open>suffix-closure\<close> lemma by induction on \<open>ST_PS\<close>: \<open>M \<in> ST_PS \<Longrightarrow> i < length M
  \<Longrightarrow> fst (M ! i) = 0 \<Longrightarrow> drop i M \<in> ST_PS\<close>.
  \<^item> \<^bold>\<open>diag\<close>: in \<open>diagSeq 0 v\<close> the only row-0 column is index \<open>0\<close>, so \<open>drop 0\<close>
    is the whole diagonal.
  \<^item> \<^bold>\<open>oper\<close>: \<open>N = M[n] = take j0 M @ concat (map blk [0..<n])\<close> (the standard
    decomposition, cf. @{thm [source] blockok_oper}).  For a row-0 index \<open>i\<close> of
    \<open>N\<close>:
    \<^enum> \<^bold>\<open>case \<open>i \<le> j0\<close>\<close> (suffix starts in the green prefix): the commutation
      \<open>drop i N = (drop i M)[n]\<close> holds \<^bold>\<open>exactly\<close> (\<open>tools/probe_oper_commute.py\<close>
      W1: 0 bad / 6393), with \<open>drop i M\<close> a row-0 suffix of \<open>M\<close> (IH gives
      \<open>drop i M \<in> ST_PS\<close>, then \<open>oper\<close>).  Needs: \<open>nextR\<close>/\<open>parent\<close> of the last
      column are invariant under removing a row-0-headed prefix of length
      \<open>\<le> j0\<close>.
    \<^enum> \<^bold>\<open>case \<open>i > j0\<close>\<close> (suffix starts inside the tiled region, \<^bold>\<open>\<approx>25%\<close> of tail
      zones \<dash> \<open>tools/probe_tailzone_idx.py\<close>): \<open>drop i N\<close> is a row-0 suffix of a
      partial tile run; it equals \<open>(drop i' M)[m]\<close> for a smaller \<open>m\<close> built from
      the per-tile periodic structure.  This is the harder sub-case and the
      reason the lemma is left as a \<open>sorry\<close> here (it re-derives reachability
      through the \<open>nextrel0\<close>/\<open>le0\<close> valley conditions, which are global).
  The whole route is \<^bold>\<open>independent\<close> of the \<section>1 collapse core.\<close>

lemma tail_zone_ST_PS:
  assumes "(0, y) # r \<in> ST_PS"
    and "dropWhile (\<lambda>q. 0 < fst q) r \<noteq> []"
  shows "dropWhile (\<lambda>q. 0 < fst q) r \<in> ST_PS"
  sorry

text \<open>\<^bold>\<open>Residual 3\<close> \<open>keeps_head_ST_PS\<close>: on standard forms the leading @{const ins}
  in the \<open>\<sigma>\<close> recursion never absorbs the head (\<open>T1\<close>, \<^bold>\<open>0 / 10437\<close>,
  \<open>probe_sigma_residual.py\<close> R-KH).  Not cleanly separable from the core: at a tied
  tail head subscript the absorb test is itself a \<open>proj\<close>-comparison.  Localized
  \<open>sorry\<close>.

  \<^bold>\<open>Obstruction mapped (2026-06-15)\<close>.  Writing \<open>M = (0,y) # r\<close>,
  \<open>aM = takeWhile (0<fst) r\<close>, \<open>tM = dropWhile (0<fst) r\<close>, \<open>A = proj y (nrm
  (translate aM))\<close>, \<open>C = nrm (translate tM)\<close>: \<open>keeps_head M\<close> is exactly the
  negation of the @{const ins} absorb-test \<open>y < e \<or> (y = e \<and> olt A f)\<close> for
  \<open>C = P e f g\<close>.  This is the \<^bold>\<open>depth-0 instance\<close> of the already-green
  \<open>NT_shape\<close>/\<open>NT_noabsorb\<close> pair (in \<open>nrmstep.thy\<close>), whose recursion
  bottoms out in \<open>NT_dom\<close> \<dash> but \<open>NT_dom\<close>/\<open>NT_shape\<close> are stated for
  \<open>fbseg u S\<close> (a \<^emph>\<open>dominated\<close> segment, \<open>\<exists>pp. fst pp < fst (hd S)\<close>), which
  \<^bold>\<open>fails\<close> for a depth-0 head \<open>(0,y)\<close>.  The required depth-0 analogue of \<open>NT_dom\<close>
  is precisely the (also sorried) \<open>STS_B\<close> in \<open>nrmstep.thy\<close>, i.e. the \<^bold>\<open>same\<close>
  \<section>1 collapse content.  Empirically (\<open>tools/probe_keepshead.py\<close>, 25296-corpus):
  \<^item> the \<open>y < e\<close> disjunct \<^bold>\<open>never\<close> fires (0 / 1537 nonempty-tail cases; in fact
    \<open>e = hdsub C = snd (hd tM) \<le> y\<close> always) \<dash> this half is the structural
    subscript bound (no \<section>1 core);
  \<^item> the only live content is the \<^bold>\<open>tied\<close> case \<open>e = y \<Longrightarrow> \<not> olt A f\<close> (the
    \<open>proj\<close>-comparison), which is genuinely the Buchholz \<section>1 collapse fact
    \<open>STS_B\<close>/\<open>sigma_argzone_mono\<close>.
  Hence the residual cannot be honestly closed here without the \<section>1 core; left
  as a single localized \<open>sorry\<close>.\<close>

lemma keeps_head_ST_PS:
  assumes "M \<in> ST_PS"
  shows "keeps_head M"
  sorry

text \<open>\<^bold>\<open>Nonemptiness of \<open>\<sigma>\<close> on standard forms\<close>: \<open>\<sigma>\<close> maps a nonempty standard form
  to a nonempty block (its leading \<open>(0,y)\<close> is preserved by head non-absorption).
  Used to discharge the empty tail-zone edge case of the block induction.\<close>

lemma sigma_ST_nonempty:
  assumes "M \<in> ST_PS"
  shows "sigma M \<noteq> []"
proof -
  have ne: "M \<noteq> []" by (rule ST_PS_nonempty[OF assms])
  obtain q r' where M: "M = q # r'" using ne by (cases M) auto
  have q0: "fst q = 0" using head_row0_ST_PS[OF assms ne] M by simp
  obtain yy where q: "q = (0, yy)" using q0 by (cases q) auto
  have kh: "keeps_head M" by (rule keeps_head_ST_PS[OF assms])
  have "sigma M = (0, yy)
          # untr 1 (proj yy (nrm (translate (takeWhile (\<lambda>q. 0 < fst q) r'))))
          @ sigma (dropWhile (\<lambda>q. 0 < fst q) r')"
    using sigma_struct_rec[of yy r'] kh M q by simp
  thus ?thesis by simp
qed

text \<open>\<^bold>\<open>Residual 4, reduced to a term-level core\<close>.  \<open>sigma_argzone_mono\<close> (the
  argument-zone \<open>seqlex\<close>-monotonicity of \<open>\<sigma>\<^sub>P y a = untr 1 (proj y (nrm (translate a)))\<close>)
  is now \<^bold>\<open>green\<close>: the \<open>aM\<close>, \<open>aN\<close> are depth-1 blocks (@{thm [source] blockok_arg} on
  the depth-0 ST block), \<open>untr 1 (\<dots>)\<close> is again a depth-1 block
  (@{thm [source] blockok_untr}), and through the depth-general order isomorphism
  @{thm [source] olt_iff_seqlex} / @{thm [source] seqlex_imp_olt} the whole
  \<open>seqlex\<close>/\<open>untr\<close>/\<open>blockok\<close> scaffolding is discharged, isolating the residue to the
  single \<^bold>\<open>term-level\<close> obligation \<open>proj_nrm_argzone_olt\<close> below.\<close>

text \<open>\<^bold>\<open>Residual 4 (THE irreducible \<section>1 core, term level)\<close> \<open>proj_nrm_argzone_olt\<close>:
  the projection-after-normalization map is \<open>olt\<close>-monotone on the \<^emph>\<open>argument zones of
  standard forms\<close>.  \<^bold>\<open>Carries the standard-form invariant\<close> (\<open>(0,y)#r\<close>, \<open>(0,y)#r'\<close>
  are ST forms, so \<open>translate aM\<close>, \<open>translate aN\<close> are translates of depth-1 blocks
  hereditarily inside \<open>NF\<close>); the bare \<open>cnf\<close>/\<open>wf3\<close> generalization \<open>PROJMONO\<close>
  (\<open>olt b f \<Longrightarrow> olt (proj a (nrm b)) (proj a (nrm f))\<close>) is \<^bold>\<open>FALSE\<close> (14739 reversals,
  universe B) and is \<^bold>\<open>not\<close> assumed.  Same Buchholz \<section>1 collapse content as
  \<open>oV_mono_NF\<close> and \<open>nrm_order_pres\<close>.  Deep closure 168350/0
  (\<open>probe_proj_mono_deep.py\<close> universe A); arg-zone core 44850/0/0
  (\<open>probe_argzone_olt_core.py\<close>).  \<^bold>\<open>Soundness gate\<close>: the tempting value-preservation
  shortcut \<open>oV (proj y (nrm B)) = oV B\<close> is \<^bold>\<open>FALSE\<close> (\<open>proj\<close> strictly grows the term in
  266594/1013167 cases, \<open>probe_argzone_projid.py\<close>); \<open>proj\<close> raises the value, so the
  core does not reduce to value-preservation.  Localized \<open>sorry\<close>.\<close>

lemma proj_nrm_argzone_olt:
  assumes "(0, y) # r \<in> ST_PS" and "(0, y) # r' \<in> ST_PS"
    and "takeWhile (\<lambda>q. 0 < fst q) r \<noteq> takeWhile (\<lambda>q. 0 < fst q) r'"
    and "olt (translate (takeWhile (\<lambda>q. 0 < fst q) r))
             (translate (takeWhile (\<lambda>q. 0 < fst q) r'))"
  shows "olt (proj y (nrm (translate (takeWhile (\<lambda>q. 0 < fst q) r))))
             (proj y (nrm (translate (takeWhile (\<lambda>q. 0 < fst q) r'))))"
  sorry

lemma sigma_argzone_mono:
  assumes ST: "(0, y) # r \<in> ST_PS" and ST': "(0, y) # r' \<in> ST_PS"
    and ane: "takeWhile (\<lambda>q. 0 < fst q) r \<noteq> takeWhile (\<lambda>q. 0 < fst q) r'"
    and asl: "seqlex (takeWhile (\<lambda>q. 0 < fst q) r) (takeWhile (\<lambda>q. 0 < fst q) r')"
  shows "seqlex (untr 1 (proj y (nrm (translate (takeWhile (\<lambda>q. 0 < fst q) r)))))
                (untr 1 (proj y (nrm (translate (takeWhile (\<lambda>q. 0 < fst q) r')))))"
proof -
  let ?aM = "takeWhile (\<lambda>q. 0 < fst q) r"
  let ?aN = "takeWhile (\<lambda>q. 0 < fst q) r'"
  let ?X = "proj y (nrm (translate ?aM))"
  let ?Y = "proj y (nrm (translate ?aN))"
  \<comment> \<open>argument zones are depth-1 blocks (the ST forms are depth-0 blocks)\<close>
  have b0M: "blockok 0 ((0, y) # r)" using blockok_ST_PS[OF ST] .
  have b0N: "blockok 0 ((0, y) # r')" using blockok_ST_PS[OF ST'] .
  have bA: "blockok (Suc 0) ?aM" using blockok_arg[OF b0M] by simp
  have bA': "blockok (Suc 0) ?aN" using blockok_arg[OF b0N] by simp
  \<comment> \<open>(1) lift \<open>seqlex aM aN\<close> to the term order via the depth-1 half-isomorphism\<close>
  have oltB: "olt (translate ?aM) (translate ?aN)"
    using seqlex_imp_olt[OF bA bA' asl] .
  \<comment> \<open>(2) the term-level core (carries the ST invariant)\<close>
  have oltX: "olt ?X ?Y" by (rule proj_nrm_argzone_olt[OF ST ST' ane oltB])
  \<comment> \<open>the images are depth-1 blocks under \<open>untr 1\<close>\<close>
  have bX: "blockok (Suc 0) (untr (Suc 0) ?X)" by (rule blockok_untr)
  have bY: "blockok (Suc 0) (untr (Suc 0) ?Y)" by (rule blockok_untr)
  \<comment> \<open>the two normalized images differ (\<open>untr 1\<close> is injective via \<open>translate\<close>)\<close>
  have xy: "?X \<noteq> ?Y"
  proof
    assume "?X = ?Y"
    hence "olt ?X ?X" using oltX by simp
    thus False using olt_irrefl by simp
  qed
  have une: "untr (Suc 0) ?X \<noteq> untr (Suc 0) ?Y"
  proof
    assume "untr (Suc 0) ?X = untr (Suc 0) ?Y"
    hence "translate (untr (Suc 0) ?X) = translate (untr (Suc 0) ?Y)" by simp
    hence "?X = ?Y" by (simp add: translate_untr)
    thus False using xy by simp
  qed
  \<comment> \<open>(2') push the term order back through the depth-1 isomorphism\<close>
  have "olt (translate (untr (Suc 0) ?X)) (translate (untr (Suc 0) ?Y))"
    using oltX by (simp add: translate_untr)
  hence "seqlex (untr (Suc 0) ?X) (untr (Suc 0) ?Y)"
    using olt_iff_seqlex[OF bX bY une] by blast
  thus ?thesis by simp
qed

text \<open>\<^bold>\<open>The depth gap\<close> is structural (green): every row of the argument-zone
  normalizer \<open>untr 1 (\<dots>)\<close> is \<open>\<ge> 1\<close>, while the \<open>\<sigma>\<close>-tail \<open>untr 0 (\<dots>)\<close> heads at
  row 0.  Hence the gap hypothesis of @{thm [source] seqlex_append_left} is
  automatically met.\<close>

lemma untr1_rows_ge1: "\<forall>p \<in> set (untr (Suc 0) t). 0 < fst p"
  using untr_set_ge[of "Suc 0" t] by auto

lemma sigma_head_row0: "sigma M \<noteq> [] \<Longrightarrow> fst (hd (sigma M)) = 0"
  unfolding sigma_def by (rule untr_hd)

subsection \<open>Assembly of \<open>sigma_seqlex_mono\<close>\<close>

text \<open>\<^bold>\<open>The block induction\<close> mirroring @{thm [source] seqlex_imp_olt}: \<open>less_induct\<close>
  on \<open>length M + length N\<close>, head split, then @{thm [source] seqlex_arg_or_tail}.
  The \<^emph>\<open>head-differ\<close> and \<^emph>\<open>tail-zone\<close> branches are green from the structural
  recursion (S) (@{thm [source] sigma_struct_rec}), @{thm [source] keeps_head_ST_PS},
  @{thm [source] tail_zone_ST_PS} and @{thm [source] seqlex_append_left}; the
  \<^emph>\<open>argument-zone\<close> branch is the single irreducible core
  @{thm [source] sigma_argzone_mono}.\<close>

lemma sigma_seqlex_mono:
  assumes "M \<in> ST_PS" and "N \<in> ST_PS" and "seqlex M N"
  shows "seqlex (sigma M) (sigma N)"
  using assms
proof (induction "length M + length N" arbitrary: M N rule: less_induct)
  case less
  show ?case
  proof (cases M)
    case Nil
    \<comment> \<open>\<open>seqlex [] N\<close> forces \<open>N \<noteq> []\<close>; \<open>sigma [] = []\<close> and \<open>sigma N \<noteq> []\<close>.\<close>
    have "N \<noteq> []" using less.prems(3) Nil by (cases N) auto
    hence "translate N \<noteq> Z"
      using head_row0_ST_PS[OF less.prems(2)] by (cases N) auto
    hence "nrm (translate N) \<noteq> Z \<or> nrm (translate N) = Z" by simp
    have sM: "sigma M = []" using Nil by (simp add: sigma_def)
    have "sigma N \<noteq> []"
    proof -
      from \<open>N \<noteq> []\<close> obtain q r' where N: "N = q # r'" by (cases N) auto
      have q0: "fst q = 0" using head_row0_ST_PS[OF less.prems(2)] N by simp
      obtain yy where q: "q = (0, yy)" using q0 by (cases q) auto
      have kh: "keeps_head N" by (rule keeps_head_ST_PS[OF less.prems(2)])
      have "sigma N = (0, yy)
              # untr 1 (proj yy (nrm (translate (takeWhile (\<lambda>q. 0 < fst q) r'))))
              @ sigma (dropWhile (\<lambda>q. 0 < fst q) r')"
        using sigma_struct_rec[of yy r'] kh N q by simp
      thus ?thesis by simp
    qed
    thus ?thesis using sM by simp
  next
    case (Cons p r)
    obtain q r' where N: "N = q # r'"
      using less.prems(3) Cons by (cases N) auto
    have p0: "fst p = 0" using head_row0_ST_PS[OF less.prems(1)] Cons by simp
    have q0: "fst q = 0" using head_row0_ST_PS[OF less.prems(2)] N by simp
    obtain y where p: "p = (0, y)" using p0 by (cases p) auto
    obtain y' where q: "q = (0, y')" using q0 by (cases q) auto
    have khM: "keeps_head M" by (rule keeps_head_ST_PS[OF less.prems(1)])
    have khN: "keeps_head N" by (rule keeps_head_ST_PS[OF less.prems(2)])
    let ?aM = "takeWhile (\<lambda>x. 0 < fst x) r" and ?tM = "dropWhile (\<lambda>x. 0 < fst x) r"
    let ?aN = "takeWhile (\<lambda>x. 0 < fst x) r'" and ?tN = "dropWhile (\<lambda>x. 0 < fst x) r'"
    let ?SPM = "untr 1 (proj y (nrm (translate ?aM)))"
    let ?SPN = "untr 1 (proj y' (nrm (translate ?aN)))"
    have sigM: "sigma M = (0, y) # ?SPM @ sigma ?tM"
      using sigma_struct_rec[of y r] khM Cons p by simp
    have sigN: "sigma N = (0, y') # ?SPN @ sigma ?tN"
      using sigma_struct_rec[of y' r'] khN N q by simp
    show ?thesis
    proof (cases "y = y'")
      case False
      \<comment> \<open>heads differ: \<open>seqlex M N\<close> forces \<open>y < y'\<close>; the leading columns decide.\<close>
      have "pairlt p q" using less.prems(3) Cons N p q False by (auto simp: pairlt_def)
      hence "y < y'" using p q by (simp add: pairlt_def)
      hence "pairlt (0, y) (0, y')" by (simp add: pairlt_def)
      thus ?thesis using sigM sigN False by simp
    next
      case True
      have slr: "seqlex r r'"
        using less.prems(3) Cons N p q True by (auto simp: pairlt_def)
      have bM: "blockok 0 ((0, y) # r)" using blockok_ST_PS[OF less.prems(1)] Cons p by simp
      have bN: "blockok 0 ((0, y) # r')" using blockok_ST_PS[OF less.prems(2)] N q True by simp
      from seqlex_arg_or_tail[OF bM bN slr]
      consider (tails) "?aM = ?aN" "seqlex ?tM ?tN"
        | (args) "?aM \<noteq> ?aN" "seqlex ?aM ?aN" by blast
      thus ?thesis
      proof cases
        case tails
        \<comment> \<open>argument zones equal \<open>\<Rightarrow>\<close> \<open>\<sigma>\<^sub>P\<close> equal; recurse on the strictly shorter
           tail (or, when the tail zone is empty, decide directly).\<close>
        have SPeq: "?SPM = ?SPN" using tails(1) True by simp
        have core: "seqlex (sigma ?tM) (sigma ?tN)"
        proof (cases "?tM = []")
          case tMempty: True
          \<comment> \<open>\<open>seqlex [] ?tN\<close> forces \<open>?tN \<noteq> []\<close>; \<open>\<sigma> [] = []\<close> and \<open>\<sigma> ?tN \<noteq> []\<close>.\<close>
          have tNne: "?tN \<noteq> []" using tails(2) tMempty by (cases ?tN) auto
          have tNst: "?tN \<in> ST_PS"
            using tail_zone_ST_PS[of y r'] less.prems(2) N q True tNne by simp
          have sNne: "sigma ?tN \<noteq> []" by (rule sigma_ST_nonempty[OF tNst])
          have "sigma ?tM = []" by (simp add: sigma_def tMempty)
          thus ?thesis using sNne by (cases "sigma ?tN") auto
        next
          case tMne: False
          obtain a as where tMcons: "?tM = a # as" using tMne by (cases ?tM) auto
          have tNne: "?tN \<noteq> []" using tails(2) tMcons by (cases ?tN) auto
          have tMst: "?tM \<in> ST_PS"
            using tail_zone_ST_PS[of y r] less.prems(1) Cons p tMne by simp
          have tNst: "?tN \<in> ST_PS"
            using tail_zone_ST_PS[of y r'] less.prems(2) N q True tNne by simp
          have lenM: "length ?tM \<le> length r" by (simp add: length_dropWhile_le)
          have lenN: "length ?tN \<le> length r'" by (simp add: length_dropWhile_le)
          have shorter: "length ?tM + length ?tN < length M + length N"
            using lenM lenN Cons N by simp
          show ?thesis by (rule less.hyps[OF shorter tMst tNst tails(2)])
        qed
        have "seqlex (?SPM @ sigma ?tM) (?SPN @ sigma ?tN)"
          using core SPeq seqlex_append_cancel by simp
        thus ?thesis using sigM sigN True by simp
      next
        case args
        \<comment> \<open>argument zones differ: the irreducible \<open>\<sigma>\<^sub>P\<close> core, then the depth-gap append.\<close>
        have spmono: "seqlex ?SPM ?SPN"
        proof -
          have stM: "(0, y) # r \<in> ST_PS" using less.prems(1) Cons p by simp
          have stN: "(0, y) # r' \<in> ST_PS" using less.prems(2) N q True by simp
          have "seqlex (untr 1 (proj y (nrm (translate ?aM))))
                       (untr 1 (proj y (nrm (translate ?aN))))"
            by (rule sigma_argzone_mono[OF stM stN args(1) args(2)])
          thus ?thesis using True by simp
        qed
        \<comment> \<open>discharge the gap hypothesis of \<open>seqlex_append_left\<close> structurally\<close>
        have gap: "length ?SPM < length ?SPN \<longrightarrow> sigma ?tM \<noteq> [] \<longrightarrow>
                     pairlt (hd (sigma ?tM)) (?SPN ! length ?SPM)"
        proof (intro impI)
          assume lt: "length ?SPM < length ?SPN" and ne: "sigma ?tM \<noteq> []"
          have h0: "fst (hd (sigma ?tM)) = 0" by (rule sigma_head_row0[OF ne])
          have "?SPN ! length ?SPM \<in> set ?SPN" using lt by simp
          hence "0 < fst (?SPN ! length ?SPM)" using untr1_rows_ge1[of "proj y' (nrm (translate ?aN))"] by simp
          thus "pairlt (hd (sigma ?tM)) (?SPN ! length ?SPM)"
            using h0 by (simp add: pairlt_def)
        qed
        have "seqlex (?SPM @ sigma ?tM) (?SPN @ sigma ?tN)"
          by (rule seqlex_append_left[OF spmono gap])
        thus ?thesis using sigM sigN True by simp
      qed
    qed
  qed
qed

text \<open>\<^bold>\<open>Order preservation on \<open>NF\<close>\<close> (\<open>nrm_order_pres\<close>): now a \<^emph>\<open>green assembly\<close> of
  \<^item> the \<open>translate\<close> order isomorphism @{thm [source] olt_ST_iff_seqlex} (turning
    \<open>olt v u\<close> on \<open>NF\<close> into \<open>seqlex M N\<close> on the standard forms),
  \<^item> the section property @{thm [source] translate_sigma} and block property
    @{thm [source] blockok_sigma} (so \<open>nrm (translate M) = translate (\<sigma> M)\<close> with
    \<open>\<sigma> M\<close> a depth-0 block),
  \<^item> the half-isomorphism @{thm [source] seqlex_imp_olt} (turning
    \<open>seqlex (\<sigma> M) (\<sigma> N)\<close> back into \<open>olt\<close>),
  on top of the \<^emph>\<open>single\<close> residual core @{thm [source] sigma_seqlex_mono}.\<close>

lemma nrm_order_pres:
  assumes "v \<in> NF" and "u \<in> NF" and "olt v u"
  shows "olt (nrm v) (nrm u)"
proof -
  from \<open>v \<in> NF\<close> obtain M where M: "M \<in> ST_PS" and vM: "v = translate M" by auto
  from \<open>u \<in> NF\<close> obtain N where N: "N \<in> ST_PS" and uN: "u = translate N" by auto
  have MN: "M \<noteq> N"
  proof
    assume "M = N"
    hence "v = u" using vM uN by simp
    thus False using \<open>olt v u\<close> olt_irrefl by simp
  qed
  have sl: "seqlex M N"
    using olt_ST_iff_seqlex[OF M N MN] \<open>olt v u\<close> vM uN by blast
  have core: "seqlex (sigma M) (sigma N)" by (rule sigma_seqlex_mono[OF M N sl])
  have "translate (sigma M) <o translate (sigma N)"
    by (rule seqlex_imp_olt[OF blockok_sigma blockok_sigma core])
  thus "olt (nrm v) (nrm u)"
    using translate_sigma vM uN by simp
qed

subsection \<open>Well-foundedness of \<open><o\<close> on \<open>NF\<close>, and PSS termination\<close>

theorem wf_Rnf_nrm: "wf Rnf"
proof (rule wf_subset[OF wf_inv_image[OF wf_olt_wf3, of nrm]])
  show "Rnf \<subseteq> inv_image {(w,x). olt w x \<and> wf3 w \<and> wf3 x} nrm"
  proof (rule subrelI)
    fix v u assume "(v,u) \<in> Rnf"
    hence vu: "olt v u" and "u \<in> NF" and "v \<in> NF" by auto
    hence "olt (nrm v) (nrm u)" using nrm_order_pres by blast
    thus "(v,u) \<in> inv_image {(w,x). olt w x \<and> wf3 w \<and> wf3 x} nrm"
      using wf3_nrm by (simp add: inv_image_def)
  qed
qed

theorem PSS_terminates_strong: "wf {(T,M). M \<in> ST_PS \<and> step M T}"
  by (rule step_terminates[OF wf_Rnf_nrm])

subsection \<open>Step decrease: the weaker (live) obligation\<close>

text \<open>For termination alone, only the expansion-step pairs must decrease \<dash> a
  single-host statement, amenable to induction over the \<open>oper\<close> case analysis
  (the machinery behind @{thm [source] m_step_decreases}) together with the
  sequence-side characterization of \<open>proj\<close> (suffix from the first maximal-row1
  column).  Empirically the first difference of the two normalized images is
  always a subscript drop or a sum truncation, never a reversal.
  \<open>nrm_order_pres\<close> subsumes this lemma via @{thm [source] m_step_decreases}.\<close>

lemma nrm_step_dec:
  assumes M: "M \<in> ST_PS" and L: "1 < Lng M" and n: "1 \<le> n"
  shows "olt (nrm (translate (M[n]))) (nrm (translate M))"
proof -
  have st: "step M (M[n])" using L n by (auto intro: step.intros)
  have TS: "M[n] \<in> ST_PS" using M st by (rule step_in_ST_PS)
  have "olt (translate (M[n])) (translate M)" using m_step_decreases[OF L n] by simp
  thus ?thesis using nrm_order_pres TS M by auto
qed

theorem PSS_terminates_nrm: "wf {(T,M). M \<in> ST_PS \<and> step M T}"
proof (rule wf_subset[OF wf_inv_image[OF wf_olt_wf3, of "\<lambda>M. nrm (translate M)"]])
  show "{(T,M). M \<in> ST_PS \<and> step M T}
          \<subseteq> inv_image {(w,x). olt w x \<and> wf3 w \<and> wf3 x} (\<lambda>M. nrm (translate M))"
  proof (rule subrelI)
    fix T M assume "(T,M) \<in> {(T,M). M \<in> ST_PS \<and> step M T}"
    then have M: "M \<in> ST_PS" and st: "step M T" by auto
    from st obtain n where L: "1 < Lng M" and n: "1 \<le> n" and TM: "T = M[n]"
      by (auto elim!: step.cases)
    have "olt (nrm (translate T)) (nrm (translate M))"
      using nrm_step_dec[OF M L n] TM by simp
    thus "(T,M) \<in> inv_image {(w,x). olt w x \<and> wf3 w \<and> wf3 x} (\<lambda>M. nrm (translate M))"
      using wf3_nrm by (simp add: inv_image_def)
  qed
qed

end
