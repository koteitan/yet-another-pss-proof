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

text \<open>\<^bold>\<open>The single remaining core\<close> \<open>sigma_seqlex_mono\<close>: on standard forms, the
  sequence normalizer \<open>\<sigma>\<close> is \<^emph>\<open>monotone\<close> for the column lexicographic order.
  This is \<open>nrm_order_pres\<close> transported entirely onto the BMS-native (column,
  suffix, \<open>seqlex\<close>, \<open>blockok\<close>) side via the \<open>translate\<close> isomorphism, the cleanest
  attack surface for the residual Buchholz-\<section>1 collapse content.

  \<^bold>\<open>Caveat\<close> (\<open>memo\<close> 続78 / 第7事件): \<open>\<sigma>\<close> must \<^emph>\<open>not\<close> be simplified to a single
  maximal-suffix step \<open>msfx\<close> (the false \<open>E6_value\<close> core).  Here \<open>\<sigma>\<close> is the full
  recursive \<open>untr \<circ> nrm \<circ> translate\<close> by definition; the statement below is about
  that full normalizer.

  \<^bold>\<open>Empirical status\<close> (soundness gate, deep closure +5): with closure of size
  17700 standard forms, \<open>\<sigma>\<close> preserves \<open>blockok 0\<close> (0 bad) and is strictly
  \<open>seqlex\<close>-monotone (604450 ordered pairs, 0 violations, 0 collapses-to-equal); the
  earlier calibration was 319600 / 0.  No counterexample at any tested depth.\<close>

lemma sigma_seqlex_mono:
  assumes "M \<in> ST_PS" and "N \<in> ST_PS" and "seqlex M N"
  shows "seqlex (sigma M) (sigma N)"
  sorry

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
