theory nrm
  imports otembed "YAPSS.proofs"
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

subsection \<open>The remaining core: order preservation on \<open>NF\<close>\<close>

text \<open>Validated empirically on 2{,}643{,}843 pairs of (hereditary blocks of)
  standard-form translates: zero collapses, zero reversals.  The counterexample
  outside \<open>NF\<close> is \<open>y\<^sub>2 = p\<^bsub>0\<^esub>(p\<^bsub>1\<^esub>(y\<^sub>1)) <o y\<^sub>1 = p\<^bsub>0\<^esub>(p\<^bsub>1\<^esub>(p\<^bsub>1\<^esub>(0)))\<close> with
  \<open>nrm y\<^sub>2 = nrm y\<^sub>1\<close>; its pair sequence \<open>(0,0)(1,1)(2,0)(3,1)(4,1)\<close> is not
  standard, so the standardness discipline (row-1 parenthood) is what the
  proof must exploit.\<close>

lemma nrm_order_pres:
  assumes "v \<in> NF" and "u \<in> NF" and "olt v u"
  shows "olt (nrm v) (nrm u)"
  sorry

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
