theory nrmstep
  imports nrm "YAPSS.seqlex"
begin

text \<open>
  \<^bold>\<open>Campaign file\<close> for the direct proof of \<open>nrm_step_dec\<close> (and ultimately
  \<open>nrm_order_pres\<close>), via the \<^emph>\<open>one-position increase\<close> relations.

  Empirical theorem (2263 snoc pairs, exact): for standard \<open>C @ [m]\<close>,
  \<open>nrm (translate (C @ [m]))\<close> is obtained from \<open>nrm (translate C)\<close> by exactly
  one of
    \<^item> inserting one leaf \<open>P w Z Z\<close> at a \<open>Z\<close>-position (tail end or empty arg), or
    \<^item> incrementing the subscript of one leaf (the fire-flip
      \<open>D\<^bsub>y'\<^esub>(0) \<rightarrow> D\<^bsub>y\<^esub>(0)\<close>, \<open>y' < y\<close>).
  Both strictly increase \<open><o\<close> by single-position congruence.  The campaign:
  prove the closure of these relations under \<open>proj\<close>/\<open>ins\<close>/\<open>nrm\<close> along the
  recursion, yielding the \<open>Pred\<close> case of \<open>nrm_step_dec\<close>; then the copy (bad)
  case on the same machinery.
\<close>

subsection \<open>One-position increase relations\<close>

text \<open>\<open>lext\<close>: one leaf inserted at a \<open>Z\<close>-position (deepest tail end or empty
  argument).  \<open>lflip\<close>: one leaf's subscript incremented.\<close>

inductive lext :: "three \<Rightarrow> three \<Rightarrow> bool" where
  lext_end:  "lext Z (P w Z Z)"
| lext_tail: "lext c c' \<Longrightarrow> lext (P a b c) (P a b c')"
| lext_arg:  "lext b b' \<Longrightarrow> lext (P a b c) (P a b' c)"

inductive lflip :: "three \<Rightarrow> three \<Rightarrow> bool" where
  lflip_leaf: "w < w' \<Longrightarrow> lflip (P w Z Z) (P w' Z Z)"
| lflip_tail: "lflip c c' \<Longrightarrow> lflip (P a b c) (P a b c')"
| lflip_arg:  "lflip b b' \<Longrightarrow> lflip (P a b c) (P a b' c)"

definition Rinc :: "three \<Rightarrow> three \<Rightarrow> bool" where
  "Rinc x y \<longleftrightarrow> lext x y \<or> lflip x y"

lemma lext_olt: "lext x y \<Longrightarrow> olt x y"
proof (induction rule: lext.induct)
  case (lext_end w) show ?case by simp
next
  case (lext_tail c c' a b) thus ?case using olt_P_c by simp
next
  case (lext_arg b b' a c) thus ?case using olt_P_b by simp
qed

lemma lflip_olt: "lflip x y \<Longrightarrow> olt x y"
proof (induction rule: lflip.induct)
  case (lflip_leaf w w') thus ?case by simp
next
  case (lflip_tail c c' a b) thus ?case using olt_P_c by simp
next
  case (lflip_arg b b' a c) thus ?case using olt_P_b by simp
qed

lemma Rinc_olt: "Rinc x y \<Longrightarrow> olt x y"
  unfolding Rinc_def using lext_olt lflip_olt by blast

subsection \<open>Unconditional \<open>proj\<close> facts\<close>

text \<open>\<open>proj\<close> is inflationary: each firing step moves to a critical term that is
  not below the current one, hence (being distinct, by size) strictly above.\<close>

lemma proj_inflate: "olt b (proj u b) \<or> proj u b = b"
proof (induction u b rule: proj.induct)
  case (1 u b)
  show ?case
  proof (cases "filter (\<lambda>g. \<not> olt g b) (Glist u b) = []")
    case True
    show ?thesis unfolding proj_id[OF True] by simp
  next
    case False
    let ?gs = "filter (\<lambda>g. \<not> olt g b) (Glist u b)"
    let ?m = "maxo (hd ?gs) (tl ?gs)"
    have mset: "?m \<in> set ?gs" by (rule maxo_hdtl_in[OF False])
    hence mG: "?m \<in> Gterm u b" using set_Glist by auto
    have mne: "?m \<noteq> b" using Gterm_size[OF mG] by auto
    have mnlt: "\<not> olt ?m b" using mset by auto
    have step: "olt b ?m" using olt_total mne mnlt by blast
    have rec: "olt ?m (proj u ?m) \<or> proj u ?m = ?m" by (rule 1(1)[OF refl False])
    have eq: "proj u b = proj u ?m" using proj_rec[OF False] by simp
    show ?thesis using rec step eq olt_trans by auto
  qed
qed

lemma proj_ole: "b \<le>o proj u b"
  using proj_inflate[of b u] by auto

subsection \<open>Critical sets under leaf insertion\<close>

text \<open>The engine of the closure: inserting one leaf transforms the critical
  collection pointwise \<dash> every new critical is an old one, a leaf-extension of
  an old one, or the trivial \<open>Z\<close>; and no critical is lost.\<close>

lemma Gterm_lext_sub:
  "lext b b' \<Longrightarrow> \<forall>g' \<in> Gterm u b'. g' \<in> Gterm u b \<or> (\<exists>g \<in> Gterm u b. lext g g') \<or> g' = Z"
proof (induction arbitrary: u rule: lext.induct)
  case (lext_end w)
  show ?case by simp
next
  case (lext_tail c c' a b)
  show ?case
  proof
    fix g' assume "g' \<in> Gterm u (P a b c')"
    then consider "u \<le> a" "g' = b \<or> g' \<in> Gterm u b" | "g' \<in> Gterm u c'"
      by (auto split: if_splits)
    thus "g' \<in> Gterm u (P a b c) \<or> (\<exists>g \<in> Gterm u (P a b c). lext g g') \<or> g' = Z"
    proof cases
      case 1 thus ?thesis by auto
    next
      case 2
      from lext_tail.IH[of u] 2 show ?thesis by fastforce
    qed
  qed
next
  case (lext_arg b b' a c)
  show ?case
  proof
    fix g' assume "g' \<in> Gterm u (P a b' c)"
    then consider "u \<le> a" "g' = b'" | "u \<le> a" "g' \<in> Gterm u b'" | "g' \<in> Gterm u c"
      by (auto split: if_splits)
    thus "g' \<in> Gterm u (P a b c) \<or> (\<exists>g \<in> Gterm u (P a b c). lext g g') \<or> g' = Z"
    proof cases
      case 1
      have "b \<in> Gterm u (P a b c)" using 1 by simp
      thus ?thesis using 1 lext_arg.hyps by auto
    next
      case 2
      from lext_arg.IH[of u] 2 show ?thesis by fastforce
    next
      case 3 thus ?thesis by auto
    qed
  qed
qed

lemma Gterm_lext_sup:
  "lext b b' \<Longrightarrow> \<forall>g \<in> Gterm u b. g \<in> Gterm u b' \<or> (\<exists>g' \<in> Gterm u b'. lext g g')"
proof (induction arbitrary: u rule: lext.induct)
  case (lext_end w)
  show ?case by simp
next
  case (lext_tail c c' a b)
  show ?case
  proof
    fix g assume "g \<in> Gterm u (P a b c)"
    then consider "u \<le> a" "g = b \<or> g \<in> Gterm u b" | "g \<in> Gterm u c"
      by (auto split: if_splits)
    thus "g \<in> Gterm u (P a b c') \<or> (\<exists>g' \<in> Gterm u (P a b c'). lext g g')"
    proof cases
      case 1 thus ?thesis by auto
    next
      case 2
      from lext_tail.IH[of u] 2 show ?thesis by fastforce
    qed
  qed
next
  case (lext_arg b b' a c)
  show ?case
  proof
    fix g assume "g \<in> Gterm u (P a b c)"
    then consider "u \<le> a" "g = b" | "u \<le> a" "g \<in> Gterm u b" | "g \<in> Gterm u c"
      by (auto split: if_splits)
    thus "g \<in> Gterm u (P a b' c) \<or> (\<exists>g' \<in> Gterm u (P a b' c). lext g g')"
    proof cases
      case 1
      have "b' \<in> Gterm u (P a b' c)" using 1 by simp
      thus ?thesis using 1 lext_arg.hyps by auto
    next
      case 2
      from lext_arg.IH[of u] 2 show ?thesis by fastforce
    next
      case 3 thus ?thesis by auto
    qed
  qed
qed

subsection \<open>Campaign targets\<close>

text \<open>(T1) the snoc characterization: appending one column to a standard form
  changes the normalized image by exactly one \<open>Rinc\<close> step.  (T2) hence the
  \<open>Pred\<close> case of the step decrease.  The closure lemmas of \<open>Rinc\<close> under
  \<open>proj\<close>/\<open>ins\<close> along the \<open>translate\<close> recursion are the planned route to (T1).\<close>

subsection \<open>\<open>ins\<close> congruence under \<open>Rinc\<close>\<close>

text \<open>Head principal of a (nonzero) sum, for absorb-condition bookkeeping.\<close>

fun hdsub :: "three \<Rightarrow> nat" where
  "hdsub Z = 0" | "hdsub (P e f g) = e"
fun hdarg :: "three \<Rightarrow> three" where
  "hdarg Z = Z" | "hdarg (P e f g) = f"

lemma ins_noabsorb:
  assumes "t = Z \<or> \<not> (a < hdsub t \<or> (a = hdsub t \<and> olt b (hdarg t)))"
  shows "ins a b t = P a b t"
  using assms by (cases t) auto

lemma ins_Rinc:
  assumes R: "Rinc t t'"
    and na:  "t = Z \<or> \<not> (a < hdsub t \<or> (a = hdsub t \<and> olt b (hdarg t)))"
    and na': "t' = Z \<or> \<not> (a < hdsub t' \<or> (a = hdsub t' \<and> olt b (hdarg t')))"
  shows "Rinc (ins a b t) (ins a b t')"
proof -
  have e:  "ins a b t = P a b t"  by (rule ins_noabsorb[OF na])
  have e': "ins a b t' = P a b t'" by (rule ins_noabsorb[OF na'])
  show ?thesis using R unfolding e e' Rinc_def
    by (auto intro: lext.intros lflip.intros)
qed

text \<open>\<open>ins\<close> is monotone in its sum argument \<^emph>\<open>unconditionally\<close>: if absorption
  fires on the right side only, the right head already dominates \<open>(a,b)\<close>; and
  absorption on the left forces absorption on the right (via transitivity).\<close>

lemma ins_olt_mono:
  assumes "olt t t'"
  shows "olt (ins a b t) (ins a b t')"
proof (cases t)
  case Z
  show ?thesis
  proof (cases t')
    case Z' : Z
    thus ?thesis using assms Z by simp
  next
    case (P e f g)
    show ?thesis
    proof (cases "a < e \<or> (a = e \<and> olt b f)")
      case True
      have r: "ins a b t' = P e f g" using P True by simp
      have "olt (P a b Z) (P e f g)" using True by auto
      thus ?thesis using Z P r by simp
    next
      case False
      thus ?thesis using Z P by simp
    qed
  qed
next
  case tP: (P e0 f0 g0)
  show ?thesis
  proof (cases t')
    case Z
    thus ?thesis using assms tP by simp
  next
    case t'P: (P e1 f1 g1)
    show ?thesis
    proof (cases "a < e0 \<or> (a = e0 \<and> olt b f0)")
      case abs_t: True
      have abs_t': "a < e1 \<or> (a = e1 \<and> olt b f1)"
      proof -
        from assms tP t'P have lt: "e0 < e1 \<or> (e0 = e1 \<and> olt f0 f1) \<or> (e0 = e1 \<and> f0 = f1 \<and> olt g0 g1)"
          by simp
        from abs_t show ?thesis
        proof
          assume "a < e0"
          thus ?thesis using lt by auto
        next
          assume ae: "a = e0 \<and> olt b f0"
          from lt show ?thesis
          proof (elim disjE conjE)
            assume "e0 < e1" thus ?thesis using ae by auto
          next
            assume "e0 = e1" "olt f0 f1"
            thus ?thesis using ae olt_trans by auto
          next
            assume "e0 = e1" "f0 = f1" "olt g0 g1"
            thus ?thesis using ae by auto
          qed
        qed
      qed
      have l: "ins a b t = t" using tP abs_t by simp
      have r: "ins a b t' = t'" using t'P abs_t' by simp
      show ?thesis unfolding l r by (rule assms)
    next
      case nabs_t: False
      show ?thesis
      proof (cases "a < e1 \<or> (a = e1 \<and> olt b f1)")
        case abs_t': True
        have l: "ins a b t = P a b t" using tP nabs_t by simp
        have r: "ins a b t' = t'" using t'P abs_t' by simp
        have "olt (P a b t) t'" using abs_t' t'P by auto
        thus ?thesis unfolding l r .
      next
        case nabs_t': False
        have l: "ins a b t = P a b t" using tP nabs_t by simp
        have r: "ins a b t' = P a b t'" using t'P nabs_t' by simp
        show ?thesis unfolding l r using assms by (rule olt_P_c)
      qed
    qed
  qed
qed

lemma Gterm_lflip_sup:
  "lflip b b' \<Longrightarrow> \<forall>g \<in> Gterm u b. g \<in> Gterm u b' \<or> (\<exists>g' \<in> Gterm u b'. lflip g g')"
proof (induction arbitrary: u rule: lflip.induct)
  case (lflip_leaf w w')
  show ?case using lflip_leaf.hyps by auto
next
  case (lflip_tail c c' a b)
  show ?case
  proof
    fix g assume "g \<in> Gterm u (P a b c)"
    then consider "u \<le> a" "g = b \<or> g \<in> Gterm u b" | "g \<in> Gterm u c"
      by (auto split: if_splits)
    thus "g \<in> Gterm u (P a b c') \<or> (\<exists>g' \<in> Gterm u (P a b c'). lflip g g')"
    proof cases
      case 1 thus ?thesis by auto
    next
      case 2
      from lflip_tail.IH[of u] 2 show ?thesis by fastforce
    qed
  qed
next
  case (lflip_arg b b' a c)
  show ?case
  proof
    fix g assume "g \<in> Gterm u (P a b c)"
    then consider "u \<le> a" "g = b" | "u \<le> a" "g \<in> Gterm u b" | "g \<in> Gterm u c"
      by (auto split: if_splits)
    thus "g \<in> Gterm u (P a b' c) \<or> (\<exists>g' \<in> Gterm u (P a b' c). lflip g g')"
    proof cases
      case 1
      have "b' \<in> Gterm u (P a b' c)" using 1 by simp
      thus ?thesis using 1 lflip_arg.hyps by auto
    next
      case 2
      from lflip_arg.IH[of u] 2 show ?thesis by fastforce
    next
      case 3 thus ?thesis by auto
    qed
  qed
qed

text \<open>The selected maximum is an upper bound (deterministic re-proof; needed
  for the max-critical correspondence in the both-fire case).\<close>

lemma maxo_ub: "z \<in> insert x (set ys) \<Longrightarrow> \<not> olt (maxo x ys) z"
proof (induction ys arbitrary: x z)
  case Nil
  hence "z = x" by simp
  thus ?case using olt_irrefl by simp
next
  case (Cons y ys)
  let ?m = "if olt x y then y else x"
  have ub: "\<And>w. w \<in> insert ?m (set ys) \<Longrightarrow> \<not> olt (maxo ?m ys) w"
    using Cons.IH by blast
  have inm: "\<not> olt (maxo ?m ys) ?m" using ub by simp
  have mx: "\<not> olt (maxo ?m ys) x"
  proof (cases "olt x y")
    case True
    have my: "\<not> olt (maxo y ys) y" using inm True by simp
    show ?thesis
    proof
      assume "olt (maxo ?m ys) x"
      hence "olt (maxo y ys) x" using True by simp
      hence "olt (maxo y ys) y" using True olt_trans by blast
      thus False using my by blast
    qed
  next
    case False
    thus ?thesis using inm by simp
  qed
  have my: "\<not> olt (maxo ?m ys) y"
  proof (cases "olt x y")
    case True thus ?thesis using inm by simp
  next
    case False
    have yx: "olt y x \<or> y = x" using False olt_total by blast
    show ?thesis
    proof
      assume a: "olt (maxo ?m ys) y"
      from yx show False
      proof
        assume "olt y x"
        hence "olt (maxo ?m ys) x" using a olt_trans by blast
        thus False using mx by blast
      next
        assume "y = x"
        thus False using a mx by simp
      qed
    qed
  qed
  from Cons.prems show ?case
  proof (elim insertE)
    assume "z = x" thus ?thesis using mx by simp
  next
    assume "z \<in> set (y # ys)"
    hence "z = y \<or> z \<in> set ys" by auto
    thus ?thesis
    proof
      assume "z = y" thus ?thesis using my by simp
    next
      assume "z \<in> set ys"
      hence "z \<in> insert ?m (set ys)" by simp
      thus ?thesis using ub by simp
    qed
  qed
qed

subsection \<open>End-position increase and the gap lemma\<close>

text \<open>\<open>einc\<close>: one leaf inserted at the \<^emph>\<open>lex-final\<close> position \<dash> along tails to the
  last summand, then (only when the tail is already \<open>Z\<close>) into its argument.
  \<open>eflip\<close>: the final leaf's subscript incremented.  These are the shapes
  actually produced by appending one column to a (standard) segment.  The gap
  lemma: nothing of size \<open>\<le> size x\<close> other than extensions separates \<open>x\<close> from its
  end-increase \<open>x'\<close>; hence (fire transport) any collapse witness of \<open>x\<close> remains
  one for \<open>x'\<close>.\<close>

inductive einc :: "three \<Rightarrow> three \<Rightarrow> bool" where
  einc_end:  "einc Z (P w Z Z)"
| einc_tail: "einc c c' \<Longrightarrow> einc (P a b c) (P a b c')"
| einc_argZ: "einc b b' \<Longrightarrow> einc (P a b Z) (P a b' Z)"

inductive eflip :: "three \<Rightarrow> three \<Rightarrow> bool" where
  eflip_leaf: "w < w' \<Longrightarrow> eflip (P w Z Z) (P w' Z Z)"
| eflip_tail: "eflip c c' \<Longrightarrow> eflip (P a b c) (P a b c')"
| eflip_argZ: "eflip b b' \<Longrightarrow> eflip (P a b Z) (P a b' Z)"

lemma einc_lext: "einc x y \<Longrightarrow> lext x y"
  by (induction rule: einc.induct) (auto intro: lext.intros)

lemma eflip_lflip: "eflip x y \<Longrightarrow> lflip x y"
  by (induction rule: eflip.induct) (auto intro: lflip.intros)

lemma einc_olt: "einc x y \<Longrightarrow> olt x y"
  using einc_lext lext_olt by blast

lemma eflip_olt: "eflip x y \<Longrightarrow> olt x y"
  using eflip_lflip lflip_olt by blast

lemma einc_gap:
  "einc x x' \<Longrightarrow> \<not> olt g x \<Longrightarrow> olt g x' \<Longrightarrow> size x \<le> size g"
proof (induction arbitrary: g rule: einc.induct)
  case (einc_end w)
  show ?case by simp
next
  case (einc_tail c c' a b)
  show ?case
  proof (cases g)
    case Z thus ?thesis using einc_tail.prems by simp
  next
    case (P e f h)
    have ne: "\<not> e < a" and nf: "\<not> (e = a \<and> olt f b)" and nh: "\<not> (e = a \<and> f = b \<and> olt h c)"
      using einc_tail.prems(1) P by auto
    have "e = a" "f = b" "olt h c'"
      using einc_tail.prems(2) P ne nf by auto
    hence "size c \<le> size h" using nh \<open>e = a\<close> einc_tail.IH by blast
    thus ?thesis using P \<open>f = b\<close> by simp
  qed
next
  case (einc_argZ b b' a)
  show ?case
  proof (cases g)
    case Z thus ?thesis using einc_argZ.prems by simp
  next
    case (P e f h)
    have ne: "\<not> e < a" and nf: "\<not> (e = a \<and> olt f b)"
      using einc_argZ.prems(1) P by auto
    have ea: "e = a" and fb': "olt f b'"
      using einc_argZ.prems(2) P ne not_olt_Z by auto
    have "size b \<le> size f" using nf ea fb' einc_argZ.IH by blast
    thus ?thesis using P by simp
  qed
qed

lemma eflip_gap:
  "eflip x x' \<Longrightarrow> \<not> olt g x \<Longrightarrow> olt g x' \<Longrightarrow> size x \<le> size g"
proof (induction arbitrary: g rule: eflip.induct)
  case (eflip_leaf w w')
  show ?case
  proof (cases g)
    case Z thus ?thesis using eflip_leaf.prems by simp
  next
    case (P e f h)
    show ?thesis using P by simp
  qed
next
  case (eflip_tail c c' a b)
  show ?case
  proof (cases g)
    case Z thus ?thesis using eflip_tail.prems by simp
  next
    case (P e f h)
    have ne: "\<not> e < a" and nf: "\<not> (e = a \<and> olt f b)" and nh: "\<not> (e = a \<and> f = b \<and> olt h c)"
      using eflip_tail.prems(1) P by auto
    have "e = a" "f = b" "olt h c'"
      using eflip_tail.prems(2) P ne nf by auto
    hence "size c \<le> size h" using nh \<open>e = a\<close> eflip_tail.IH by blast
    thus ?thesis using P \<open>f = b\<close> by simp
  qed
next
  case (eflip_argZ b b' a)
  show ?case
  proof (cases g)
    case Z thus ?thesis using eflip_argZ.prems by simp
  next
    case (P e f h)
    have ne: "\<not> e < a" and nf: "\<not> (e = a \<and> olt f b)"
      using eflip_argZ.prems(1) P by auto
    have ea: "e = a" and fb': "olt f b'"
      using eflip_argZ.prems(2) P ne not_olt_Z by auto
    have "size b \<le> size f" using nf ea fb' eflip_argZ.IH by blast
    thus ?thesis using P by simp
  qed
qed

text \<open>Fire transport: a collapse witness of \<open>x\<close> yields one for any end-increase
  of \<open>x\<close>.  (\<open>fire u b \<equiv> \<exists>g\<in>Gterm u b. \<not> olt g b\<close>.)\<close>

lemma fire_transport:
  assumes R: "einc x x' \<or> eflip x x'"
    and g: "g \<in> Gterm u x" and ng: "\<not> olt g x"
  shows "\<exists>g' \<in> Gterm u x'. \<not> olt g' x'"
proof -
  have szg: "size g < size x" by (rule Gterm_size[OF g])
  have ngx': "\<not> olt g x'"
  proof
    assume "olt g x'"
    hence "size x \<le> size g" using R ng einc_gap eflip_gap by blast
    thus False using szg by simp
  qed
  have lr: "lext x x' \<or> lflip x x'"
    using R einc_lext eflip_lflip by blast
  show ?thesis
  proof (cases "lext x x'")
    case True
    from Gterm_lext_sup[OF True, of u] g
    have "g \<in> Gterm u x' \<or> (\<exists>g' \<in> Gterm u x'. lext g g')" by blast
    thus ?thesis
    proof
      assume "g \<in> Gterm u x'" thus ?thesis using ngx' by blast
    next
      assume "\<exists>g' \<in> Gterm u x'. lext g g'"
      then obtain g' where g': "g' \<in> Gterm u x'" and lgg': "lext g g'" by blast
      have "\<not> olt g' x'"
      proof
        assume a: "olt g' x'"
        have "olt g g'" by (rule lext_olt[OF lgg'])
        hence "olt g x'" using a olt_trans by blast
        thus False using ngx' by blast
      qed
      thus ?thesis using g' by blast
    qed
  next
    case False
    hence lf: "lflip x x'" using lr by blast
    from Gterm_lflip_sup[OF lf, of u] g
    have "g \<in> Gterm u x' \<or> (\<exists>g' \<in> Gterm u x'. lflip g g')" by blast
    thus ?thesis
    proof
      assume "g \<in> Gterm u x'" thus ?thesis using ngx' by blast
    next
      assume "\<exists>g' \<in> Gterm u x'. lflip g g'"
      then obtain g' where g': "g' \<in> Gterm u x'" and lgg': "lflip g g'" by blast
      have "\<not> olt g' x'"
      proof
        assume a: "olt g' x'"
        have "olt g g'" by (rule lflip_olt[OF lgg'])
        hence "olt g x'" using a olt_trans by blast
        thus False using ngx' by blast
      qed
      thus ?thesis using g' by blast
    qed
  qed
qed

subsection \<open>Small computation lemmas\<close>

lemma proj_Z: "proj u Z = Z"
  by (rule proj_id) simp

lemma nrm_leaf: "nrm (P w Z Z) = P w Z Z"
  by (simp add: proj_Z)

lemma proj_leaf: "proj u (P w Z Z) = P w Z Z"
proof -
  have "filter (\<lambda>g. \<not> olt g (P w Z Z)) (Glist u (P w Z Z)) = []"
    by auto
  thus ?thesis by (rule proj_id)
qed

lemma Rinc_arg_cong: "Rinc b b' \<Longrightarrow> Rinc (P a b c) (P a b' c)"
  unfolding Rinc_def by (auto intro: lext.intros lflip.intros)

lemma Rinc_tail_cong: "Rinc c c' \<Longrightarrow> Rinc (P a b c) (P a b c')"
  unfolding Rinc_def by (auto intro: lext.intros lflip.intros)

subsection \<open>The snoc condition bundle and main induction\<close>

text \<open>\<open>snocok C q\<close>: the conditions along the recursive decomposition of \<open>C\<close>
  under which appending \<open>q\<close> changes the normalized image by one \<open>Rinc\<close> step.
  The no-absorb conditions in the tail branch are stated directly; deriving
  the whole bundle from standardness of \<open>C @ [q]\<close> is a separate (pending)
  obligation concentrating the class facts.\<close>

function snocok :: "pairseq \<Rightarrow> nat \<times> nat \<Rightarrow> bool" where
  "snocok [] q = False"
| "snocok (p # rest) q =
     (if dropWhile (\<lambda>r. fst p < fst r) rest = []
      then (fst p < fst q \<longrightarrow>
            olt (proj (snd p) (nrm (translate rest)))
                (proj (snd p) (nrm (translate (rest @ [q])))))
      else snocok (dropWhile (\<lambda>r. fst p < fst r) rest) q)"
  by pat_completeness auto
termination
  by (relation "measure (length \<circ> fst)")
     (auto simp: le_imp_less_Suc length_dropWhile_le)

lemma nrm_snoc_seg:
  "snocok C q \<Longrightarrow> C \<noteq> [] \<Longrightarrow> olt (nrm (translate C)) (nrm (translate (C @ [q])))"
proof (induct C q rule: snocok.induct)
  case (1 q) show ?case using 1 by simp
next
  case (2 p rest q)
  have sokA: "snocok (p # rest) q" by fact
  show ?case
  proof -
    let ?Pp = "\<lambda>r. fst p < fst r"
    let ?K = "takeWhile ?Pp rest"
    let ?T = "dropWhile ?Pp rest"
    let ?pb = "proj (snd p) (nrm (translate ?K))"
    have nC: "nrm (translate (p # rest)) = ins (snd p) ?pb (nrm (translate ?T))"
      by (simp only: translate.simps(2) nrm.simps(2))
    have appC: "(p # rest) @ [q] = p # (rest @ [q])" by simp
    show "olt (nrm (translate (p # rest))) (nrm (translate ((p # rest) @ [q])))"
    proof (cases "?T = []")
      case Tnil: True
      have allP: "\<forall>r \<in> set rest. ?Pp r" using Tnil by (simp add: dropWhile_eq_Nil_conv)
      have Kall: "?K = rest" using allP by (simp add: takeWhile_eq_all_conv)
      have nCs: "nrm (translate (p # rest)) = P (snd p) (proj (snd p) (nrm (translate rest))) Z"
        by (simp only: nC Tnil Kall translate.simps(1) nrm.simps(1) ins.simps(1))
      show ?thesis
      proof (cases "fst p < fst q")
        case qd: True   \<comment> \<open>(C) argument extension\<close>
        have tw': "takeWhile ?Pp (rest @ [q]) = rest @ [q]"
          using allP qd by (simp add: takeWhile_append)
        have dw': "dropWhile ?Pp (rest @ [q]) = []"
          using allP qd by (simp add: dropWhile_append)
        have e1: "translate ((p # rest) @ [q]) = P (snd p) (translate (rest @ [q])) Z"
          unfolding appC by (simp only: translate.simps(2) tw' dw' translate.simps(1))
        have nC': "nrm (translate ((p # rest) @ [q]))
                    = P (snd p) (proj (snd p) (nrm (translate (rest @ [q])))) Z"
          by (simp only: e1 nrm.simps ins.simps(1))
        have unfA: "snocok (p # rest) q \<longleftrightarrow>
              (fst p < fst q \<longrightarrow>
               olt (proj (snd p) (nrm (translate rest)))
                   (proj (snd p) (nrm (translate (rest @ [q])))))"
          by (simp only: snocok.simps if_P[OF Tnil])
        have PR: "olt (proj (snd p) (nrm (translate rest)))
                      (proj (snd p) (nrm (translate (rest @ [q]))))"
          using sokA qd unfolding unfA by blast
        show ?thesis unfolding nCs nC' by (rule olt_P_b[OF PR])
      next
        case qnd: False   \<comment> \<open>(A) new summand: \<open>ins\<close>-monotonicity, no conditions\<close>
        have tw': "takeWhile ?Pp (rest @ [q]) = rest"
          using allP qnd by (simp add: takeWhile_append)
        have dw': "dropWhile ?Pp (rest @ [q]) = [q]"
          using allP qnd by (simp add: dropWhile_append)
        have e1: "translate ((p # rest) @ [q]) = P (snd p) (translate rest) (translate [q])"
          unfolding appC by (simp only: translate.simps(2) tw' dw' Kall)
        have e2: "translate [q] = P (snd q) Z Z"
          by (simp only: translate.simps(2) takeWhile.simps(1) dropWhile.simps(1)
                         translate.simps(1))
        have nC': "nrm (translate ((p # rest) @ [q]))
                    = ins (snd p) (proj (snd p) (nrm (translate rest))) (P (snd q) Z Z)"
          by (simp only: e1 e2 nrm.simps proj_Z ins.simps(1) Kall)
        have nCz: "nrm (translate (p # rest))
                    = ins (snd p) (proj (snd p) (nrm (translate rest))) Z"
          by (simp only: nC Tnil Kall translate.simps(1) nrm.simps(1))
        have "olt (ins (snd p) (proj (snd p) (nrm (translate rest))) Z)
                  (ins (snd p) (proj (snd p) (nrm (translate rest))) (P (snd q) Z Z))"
          by (rule ins_olt_mono) simp
        thus ?thesis unfolding nCz nC' .
      qed
    next
      case Tne: False   \<comment> \<open>(B) tail extension: \<open>ins\<close>-monotonicity on the IH\<close>
      obtain w where win: "w \<in> set rest" and wnp: "\<not> ?Pp w"
        using Tne by (fastforce simp: dropWhile_eq_Nil_conv)
      have tw': "takeWhile ?Pp (rest @ [q]) = ?K"
        using win wnp by (simp add: takeWhile_append1)
      have dw': "dropWhile ?Pp (rest @ [q]) = ?T @ [q]"
        using win wnp by (simp add: dropWhile_append1)
      have nC': "nrm (translate ((p # rest) @ [q]))
                  = ins (snd p) ?pb (nrm (translate (?T @ [q])))"
        unfolding appC by (simp only: translate.simps(2) tw' dw' nrm.simps(2))
      have unfB: "snocok (p # rest) q \<longleftrightarrow> snocok ?T q"
        by (simp only: snocok.simps if_not_P[OF Tne])
      have sokT: "snocok ?T q"
        using sokA unfolding unfB .
      have IH: "olt (nrm (translate ?T)) (nrm (translate (?T @ [q])))"
        by (rule 2(1)[OF Tne sokT Tne])
      have "olt (ins (snd p) ?pb (nrm (translate ?T)))
                (ins (snd p) ?pb (nrm (translate (?T @ [q]))))"
        by (rule ins_olt_mono[OF IH])
      thus ?thesis unfolding nC nC' by simp
    qed
  qed
qed

text \<open>The sole remaining leaf obligation: at the argument-extension step against
  a standard host, the appended column strictly increases the projected
  argument.  By the suffix characterization of \<open>proj\<close> on standard segments
  (empirically: \<open>proj\<close> picks the suffix from the first maximal-row-1 column,
  and the appended column always lies in that suffix).\<close>

subsection \<open>Structural layer: \<open>einc \<union> eflip\<close> version of the snoc characterization\<close>

abbreviation Einc :: "three \<Rightarrow> three \<Rightarrow> bool" where
  "Einc x y \<equiv> einc x y \<or> eflip x y"

lemma Einc_olt: "Einc x y \<Longrightarrow> olt x y"
  using einc_olt eflip_olt by blast

function snocokS :: "pairseq \<Rightarrow> nat \<times> nat \<Rightarrow> bool" where
  "snocokS [] q = False"
| "snocokS (p # rest) q =
     (if dropWhile (\<lambda>r. fst p < fst r) rest = []
      then (if fst p < fst q
            then Einc (proj (snd p) (nrm (translate rest)))
                      (proj (snd p) (nrm (translate (rest @ [q]))))
            else snd q \<le> snd p)
      else snocokS (dropWhile (\<lambda>r. fst p < fst r) rest) q \<and>
           \<not> (snd p < hdsub (nrm (translate (dropWhile (\<lambda>r. fst p < fst r) rest)))
              \<or> (snd p = hdsub (nrm (translate (dropWhile (\<lambda>r. fst p < fst r) rest)))
                 \<and> olt (proj (snd p) (nrm (translate (takeWhile (\<lambda>r. fst p < fst r) rest))))
                       (hdarg (nrm (translate (dropWhile (\<lambda>r. fst p < fst r) rest)))))) \<and>
           \<not> (snd p < hdsub (nrm (translate (dropWhile (\<lambda>r. fst p < fst r) rest @ [q])))
              \<or> (snd p = hdsub (nrm (translate (dropWhile (\<lambda>r. fst p < fst r) rest @ [q])))
                 \<and> olt (proj (snd p) (nrm (translate (takeWhile (\<lambda>r. fst p < fst r) rest))))
                       (hdarg (nrm (translate (dropWhile (\<lambda>r. fst p < fst r) rest @ [q])))))))"
  by pat_completeness auto
termination
  by (relation "measure (length \<circ> fst)")
     (auto simp: le_imp_less_Suc length_dropWhile_le)

lemma nrm_snoc_str:
  "snocokS C q \<Longrightarrow> C \<noteq> [] \<Longrightarrow> Einc (nrm (translate C)) (nrm (translate (C @ [q])))"
proof (induct C q rule: snocokS.induct)
  case (1 q) show ?case using 1 by simp
next
  case (2 p rest q)
  have sokA: "snocokS (p # rest) q" by fact
  show ?case
  proof -
    let ?Pp = "\<lambda>r. fst p < fst r"
    let ?K = "takeWhile ?Pp rest"
    let ?T = "dropWhile ?Pp rest"
    let ?pb = "proj (snd p) (nrm (translate ?K))"
    have nC: "nrm (translate (p # rest)) = ins (snd p) ?pb (nrm (translate ?T))"
      by (simp only: translate.simps(2) nrm.simps(2))
    have appC: "(p # rest) @ [q] = p # (rest @ [q])" by simp
    show "Einc (nrm (translate (p # rest))) (nrm (translate ((p # rest) @ [q])))"
    proof (cases "?T = []")
      case Tnil: True
      have allP: "\<forall>r \<in> set rest. ?Pp r" using Tnil by (simp add: dropWhile_eq_Nil_conv)
      have Kall: "?K = rest" using allP by (simp add: takeWhile_eq_all_conv)
      have nCs: "nrm (translate (p # rest)) = P (snd p) (proj (snd p) (nrm (translate rest))) Z"
        by (simp only: nC Tnil Kall translate.simps(1) nrm.simps(1) ins.simps(1))
      show ?thesis
      proof (cases "fst p < fst q")
        case qd: True   \<comment> \<open>(C) argument extension\<close>
        have tw': "takeWhile ?Pp (rest @ [q]) = rest @ [q]"
          using allP qd by (simp add: takeWhile_append)
        have dw': "dropWhile ?Pp (rest @ [q]) = []"
          using allP qd by (simp add: dropWhile_append)
        have e1: "translate ((p # rest) @ [q]) = P (snd p) (translate (rest @ [q])) Z"
          unfolding appC by (simp only: translate.simps(2) tw' dw' translate.simps(1))
        have nC': "nrm (translate ((p # rest) @ [q]))
                    = P (snd p) (proj (snd p) (nrm (translate (rest @ [q])))) Z"
          by (simp only: e1 nrm.simps ins.simps(1))
        have unfA: "snocokS (p # rest) q \<longleftrightarrow>
              Einc (proj (snd p) (nrm (translate rest)))
                   (proj (snd p) (nrm (translate (rest @ [q]))))"
          by (simp only: snocokS.simps if_P[OF Tnil] if_P[OF qd])
        have PR: "Einc (proj (snd p) (nrm (translate rest)))
                       (proj (snd p) (nrm (translate (rest @ [q]))))"
          using sokA unfolding unfA .
        show ?thesis unfolding nCs nC'
          using PR einc.einc_argZ eflip.eflip_argZ by blast
      next
        case qnd: False   \<comment> \<open>(A) new summand\<close>
        have tw': "takeWhile ?Pp (rest @ [q]) = rest"
          using allP qnd by (simp add: takeWhile_append)
        have dw': "dropWhile ?Pp (rest @ [q]) = [q]"
          using allP qnd by (simp add: dropWhile_append)
        have e1: "translate ((p # rest) @ [q]) = P (snd p) (translate rest) (translate [q])"
          unfolding appC by (simp only: translate.simps(2) tw' dw' Kall)
        have e2: "translate [q] = P (snd q) Z Z"
          by (simp only: translate.simps(2) takeWhile.simps(1) dropWhile.simps(1)
                         translate.simps(1))
        have nC': "nrm (translate ((p # rest) @ [q]))
                    = ins (snd p) (proj (snd p) (nrm (translate rest))) (P (snd q) Z Z)"
          by (simp only: e1 e2 nrm.simps proj_Z ins.simps(1) Kall)
        have unfA: "snocokS (p # rest) q \<longleftrightarrow> snd q \<le> snd p"
          by (simp only: snocokS.simps if_P[OF Tnil] if_not_P[OF qnd])
        have yq: "snd q \<le> snd p" using sokA unfolding unfA .
        have noab: "ins (snd p) (proj (snd p) (nrm (translate rest))) (P (snd q) Z Z)
                     = P (snd p) (proj (snd p) (nrm (translate rest))) (P (snd q) Z Z)"
          by (rule ins_noabsorb) (use yq not_olt_Z in auto)
        have R: "nrm (translate ((p # rest) @ [q]))
                  = P (snd p) (proj (snd p) (nrm (translate rest))) (P (snd q) Z Z)"
          by (simp only: nC' noab)
        have G1: "einc (P (snd p) (proj (snd p) (nrm (translate rest))) Z)
                       (P (snd p) (proj (snd p) (nrm (translate rest))) (P (snd q) Z Z))"
          by (rule einc.einc_tail[OF einc.einc_end])
        show ?thesis unfolding nCs R using G1 by blast
      qed
    next
      case Tne: False   \<comment> \<open>(B) tail extension\<close>
      obtain w where win: "w \<in> set rest" and wnp: "\<not> ?Pp w"
        using Tne by (fastforce simp: dropWhile_eq_Nil_conv)
      have tw': "takeWhile ?Pp (rest @ [q]) = ?K"
        using win wnp by (simp add: takeWhile_append1)
      have dw': "dropWhile ?Pp (rest @ [q]) = ?T @ [q]"
        using win wnp by (simp add: dropWhile_append1)
      have nC': "nrm (translate ((p # rest) @ [q]))
                  = ins (snd p) ?pb (nrm (translate (?T @ [q])))"
        unfolding appC by (simp only: translate.simps(2) tw' dw' nrm.simps(2))
      have unfB: "snocokS (p # rest) q \<longleftrightarrow>
             (snocokS ?T q \<and>
              \<not> (snd p < hdsub (nrm (translate ?T))
                 \<or> (snd p = hdsub (nrm (translate ?T))
                    \<and> olt ?pb (hdarg (nrm (translate ?T))))) \<and>
              \<not> (snd p < hdsub (nrm (translate (?T @ [q])))
                 \<or> (snd p = hdsub (nrm (translate (?T @ [q])))
                    \<and> olt ?pb (hdarg (nrm (translate (?T @ [q])))))))"
        by (simp only: snocokS.simps if_not_P[OF Tne])
      have sokT: "snocokS ?T q" and na: "\<not> (snd p < hdsub (nrm (translate ?T))
                 \<or> (snd p = hdsub (nrm (translate ?T))
                    \<and> olt ?pb (hdarg (nrm (translate ?T)))))"
        and na': "\<not> (snd p < hdsub (nrm (translate (?T @ [q])))
                 \<or> (snd p = hdsub (nrm (translate (?T @ [q])))
                    \<and> olt ?pb (hdarg (nrm (translate (?T @ [q]))))))"
        using sokA unfolding unfB by blast+
      have IH: "Einc (nrm (translate ?T)) (nrm (translate (?T @ [q])))"
        by (rule 2(1)[OF Tne sokT Tne])
      have el: "ins (snd p) ?pb (nrm (translate ?T)) = P (snd p) ?pb (nrm (translate ?T))"
        by (rule ins_noabsorb) (use na in auto)
      have er: "ins (snd p) ?pb (nrm (translate (?T @ [q])))
                 = P (snd p) ?pb (nrm (translate (?T @ [q])))"
        by (rule ins_noabsorb) (use na' in auto)
      have "Einc (P (snd p) ?pb (nrm (translate ?T)))
                 (P (snd p) ?pb (nrm (translate (?T @ [q]))))"
        using IH einc.einc_tail eflip.eflip_tail by blast
      thus ?thesis unfolding nC nC' el er by simp
    qed
  qed
qed

abbreviation pfire :: "nat \<Rightarrow> three \<Rightarrow> bool" where
  "pfire u b \<equiv> (\<exists>g \<in> Gterm u b. \<not> olt g b)"

lemma pfire_filter: "pfire u b \<longleftrightarrow> filter (\<lambda>g. \<not> olt g b) (Glist u b) \<noteq> []"
  using set_Glist by (auto simp: filter_empty_conv)

lemma proj_nofire: "\<not> pfire u b \<Longrightarrow> proj u b = b"
  using pfire_filter proj_id by blast

subsection \<open>\<open>proj\<close> terminates in one step\<close>

text \<open>Criticals of criticals are criticals; hence the maximal violating critical
  is itself collapse-free (a violator inside it would be a strictly larger
  violator of the original term, contradicting maximality by size).  So the
  projection loop always stops after a single step.\<close>

lemma Gterm_trans: "g \<in> Gterm u t \<Longrightarrow> h \<in> Gterm u g \<Longrightarrow> h \<in> Gterm u t"
proof (induction t arbitrary: g)
  case (P a b c)
  from P.prems(1) consider "u \<le> a" "g = b" | "u \<le> a" "g \<in> Gterm u b" | "g \<in> Gterm u c"
    by (auto split: if_splits)
  thus ?case
  proof cases
    case 1 thus ?thesis using P.prems(2) by auto
  next
    case 2 thus ?thesis using P.IH(1) P.prems(2) by auto
  next
    case 3 thus ?thesis using P.IH(2) P.prems(2) by auto
  qed
qed simp

lemma maxg_nofire:
  assumes ne: "filter (\<lambda>g. \<not> olt g b) (Glist u b) \<noteq> []"
  shows "\<not> pfire u (maxo (hd (filter (\<lambda>g. \<not> olt g b) (Glist u b)))
                         (tl (filter (\<lambda>g. \<not> olt g b) (Glist u b))))"
proof
  let ?gs = "filter (\<lambda>g. \<not> olt g b) (Glist u b)"
  let ?m = "maxo (hd ?gs) (tl ?gs)"
  have mset: "?m \<in> set ?gs" by (rule maxo_hdtl_in[OF ne])
  have mG: "?m \<in> Gterm u b" using mset set_Glist by auto
  have mnb: "\<not> olt ?m b" using mset by auto
  assume "pfire u ?m"
  then obtain g where gG: "g \<in> Gterm u ?m" and gnm: "\<not> olt g ?m" by blast
  have gB: "g \<in> Gterm u b" by (rule Gterm_trans[OF mG gG])
  have gsz: "size g < size ?m" by (rule Gterm_size[OF gG])
  have "\<not> olt g b"
  proof
    assume "olt g b"
    have "ole b ?m" using mnb olt_total by blast
    hence "olt g ?m" using \<open>olt g b\<close> \<open>ole b ?m\<close> olt_ole_trans by blast
    thus False using gnm by blast
  qed
  hence "g \<in> set ?gs" using gB set_Glist by auto
  hence inseq: "g \<in> insert (hd ?gs) (set (tl ?gs))" by (cases ?gs) auto
  have "\<not> olt ?m g" using maxo_ub[OF inseq] .
  hence "g = ?m" using gnm olt_total by blast
  thus False using gsz by simp
qed

lemma proj_once:
  "proj u b = (if filter (\<lambda>g. \<not> olt g b) (Glist u b) = [] then b
               else maxo (hd (filter (\<lambda>g. \<not> olt g b) (Glist u b)))
                         (tl (filter (\<lambda>g. \<not> olt g b) (Glist u b))))"
proof (cases "filter (\<lambda>g. \<not> olt g b) (Glist u b) = []")
  case True thus ?thesis using proj_id by simp
next
  case False
  let ?m = "maxo (hd (filter (\<lambda>g. \<not> olt g b) (Glist u b)))
                 (tl (filter (\<lambda>g. \<not> olt g b) (Glist u b)))"
  have "proj u b = proj u ?m" using proj_rec[OF False] by simp
  also have "proj u ?m = ?m"
    using maxg_nofire[OF False] proj_nofire by blast
  finally show ?thesis using False by simp
qed

text \<open>Prefix monotonicity of the projection: if every critical of \<open>x\<close> is a
  critical of \<open>y\<close> and \<open>x \<le>\<^sub>o y\<close>, the projections stay ordered \<dash> purely from
  maximality.  (The intended instance: \<open>x\<close> a summand-prefix of \<open>y\<close>.)\<close>

lemma proj_submono:
  assumes sub: "Gterm u x \<subseteq> Gterm u y" and xy: "ole x y" and yny: "\<not> pfire u y \<Longrightarrow> \<not> pfire u x"
  shows "ole (proj u x) (proj u y)"
proof (cases "pfire u x")
  case False
  have pxx: "proj u x = x" by (rule proj_nofire[OF False])
  have yp: "ole y (proj u y)" using proj_ole[of y u] by simp
  have "ole x (proj u y)"
  proof (cases "x = y")
    case True thus ?thesis using yp by simp
  next
    case False
    hence lxy: "olt x y" using xy by simp
    show ?thesis using olt_ole_trans[OF lxy] yp by (cases "y = proj u y") auto
  qed
  thus ?thesis unfolding pxx .
next
  case xf: True
  have yf: "pfire u y"
    using xf yny by blast
  let ?gx = "filter (\<lambda>g. \<not> olt g x) (Glist u x)"
  let ?gy = "filter (\<lambda>g. \<not> olt g y) (Glist u y)"
  have nex: "?gx \<noteq> []" using xf pfire_filter by blast
  have ney: "?gy \<noteq> []" using yf pfire_filter by blast
  let ?mx = "maxo (hd ?gx) (tl ?gx)"
  let ?my = "maxo (hd ?gy) (tl ?gy)"
  have px: "proj u x = ?mx" using proj_once[of u x] nex by simp
  have py: "proj u y = ?my" using proj_once[of u y] ney by simp
  have mxx: "?mx \<in> set ?gx" by (rule maxo_hdtl_in[OF nex])
  have mxG: "?mx \<in> Gterm u y" using mxx set_Glist sub by auto
  have mxnx: "\<not> olt ?mx x" using mxx by auto
  have "\<not> olt ?mx y \<or> olt ?mx y" by blast
  have mxny: "\<not> olt ?mx y \<Longrightarrow> ?mx \<in> set ?gy"
    using mxG set_Glist by auto
  show ?thesis
  proof (cases "olt ?mx y")
    case True
    \<comment> \<open>\<open>?mx\<close> is not a violator of \<open>y\<close>; but \<open>?my \<ge>\<^sub>o y >\<^sub>o ?mx\<close> via inflation\<close>
    have "ole y ?my"
    proof -
      have "?my \<in> set ?gy" by (rule maxo_hdtl_in[OF ney])
      hence "\<not> olt ?my y" by auto
      thus ?thesis using olt_total by blast
    qed
    hence "olt ?mx ?my" using True olt_ole_trans by blast
    thus ?thesis unfolding px py by blast
  next
    case False
    have inseq: "?mx \<in> insert (hd ?gy) (set (tl ?gy))"
      using mxny[OF False] by (cases ?gy) auto
    have "\<not> olt ?my ?mx" using maxo_ub[OF inseq] .
    hence "ole ?mx ?my" using olt_total by blast
    thus ?thesis unfolding px py .
  qed
qed

subsection \<open>The max-row1 suffix\<close>

text \<open>The E6 projection theorem (empirically exact on all hereditary standard
  dominated segments, 15302 positions): when the projection fires at the host
  level, its value is the normalized image of the suffix of the segment
  starting at the \<^emph>\<open>first\<close> column of maximal row-1 value.\<close>

definition maxr1 :: "pairseq \<Rightarrow> nat" where
  "maxr1 S = Max (snd ` set S)"

definition msfx :: "pairseq \<Rightarrow> pairseq" where
  "msfx S = dropWhile (\<lambda>c. snd c < maxr1 S) S"

lemma maxr1_in: "S \<noteq> [] \<Longrightarrow> maxr1 S \<in> snd ` set S"
  unfolding maxr1_def by (intro Max_in) auto

lemma maxr1_ub: "c \<in> set S \<Longrightarrow> snd c \<le> maxr1 S"
  unfolding maxr1_def by (intro Max_ge) auto

lemma msfx_ne: "S \<noteq> [] \<Longrightarrow> msfx S \<noteq> []"
proof
  assume S: "S \<noteq> []" and m: "msfx S = []"
  have "\<forall>c \<in> set S. snd c < maxr1 S"
    using m unfolding msfx_def by (simp add: dropWhile_eq_Nil_conv)
  thus False using maxr1_in[OF S] by auto
qed

lemma msfx_hd: "S \<noteq> [] \<Longrightarrow> snd (hd (msfx S)) = maxr1 S"
proof -
  assume S: "S \<noteq> []"
  have ne: "dropWhile (\<lambda>c. snd c < maxr1 S) S \<noteq> []"
    using msfx_ne[OF S] unfolding msfx_def .
  have "\<not> snd (hd (msfx S)) < maxr1 S"
    using hd_dropWhile[OF ne] unfolding msfx_def .
  moreover have "hd (msfx S) \<in> set S"
    using ne hd_in_set set_dropWhileD unfolding msfx_def by fast
  ultimately show ?thesis using maxr1_ub by fastforce
qed

lemma msfx_decomp: "S = takeWhile (\<lambda>c. snd c < maxr1 S) S @ msfx S"
  unfolding msfx_def by simp

lemma msfx_set: "set (msfx S) \<subseteq> set S"
  unfolding msfx_def using set_dropWhileD by fast

lemma maxr1_append_le:
  assumes S: "S \<noteq> []" and q: "snd q \<le> maxr1 S"
  shows "maxr1 (S @ [q]) = maxr1 S"
proof -
  have ins: "snd ` set (S @ [q]) = insert (snd q) (snd ` set S)" by auto
  have "Max (insert (snd q) (snd ` set S)) = max (snd q) (Max (snd ` set S))"
    by (intro Max_insert) (use S in auto)
  also have "\<dots> = Max (snd ` set S)"
    using q unfolding maxr1_def by (simp add: max_absorb2)
  finally show ?thesis unfolding maxr1_def ins .
qed

lemma msfx_append_le:
  assumes S: "S \<noteq> []" and q: "snd q \<le> maxr1 S"
  shows "msfx (S @ [q]) = msfx S @ [q]"
proof -
  obtain c where c: "c \<in> set S" "snd c = maxr1 S"
    using maxr1_in[OF S] by auto
  have "dropWhile (\<lambda>r. snd r < maxr1 S) (S @ [q]) =
        dropWhile (\<lambda>r. snd r < maxr1 S) S @ [q]"
    using c by (intro dropWhile_append1) auto
  thus ?thesis unfolding msfx_def maxr1_append_le[OF S q] .
qed

lemma maxr1_append_gt:
  assumes q: "maxr1 S < snd q"
  shows "maxr1 (S @ [q]) = snd q"
proof (cases "S = []")
  case True thus ?thesis unfolding maxr1_def by simp
next
  case False
  have ins: "snd ` set (S @ [q]) = insert (snd q) (snd ` set S)" by auto
  have "Max (insert (snd q) (snd ` set S)) = max (snd q) (Max (snd ` set S))"
    by (intro Max_insert) (use False in auto)
  also have "\<dots> = snd q"
    using q unfolding maxr1_def by (simp add: max_absorb1)
  finally show ?thesis unfolding maxr1_def ins .
qed

lemma msfx_append_gt:
  assumes q: "maxr1 S < snd q"
  shows "msfx (S @ [q]) = [q]"
proof -
  have all: "\<And>c. c \<in> set S \<Longrightarrow> snd c < snd q"
    using maxr1_ub q by fastforce
  have "dropWhile (\<lambda>r. snd r < snd q) (S @ [q]) = dropWhile (\<lambda>r. snd r < snd q) [q]"
    by (intro dropWhile_append2) (use all in auto)
  thus ?thesis unfolding msfx_def maxr1_append_gt[OF q] by simp
qed

lemma NT_single: "nrm (translate [c]) = P (snd c) Z Z"
  by (cases c) (simp add: proj_Z)

lemma maxr1_tail:
  assumes Y: "Y \<noteq> []" and X: "\<forall>c \<in> set X. snd c < maxr1 Y"
  shows "maxr1 (X @ Y) = maxr1 Y"
proof (cases "X = []")
  case True thus ?thesis by simp
next
  case False
  have su: "snd ` set (X @ Y) = snd ` set X \<union> snd ` set Y" by auto
  have mu: "Max (snd ` set X \<union> snd ` set Y) = max (Max (snd ` set X)) (Max (snd ` set Y))"
    by (intro Max_Un) (use False Y in auto)
  have "Max (snd ` set X) \<in> snd ` set X" by (intro Max_in) (use False in auto)
  hence "Max (snd ` set X) < maxr1 Y" using X by auto
  hence "Max (snd ` set X) \<le> Max (snd ` set Y)" unfolding maxr1_def by simp
  thus ?thesis unfolding maxr1_def su mu by (simp add: max_absorb2)
qed

lemma msfx_tail:
  assumes Y: "Y \<noteq> []" and X: "\<forall>c \<in> set X. snd c < maxr1 Y"
  shows "msfx (X @ Y) = msfx Y"
proof -
  have m: "maxr1 (X @ Y) = maxr1 Y" by (rule maxr1_tail[OF Y X])
  have "dropWhile (\<lambda>c. snd c < maxr1 Y) (X @ Y) = dropWhile (\<lambda>c. snd c < maxr1 Y) Y"
    using X by (intro dropWhile_append2) auto
  thus ?thesis unfolding msfx_def m .
qed

text \<open>Under fire the projection moves strictly (to a critical, hence smaller
  in size).\<close>

lemma proj_fire_ne:
  assumes f: "pfire u b"
  shows "proj u b \<noteq> b"
proof -
  let ?gs = "filter (\<lambda>g. \<not> olt g b) (Glist u b)"
  have ne: "?gs \<noteq> []" using f pfire_filter by blast
  have "proj u b = maxo (hd ?gs) (tl ?gs)" using proj_once[of u b] ne by simp
  moreover have "maxo (hd ?gs) (tl ?gs) \<in> set ?gs" by (rule maxo_hdtl_in[OF ne])
  ultimately have "proj u b \<in> Gterm u b" using set_Glist by auto
  thus ?thesis using Gterm_size by fastforce
qed

subsection \<open>Subscript bookkeeping: the head of the suffix image is the max row-1\<close>

lemma Gterm_subs: "g \<in> Gterm u t \<Longrightarrow> subs g \<subseteq> subs t"
proof (induction t arbitrary: g)
  case (P a b c)
  from P.prems consider "u \<le> a" "g = b" | "u \<le> a" "g \<in> Gterm u b" | "g \<in> Gterm u c"
    by (auto split: if_splits)
  thus ?case
  proof cases
    case 1 thus ?thesis by auto
  next
    case 2 thus ?thesis using P.IH(1) by auto
  next
    case 3 thus ?thesis using P.IH(2) by auto
  qed
qed simp

lemma proj_subs: "subs (proj u b) \<subseteq> subs b"
proof (cases "filter (\<lambda>g. \<not> olt g b) (Glist u b) = []")
  case True thus ?thesis using proj_once[of u b] by simp
next
  case False
  let ?gs = "filter (\<lambda>g. \<not> olt g b) (Glist u b)"
  have "proj u b = maxo (hd ?gs) (tl ?gs)" using proj_once[of u b] False by simp
  moreover have "maxo (hd ?gs) (tl ?gs) \<in> set ?gs" by (rule maxo_hdtl_in[OF False])
  ultimately have "proj u b \<in> Gterm u b" using set_Glist by auto
  thus ?thesis by (rule Gterm_subs)
qed

lemma ins_subs: "subs (ins a b t) \<subseteq> insert a (subs b \<union> subs t)"
  by (cases t) auto

lemma nrm_subs: "subs (nrm w) \<subseteq> subs w"
proof (induction w)
  case (P a b c)
  have "subs (nrm (P a b c)) \<subseteq> insert a (subs (proj a (nrm b)) \<union> subs (nrm c))"
    using ins_subs by simp
  also have "\<dots> \<subseteq> insert a (subs (nrm b) \<union> subs (nrm c))"
    using proj_subs by fastforce
  also have "\<dots> \<subseteq> insert a (subs b \<union> subs c)"
    using P.IH by fastforce
  finally show ?case by simp
qed simp

lemma NT_subs: "subs (nrm (translate M)) \<subseteq> snd ` set M"
  using nrm_subs subs_translate by fast

lemma ins_neZ: "ins a b t \<noteq> Z"
  by (cases t) auto

lemma ins_hdsub: "a \<le> hdsub (ins a b t)"
  by (cases t) auto

lemma NT_neZ: "nrm (translate (c # rest)) \<noteq> Z"
proof -
  have "nrm (translate (c # rest))
        = ins (snd c) (proj (snd c) (nrm (translate (takeWhile (\<lambda>r. fst c < fst r) rest))))
                      (nrm (translate (dropWhile (\<lambda>r. fst c < fst r) rest)))"
    by (simp only: translate.simps(2) nrm.simps(2))
  thus ?thesis using ins_neZ by simp
qed

lemma NT_hd_ge: "snd c \<le> hdsub (nrm (translate (c # rest)))"
proof -
  have "nrm (translate (c # rest))
        = ins (snd c) (proj (snd c) (nrm (translate (takeWhile (\<lambda>r. fst c < fst r) rest))))
                      (nrm (translate (dropWhile (\<lambda>r. fst c < fst r) rest)))"
    by (simp only: translate.simps(2) nrm.simps(2))
  thus ?thesis using ins_hdsub by simp
qed

text \<open>Purely, with no class premise: the head subscript of the normalized
  image of the max-row1 suffix is exactly the maximal row-1 value.\<close>

lemma NT_msfx_hdsub:
  assumes S: "S \<noteq> []"
  shows "hdsub (nrm (translate (msfx S))) = maxr1 S"
proof -
  obtain c' rest' where M: "msfx S = c' # rest'"
    using msfx_ne[OF S] by (cases "msfx S") auto
  have hd': "snd c' = maxr1 S" using msfx_hd[OF S] unfolding M by simp
  have ge: "maxr1 S \<le> hdsub (nrm (translate (msfx S)))"
    unfolding M using NT_hd_ge hd' by metis
  obtain e f g where E: "nrm (translate (msfx S)) = P e f g"
    using NT_neZ unfolding M by (cases "nrm (translate (c' # rest'))") auto
  have "e \<in> subs (nrm (translate (msfx S)))" unfolding E by simp
  hence "e \<in> snd ` set (msfx S)" using NT_subs by fast
  hence "e \<in> snd ` set S" using msfx_set by fast
  hence "e \<le> maxr1 S" using maxr1_ub by fast
  thus ?thesis using ge unfolding E by simp
qed

text \<open>Hence two purely subscript-theoretic dominance facts: every critical of
  a normalized image has head subscript at most the segment's max row-1, and
  anything with head subscript strictly below it is \<open>olt\<close>-below the suffix
  image.\<close>

lemma Gterm_NT_hdsub_le:
  assumes "g \<in> Gterm u (nrm (translate S))" and "g \<noteq> Z"
  shows "hdsub g \<le> maxr1 S"
proof -
  obtain e f r where E: "g = P e f r" using assms(2) by (cases g) auto
  have "e \<in> subs g" unfolding E by simp
  hence "e \<in> subs (nrm (translate S))" using Gterm_subs assms(1) by fast
  hence "e \<in> snd ` set S" using NT_subs by fast
  hence "e \<le> maxr1 S" using maxr1_ub by fast
  thus ?thesis unfolding E by simp
qed

lemma olt_msfx_lowsub:
  assumes S: "S \<noteq> []" and g: "g = Z \<or> hdsub g < maxr1 S"
  shows "olt g (nrm (translate (msfx S)))"
proof -
  obtain c' rest' where M: "msfx S = c' # rest'"
    using msfx_ne[OF S] by (cases "msfx S") auto
  obtain f' g' where E: "nrm (translate (msfx S)) = P (maxr1 S) f' g'"
    using NT_neZ NT_msfx_hdsub[OF S] unfolding M
    by (cases "nrm (translate (c' # rest'))") auto
  show ?thesis
  proof (cases g)
    case Z thus ?thesis unfolding E by simp
  next
    case (P e f r)
    have "e < maxr1 S" using g unfolding P by simp
    thus ?thesis unfolding P E by simp
  qed
qed

subsection \<open>Transport of \<open>Einc\<close> through \<open>proj\<close>\<close>

text \<open>Provenance: the pair under transport is the normalized image of an
  all-dominated standard sub-segment and its one-column extension; \<open>u\<close> is the
  enclosing head's row-1 value.  (The transport cases are false for arbitrary
  \<open>Einc\<close> pairs \<dash> e.g.\ a leaf inserted into a region discarded by the
  projection; provenance is what excludes those.)\<close>

definition segprov :: "nat \<Rightarrow> pairseq \<Rightarrow> nat \<times> nat \<Rightarrow> bool" where
  "segprov u S q \<longleftrightarrow> (\<exists>pre pp post. pre @ (pp # S) @ [q] @ post \<in> ST_PS
                       \<and> (\<forall>r \<in> set S. fst pp < fst r) \<and> fst pp < fst q \<and> u = snd pp)"

text \<open>The dominated-segment class and its E6 facts (empirically exact;
  validation suite \<open>tools/mine_master.py\<close>, V1--V5 all zero, plus the seam
  invariants \<open>tools/mine_seam.py\<close>, 1128/1128).\<close>

definition dseg :: "nat \<Rightarrow> pairseq \<Rightarrow> bool" where
  "dseg u S \<longleftrightarrow> S \<noteq> [] \<and> (\<exists>pre pp post. pre @ (pp # S) @ post \<in> ST_PS
                 \<and> (\<forall>r \<in> set S. fst pp < fst r) \<and> u = snd pp)"

lemma segprov_dseg: "segprov u S q \<Longrightarrow> S \<noteq> [] \<Longrightarrow> dseg u S"
  unfolding segprov_def dseg_def by blast

lemma segprov_dsegq:
  assumes "segprov u S q" shows "dseg u (S @ [q])"
proof -
  from assms obtain pre pp post where h: "pre @ (pp # S) @ [q] @ post \<in> ST_PS"
      and dom: "\<forall>r \<in> set S. fst pp < fst r" and dq: "fst pp < fst q" and u: "u = snd pp"
    unfolding segprov_def by blast
  have "pre @ (pp # (S @ [q])) @ post \<in> ST_PS" using h by simp
  moreover have "\<forall>r \<in> set (S @ [q]). fst pp < fst r" using dom dq by auto
  ultimately show ?thesis unfolding dseg_def using u by blast
qed

text \<open>Forest-boundary pieces: contiguous sublists of a dominated run whose
  skipped prefix \<open>mid\<close> lies entirely at levels \<open>\<ge>\<close> the piece head's level.
  This is the closure of the adjacent class under the two descents of the
  \<open>translate\<close> recursion (empirically C1-clean: \<open>tools/mine_master2.py\<close>).\<close>

definition stepsok :: "pairseq \<Rightarrow> bool" where
  "stepsok C \<longleftrightarrow> (\<forall>j. Suc j < length C \<longrightarrow> fst (C ! Suc j) \<le> Suc (fst (C ! j)))"

lemma blockok_stepsok: "blockok d M \<Longrightarrow> stepsok M"
  unfolding blockok_def stepsok_def by blast

lemma stepsok_sub: "stepsok (u @ C @ v) \<Longrightarrow> stepsok C"
proof -
  assume H: "stepsok (u @ C @ v)"
  show "stepsok C"
    unfolding stepsok_def
  proof (intro allI impI)
    fix j assume j: "Suc j < length C"
    have e1: "(u @ C @ v) ! (length u + j) = C ! j"
      using j by (simp add: nth_append)
    have e2: "(u @ C @ v) ! (length u + Suc j) = C ! Suc j"
      using j by (simp add: nth_append)
    have "Suc (length u + j) < length (u @ C @ v)" using j by simp
    hence "fst ((u @ C @ v) ! Suc (length u + j)) \<le> Suc (fst ((u @ C @ v) ! (length u + j)))"
      using H unfolding stepsok_def by blast
    thus "fst (C ! Suc j) \<le> Suc (fst (C ! j))" using e1 e2 by simp
  qed
qed

subsection \<open>Row-1 discipline of standard sequences\<close>

text \<open>\<open>r1ok\<close>: every column at positive level has a row-0 parent (the nearest
  preceding column one level below, with no dip in between) whose row-1 value
  it exceeds by at most one.  (Empirically exact on all standard hosts,
  14558 columns, difference distribution \<open>-3..+1\<close>.)\<close>

definition r1ok :: "pairseq \<Rightarrow> bool" where
  "r1ok M \<longleftrightarrow> (\<forall>j. j < length M \<longrightarrow> 0 < fst (M ! j) \<longrightarrow>
     (\<exists>k. k < j \<and> Suc (fst (M ! k)) = fst (M ! j)
        \<and> (\<forall>l. k < l \<and> l < j \<longrightarrow> fst (M ! j) \<le> fst (M ! l))
        \<and> snd (M ! j) \<le> Suc (snd (M ! k))))"

lemma r1ok_diagSeq: "r1ok (diagSeq 0 v)"
proof -
  have len: "length (diagSeq 0 v) = Suc v"
    unfolding diagSeq_def by simp
  have nth: "\<And>j. j < Suc v \<Longrightarrow> diagSeq 0 v ! j = (j, j)"
    unfolding diagSeq_def by (simp del: upt_Suc)
  show ?thesis
    unfolding r1ok_def
  proof (intro allI impI)
    fix j assume jl: "j < length (diagSeq 0 v)"
      and jp: "0 < fst (diagSeq 0 v ! j)"
    have jv: "j < Suc v" using jl len by simp
    have fj: "fst (diagSeq 0 v ! j) = j" using nth[OF jv] by simp
    have j0: "0 < j" using jp fj by simp
    have kv: "j - 1 < Suc v" using jv by simp
    show "\<exists>k. k < j \<and> Suc (fst (diagSeq 0 v ! k)) = fst (diagSeq 0 v ! j)
        \<and> (\<forall>l. k < l \<and> l < j \<longrightarrow> fst (diagSeq 0 v ! j) \<le> fst (diagSeq 0 v ! l))
        \<and> snd (diagSeq 0 v ! j) \<le> Suc (snd (diagSeq 0 v ! k))"
    proof (intro exI[of _ "j - 1"] conjI)
      show "j - 1 < j" using j0 by simp
      show "Suc (fst (diagSeq 0 v ! (j - 1))) = fst (diagSeq 0 v ! j)"
        using nth[OF kv] fj j0 by simp
      show "\<forall>l. j - 1 < l \<and> l < j \<longrightarrow> fst (diagSeq 0 v ! j) \<le> fst (diagSeq 0 v ! l)"
        by auto
      show "snd (diagSeq 0 v ! j) \<le> Suc (snd (diagSeq 0 v ! (j - 1)))"
        using nth[OF jv] nth[OF kv] j0 by simp
    qed
  qed
qed

lemma r1ok_take: "r1ok M \<Longrightarrow> r1ok (take m M)"
proof -
  assume A: "r1ok M"
  show ?thesis
    unfolding r1ok_def
  proof (intro allI impI)
    fix j assume jl: "j < length (take m M)" and jp: "0 < fst (take m M ! j)"
    have jm: "j < m" and jM: "j < length M" using jl by auto
    have nj: "take m M ! j = M ! j" using jm by simp
    from A jM jp obtain k where k: "k < j" "Suc (fst (M ! k)) = fst (M ! j)"
      "\<forall>l. k < l \<and> l < j \<longrightarrow> fst (M ! j) \<le> fst (M ! l)"
      "snd (M ! j) \<le> Suc (snd (M ! k))"
      unfolding r1ok_def nj by blast
    have nk: "take m M ! k = M ! k" using k(1) jm by simp
    have nl: "\<And>l. k < l \<and> l < j \<Longrightarrow> take m M ! l = M ! l" using jm by simp
    show "\<exists>k. k < j \<and> Suc (fst (take m M ! k)) = fst (take m M ! j)
        \<and> (\<forall>l. k < l \<and> l < j \<longrightarrow> fst (take m M ! j) \<le> fst (take m M ! l))
        \<and> snd (take m M ! j) \<le> Suc (snd (take m M ! k))"
      using k nj nk nl by (intro exI[of _ k]) auto
  qed
qed

lemma r1ok_butlast: "r1ok M \<Longrightarrow> r1ok (butlast M)"
  using r1ok_take[of M "length M - 1"] by (simp add: butlast_conv_take)

text \<open>The copy index is at most 1, so the row-1 delta is always zero: copies
  replicate row-1 values exactly.\<close>

lemma idx1_le: "idx1 M j \<le> 1"
  unfolding idx1_def by simp

lemma concat_map_upt_length:
  assumes "\<And>k. k < n \<Longrightarrow> length (F k) = L"
  shows "length (concat (map F [0..<n])) = n * L"
  using assms
proof (induct n)
  case 0 show ?case by simp
next
  case (Suc n)
  have "length (concat (map F [0..<Suc n]))
        = length (concat (map F [0..<n])) + length (F n)" by simp
  also have "\<dots> = n * L + L" using Suc by simp
  finally show ?case by simp
qed

lemma concat_map_upt_nth:
  assumes len: "\<And>k. k < n \<Longrightarrow> length (F k) = L"
    and k: "k < n" and q: "q < L"
  shows "concat (map F [0..<n]) ! (k * L + q) = F k ! q"
  using len k
proof (induct n)
  case 0 thus ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "k < n")
    case True
    have ll: "length (concat (map F [0..<n])) = n * L"
      by (rule concat_map_upt_length) (use Suc.prems(1) in simp)
    have il: "k * L + q < n * L"
    proof -
      have "k * L + q < k * L + L" using q by simp
      also have "\<dots> = Suc k * L" by simp
      also have "\<dots> \<le> n * L" using True by (intro mult_le_mono1) simp
      finally show ?thesis .
    qed
    have "concat (map F [0..<Suc n]) = concat (map F [0..<n]) @ F n" by simp
    hence "concat (map F [0..<Suc n]) ! (k * L + q) = concat (map F [0..<n]) ! (k * L + q)"
      using il ll by (simp add: nth_append)
    thus ?thesis using Suc True by simp
  next
    case False
    hence kn: "k = n" using Suc.prems(2) by simp
    have ll: "length (concat (map F [0..<n])) = n * L"
      by (rule concat_map_upt_length) (use Suc.prems(1) in simp)
    have "concat (map F [0..<Suc n]) = concat (map F [0..<n]) @ F n" by simp
    hence "concat (map F [0..<Suc n]) ! (n * L + q) = F n ! q"
      using ll by (simp add: nth_append)
    thus ?thesis using kn by simp
  qed
qed

lemma oper_bad_len:
  assumes opeqX: "X = take j0 M @ concat (map (\<lambda>k.
           map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j)) [j0..<j1]) [0..<n])"
    and j0j1X: "j0 < j1" and j1lenX: "j1 < length M"
  shows "length X = j0 + n * (j1 - j0)"
proof -
  have "length (concat (map (\<lambda>k. map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j)) [j0..<j1]) [0..<n]))
        = n * (j1 - j0)"
    by (rule concat_map_upt_length) simp
  moreover have "length (take j0 M) = j0" using j0j1X j1lenX by simp
  ultimately show ?thesis unfolding opeqX by simp
qed

lemma oper_bad_nth_pre:
  assumes opeqX: "X = take j0 M @ concat (map (\<lambda>k.
           map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j)) [j0..<j1]) [0..<n])"
    and "i < j0" and "j1 < length M" and "j0 < j1"
  shows "X ! i = M ! i"
  unfolding opeqX using assms(2-4) by (simp add: nth_append)

lemma oper_bad_nth_copy:
  assumes opeqX: "X = take j0 M @ concat (map (\<lambda>k.
           map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j)) [j0..<j1]) [0..<n])"
    and j0j1X: "j0 < j1" and j1lenX: "j1 < length M"
    and k: "k < n" and q: "q < j1 - j0"
  shows "X ! (j0 + (k * (j1 - j0) + q)) = (entry M 0 (j0 + q) + k * d0, entry M 1 (j0 + q))"
proof -
  have c: "concat (map (\<lambda>k. map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j)) [j0..<j1]) [0..<n])
           ! (k * (j1 - j0) + q)
           = map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j)) [j0..<j1] ! q"
    by (rule concat_map_upt_nth[OF _ k q]) simp
  have m: "map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j)) [j0..<j1] ! q
           = (entry M 0 (j0 + q) + k * d0, entry M 1 (j0 + q))"
    using q by simp
  have lt: "length (take j0 M) = j0" using j0j1X j1lenX by simp
  show ?thesis unfolding opeqX using c m lt by (simp add: nth_append)
qed

text \<open>The remaining copy-witness case: a level-minimal column of the block
  prefix inside a later copy.  Its parent is the last block column at the
  previous copy's matching level (or the original prefix parent for exact
  copies); only the row-1 bound of that witness (\<open>r1ok_climb\<close>) is a class
  fact.\<close>

lemma r1ok_climb:
  assumes "M \<in> ST_PS"
    and "j1 < length M" and "j0 < j1"
    and "i1 = idx1 M j1" and "hasParent M i1 j1" and "j0 = parent M i1 j1"
    and "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
    and "q < j1 - j0"
    and "\<forall>r. r < q \<longrightarrow> entry M 0 (j0 + q) \<le> entry M 0 (j0 + r)"
    and "r' < j1 - j0" and "q \<le> r'"
    and "entry M 0 (j0 + r') = entry M 0 (j0 + q) + d0 - 1"
    and "\<forall>r. r' < r \<and> r < j1 - j0 \<longrightarrow> entry M 0 (j0 + q) + d0 - 1 < entry M 0 (j0 + r)"
  shows "entry M 1 (j0 + q) \<le> Suc (entry M 1 (j0 + r'))"
  sorry

lemma r1ok_copy_witness:
  assumes R: "r1ok M" and B: "blockok 0 M" and ST: "M \<in> ST_PS"
    and j1len: "j1 < length M" and j0j1: "j0 < j1"
    and i1d: "i1 = idx1 M j1" and hp: "hasParent M i1 j1"
    and j0d: "j0 = parent M i1 j1"
    and d0d: "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
    and opeq: "X = take j0 M @ concat (map (\<lambda>k.
           map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j)) [j0..<j1]) [0..<n])"
    and k1: "1 \<le> k" and kn: "k < n" and qL: "q < j1 - j0"
    and PM: "\<forall>r. r < q \<longrightarrow> entry M 0 (j0 + q) \<le> entry M 0 (j0 + r)"
    and pos: "0 < entry M 0 (j0 + q) + k * d0"
  shows "\<exists>w. w < j0 + (k * (j1 - j0) + q)
       \<and> Suc (fst (X ! w)) = fst (X ! (j0 + (k * (j1 - j0) + q)))
       \<and> (\<forall>l. w < l \<and> l < j0 + (k * (j1 - j0) + q) \<longrightarrow>
            fst (X ! (j0 + (k * (j1 - j0) + q))) \<le> fst (X ! l))
       \<and> snd (X ! (j0 + (k * (j1 - j0) + q))) \<le> Suc (snd (X ! w))"
proof -
  define L where "L = j1 - j0"
  have L0: "0 < L" unfolding L_def using j0j1 by simp
  have qL': "q < L" unfolding L_def by (rule qL)
  define i where "i = j0 + (k * L + q)"
  have nc: "\<And>k' q'. k' < n \<Longrightarrow> q' < L \<Longrightarrow>
        X ! (j0 + (k' * L + q')) = (entry M 0 (j0 + q') + k' * d0, entry M 1 (j0 + q'))"
    unfolding L_def using oper_bad_nth_copy[OF opeq j0j1 j1len] by blast
  have np: "\<And>l. l < j0 \<Longrightarrow> X ! l = M ! l"
    using oper_bad_nth_pre[OF opeq _ j1len j0j1] by blast
  have Xi: "X ! i = (entry M 0 (j0 + q) + k * d0, entry M 1 (j0 + q))"
    unfolding i_def by (rule nc[OF kn qL'])
  have e0step: "\<And>j. Suc j < length M \<Longrightarrow> entry M 0 (Suc j) \<le> Suc (entry M 0 j)"
  proof -
    fix j assume sj: "Suc j < length M"
    have "fst (M ! Suc j) \<le> Suc (fst (M ! j))" using B sj unfolding blockok_def by simp
    thus "entry M 0 (Suc j) \<le> Suc (entry M 0 j)" unfolding entry_def by simp
  qed
  define tgt where "tgt = entry M 0 (j0 + q) + d0 - 1"
  define cands where "cands = {r. r < L \<and> entry M 0 (j0 + r) \<le> tgt}"
  have fin: "finite cands" unfolding cands_def by simp
  show ?thesis
  proof (cases "cands = {}")
    case empty: True
    have d00: "d0 = 0"
    proof (rule ccontr)
      assume "d0 \<noteq> 0"
      hence "entry M 0 (j0 + q) \<le> tgt" unfolding tgt_def by simp
      hence "q \<in> cands" unfolding cands_def using qL' by simp
      thus False using empty by simp
    qed
    have e0pos: "0 < entry M 0 (j0 + q)" using pos d00 by simp
    have jqlen: "j0 + q < length M" using qL' j1len unfolding L_def by simp
    have ipM: "0 < fst (M ! (j0 + q))" using e0pos unfolding entry_def by simp
    from R jqlen ipM obtain p where p: "p < j0 + q" "Suc (fst (M ! p)) = fst (M ! (j0 + q))"
      "\<forall>l. p < l \<and> l < j0 + q \<longrightarrow> fst (M ! (j0 + q)) \<le> fst (M ! l)"
      "snd (M ! (j0 + q)) \<le> Suc (snd (M ! p))"
      unfolding r1ok_def by metis
    have pj0: "p < j0"
    proof (rule ccontr)
      assume "\<not> p < j0"
      hence pin: "p - j0 < q" and pdec: "p = j0 + (p - j0)" using p(1) by auto
      have "entry M 0 (j0 + (p - j0)) < entry M 0 (j0 + q)"
        using p(2) pdec unfolding entry_def by simp
      moreover have "entry M 0 (j0 + q) \<le> entry M 0 (j0 + (p - j0))" using PM pin by blast
      ultimately show False by simp
    qed
    have wi: "p < i" unfolding i_def using pj0 by simp
    have Xw: "X ! p = M ! p" by (rule np[OF pj0])
    have f1: "Suc (fst (X ! p)) = fst (X ! i)"
      unfolding Xi Xw using p(2) d00 unfolding entry_def by simp
    have nd: "\<forall>l. p < l \<and> l < i \<longrightarrow> fst (X ! i) \<le> fst (X ! l)"
    proof (intro allI impI)
      fix l assume lw: "p < l \<and> l < i"
      show "fst (X ! i) \<le> fst (X ! l)"
      proof (cases "l < j0")
        case True
        have "l < j0 + q" using True by simp
        hence "fst (M ! (j0 + q)) \<le> fst (M ! l)" using p(3) lw by blast
        thus ?thesis unfolding Xi np[OF True] entry_def using d00 by simp
      next
        case False
        define kl where "kl = (l - j0) div L"
        define rl where "rl = (l - j0) mod L"
        have ldec: "l = j0 + (kl * L + rl)"
          unfolding kl_def rl_def using False by simp
        have rlL: "rl < L" unfolding rl_def using L0 by simp
        have kln: "kl < n"
        proof -
          have "l < j0 + (k * L + q)" using lw unfolding i_def by simp
          hence "l - j0 < k * L + L" using qL' by simp
          hence "l - j0 < Suc k * L" by simp
          hence "kl < Suc k" unfolding kl_def
            by (metis less_mult_imp_div_less mult.commute)
          thus ?thesis using kn by simp
        qed
        have Xl: "X ! l = (entry M 0 (j0 + rl) + kl * d0, entry M 1 (j0 + rl))"
          unfolding ldec by (rule nc[OF kln rlL])
        have "rl \<notin> cands" using empty by simp
        hence "tgt < entry M 0 (j0 + rl)" unfolding cands_def using rlL by simp
        hence "entry M 0 (j0 + q) \<le> entry M 0 (j0 + rl)"
          unfolding tgt_def using d00 by simp
        thus ?thesis unfolding Xi Xl using d00 by simp
      qed
    qed
    have s1: "snd (X ! i) \<le> Suc (snd (X ! p))"
      unfolding Xi Xw using p(4) unfolding entry_def by simp
    show ?thesis
      using wi f1 nd s1 unfolding i_def L_def by blast
  next
    case ne: False
    define r' where "r' = Max cands"
    have rin: "r' \<in> cands" unfolding r'_def using fin ne by simp
    have rL: "r' < L" and rtgt: "entry M 0 (j0 + r') \<le> tgt"
      using rin unfolding cands_def by auto
    have rmax: "\<And>r. r \<in> cands \<Longrightarrow> r \<le> r'" unfolding r'_def using fin by simp
    have above: "\<forall>r. r' < r \<and> r < L \<longrightarrow> tgt < entry M 0 (j0 + r)"
    proof (intro allI impI)
      fix r assume rr: "r' < r \<and> r < L"
      have "r \<notin> cands" using rmax rr by fastforce
      thus "tgt < entry M 0 (j0 + r)" unfolding cands_def using rr by simp
    qed
    have qr: "q \<le> r'"
    proof (cases "d0 = 0")
      case True
      show ?thesis
      proof (rule ccontr)
        assume "\<not> q \<le> r'"
        hence "r' < q" by simp
        hence le1: "entry M 0 (j0 + q) \<le> entry M 0 (j0 + r')" using PM by blast
        have le2: "entry M 0 (j0 + r') \<le> entry M 0 (j0 + q) - 1"
          using rtgt unfolding tgt_def True by simp
        have "0 < entry M 0 (j0 + q)" using pos True by simp
        thus False using le1 le2 by simp
      qed
    next
      case False
      hence "entry M 0 (j0 + q) \<le> tgt" unfolding tgt_def by simp
      hence "q \<in> cands" unfolding cands_def using qL' by simp
      thus ?thesis by (rule rmax)
    qed
    have nR: "nextR M i1 j0 j1" unfolding j0d by (rule parent_nextR[OF hp])
    have rexact: "entry M 0 (j0 + r') = tgt"
    proof (cases "Suc r' < L")
      case True
      have "tgt < entry M 0 (j0 + Suc r')" using above True by blast
      moreover have "Suc (j0 + r') < length M"
        using True j1len unfolding L_def by simp
      ultimately have "tgt < Suc (entry M 0 (j0 + r'))"
        using e0step[of "j0 + r'"] by simp
      thus ?thesis using rtgt by simp
    next
      case False
      hence rlast: "r' = L - 1" using rL by simp
      have jr: "j0 + r' = j1 - 1" unfolding rlast L_def using j0j1 by simp
      have "Suc (j1 - 1) < length M" using j0j1 j1len by simp
      hence "entry M 0 j1 \<le> Suc (entry M 0 (j1 - 1))"
        using e0step[of "j1 - 1"] j0j1 by simp
      hence stepj1: "entry M 0 j1 - 1 \<le> entry M 0 (j0 + r')" using jr by simp
      have e0q0: "entry M 0 (j0 + q) \<le> entry M 0 j0"
      proof (cases "q = 0")
        case True thus ?thesis by simp
      next
        case False
        thus ?thesis using PM by auto
      qed
      have tgt_le: "tgt \<le> entry M 0 j1 - 1"
      proof (cases "0 < i1")
        case True
        have "nextrel1 M j0 j1" using nR True unfolding nextR_def by simp
        hence "le0 M j0 j1" unfolding nextrel1_def by blast
        hence le01: "entry M 0 j0 \<le> entry M 0 j1" by (rule le0_entry0_mono)
        have d0v: "d0 = entry M 0 j1 - entry M 0 j0" using True d0d by simp
        have "tgt = entry M 0 (j0 + q) + (entry M 0 j1 - entry M 0 j0) - 1"
          unfolding tgt_def d0v by simp
        also have "\<dots> \<le> entry M 0 j0 + (entry M 0 j1 - entry M 0 j0) - 1"
          using e0q0 by simp
        also have "\<dots> = entry M 0 j1 - 1" using le01 by simp
        finally show ?thesis .
      next
        case False
        have "nextrel0 M j0 j1" using nR False unfolding nextR_def i1d by (simp add: idx1_def)
        hence lt01: "entry M 0 j0 < entry M 0 j1" by (rule nextrel0_entry0_less)
        have d0v: "d0 = 0" using False d0d by simp
        have "tgt = entry M 0 (j0 + q) - 1" unfolding tgt_def d0v by simp
        also have "\<dots> \<le> entry M 0 j0 - 1" using e0q0 by simp
        also have "\<dots> \<le> entry M 0 j1 - 1" using lt01 by simp
        finally show ?thesis .
      qed
      show ?thesis using rtgt stepj1 tgt_le by simp
    qed
    define w where "w = j0 + ((k - 1) * L + r')"
    have wi: "w < i"
    proof -
      have "(k - 1) * L + r' < k * L + q \<longleftrightarrow> (k - 1) * L + r' < k * L + q" by simp
      have "(k - 1) * L + r' < (k - 1) * L + L" using rL by simp
      also have "\<dots> = k * L" using k1 by (simp add: mult_eq_if)
      also have "\<dots> \<le> k * L + q" by simp
      finally show ?thesis unfolding w_def i_def by simp
    qed
    have k1n: "k - 1 < n" using k1 kn by simp
    have Xw: "X ! w = (entry M 0 (j0 + r') + (k - 1) * d0, entry M 1 (j0 + r'))"
      unfolding w_def by (rule nc[OF k1n rL])
    have tgtpos: "Suc tgt = entry M 0 (j0 + q) + d0"
    proof (cases "d0 = 0")
      case True
      have "0 < entry M 0 (j0 + q)" using pos True by simp
      thus ?thesis unfolding tgt_def True by simp
    next
      case False thus ?thesis unfolding tgt_def by simp
    qed
    have f1: "Suc (fst (X ! w)) = fst (X ! i)"
    proof -
      have "Suc (fst (X ! w)) = Suc tgt + (k - 1) * d0"
        unfolding Xw rexact by simp
      also have "\<dots> = entry M 0 (j0 + q) + d0 + (k - 1) * d0" using tgtpos by simp
      also have "\<dots> = entry M 0 (j0 + q) + k * d0"
        using k1 by (simp add: mult_eq_if)
      finally show ?thesis unfolding Xi by simp
    qed
    have nd: "\<forall>l. w < l \<and> l < i \<longrightarrow> fst (X ! i) \<le> fst (X ! l)"
    proof (intro allI impI)
      fix l assume lw: "w < l \<and> l < i"
      have lge: "j0 \<le> l" using lw unfolding w_def by simp
      define kl where "kl = (l - j0) div L"
      define rl where "rl = (l - j0) mod L"
      have ldec: "l = j0 + (kl * L + rl)"
        unfolding kl_def rl_def using lge by simp
      have rlL: "rl < L" unfolding rl_def using L0 by simp
      have bnds: "(k - 1) * L + r' < kl * L + rl \<and> kl * L + rl < k * L + q"
        using lw unfolding w_def i_def ldec by simp
      have klr: "kl = k - 1 \<and> r' < rl \<or> kl = k \<and> rl < q"
      proof -
        have klk: "kl < Suc k"
        proof (rule ccontr)
          assume "\<not> kl < Suc k"
          hence "Suc k * L \<le> kl * L" by (intro mult_le_mono1) simp
          moreover have "kl * L + rl < Suc k * L" using bnds qL' by simp
          ultimately show False by simp
        qed
        have klk1: "k - 1 \<le> kl"
        proof (rule ccontr)
          assume "\<not> k - 1 \<le> kl"
          hence "Suc kl \<le> k - 1" by simp
          hence "Suc kl * L \<le> (k - 1) * L" by (intro mult_le_mono1)
          hence "kl * L + rl < (k - 1) * L" using rlL by simp
          thus False using bnds by simp
        qed
        consider "kl = k - 1" | "kl = k" using klk klk1 k1 by linarith
        thus ?thesis
        proof cases
          case 1
          have "r' < rl" using bnds unfolding 1 by simp
          thus ?thesis using 1 by simp
        next
          case 2
          have "rl < q" using bnds unfolding 2 by simp
          thus ?thesis using 2 by simp
        qed
      qed
      have Xl: "X ! l = (entry M 0 (j0 + rl) + kl * d0, entry M 1 (j0 + rl))"
        unfolding ldec by (rule nc[OF _ rlL]) (use klr kn k1n in auto)
      from klr show "fst (X ! i) \<le> fst (X ! l)"
      proof
        assume A: "kl = k - 1 \<and> r' < rl"
        have "tgt < entry M 0 (j0 + rl)" using above A rlL by blast
        hence "Suc tgt \<le> entry M 0 (j0 + rl)" by simp
        hence "entry M 0 (j0 + q) + d0 + (k - 1) * d0 \<le> entry M 0 (j0 + rl) + (k - 1) * d0"
          using tgtpos by simp
        hence "entry M 0 (j0 + q) + k * d0 \<le> entry M 0 (j0 + rl) + (k - 1) * d0"
          using k1 by (simp add: mult_eq_if)
        thus ?thesis unfolding Xi Xl using A by simp
      next
        assume A: "kl = k \<and> rl < q"
        have "entry M 0 (j0 + q) \<le> entry M 0 (j0 + rl)" using PM A by blast
        thus ?thesis unfolding Xi Xl using A by simp
      qed
    qed
    have s1: "snd (X ! i) \<le> Suc (snd (X ! w))"
    proof -
      have ab': "\<forall>r. r' < r \<and> r < j1 - j0 \<longrightarrow>
                  entry M 0 (j0 + q) + d0 - 1 < entry M 0 (j0 + r)"
        using above unfolding L_def tgt_def by blast
      have "entry M 1 (j0 + q) \<le> Suc (entry M 1 (j0 + r'))"
        by (rule r1ok_climb[OF ST j1len j0j1 i1d hp j0d d0d qL PM rL[unfolded L_def] qr
              rexact[unfolded tgt_def] ab'])
      thus ?thesis unfolding Xi Xw by simp
    qed
    show ?thesis
      using wi f1 nd s1 unfolding i_def L_def by blast
  qed
qed

lemma r1ok_oper_bad:
  assumes R: "r1ok M" and B: "blockok 0 M" and ST: "M \<in> ST_PS" and n1: "1 \<le> n"
    and j1d: "j1 = Lng M - 1" and j1nz: "j1 \<noteq> 0"
    and Fz: "\<not> (entry M 0 j1 = 0 \<and> entry M 1 j1 = 0)"
    and i1d: "i1 = idx1 M j1" and hp: "hasParent M i1 j1"
    and j0d: "j0 = parent M i1 j1"
    and d0d: "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
    and opeq0: "oper M n = take j0 M @ concat (map (\<lambda>k.
           map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j)) [j0..<j1]) [0..<n])"
  shows "r1ok (oper M n)"
proof -
  define X where "X = oper M n"
  have opeq: "X = take j0 M @ concat (map (\<lambda>k.
           map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j)) [j0..<j1]) [0..<n])"
    unfolding X_def by (rule opeq0)
  have nR: "nextR M i1 j0 j1" unfolding j0d by (rule parent_nextR[OF hp])
  have j0j1: "j0 < j1" using nR by (rule nextR_less)
  have j1len: "j1 < length M" using j1d j1nz by (cases M) auto
  define L where "L = j1 - j0"
  have L0: "0 < L" unfolding L_def using j0j1 by simp
  have lenX: "length X = j0 + n * L"
    unfolding L_def by (rule oper_bad_len[OF opeq j0j1 j1len])
  have pairM: "\<And>j. (entry M 0 j, entry M 1 j) = M ! j"
    unfolding entry_def by simp
  have np: "\<And>i. i < j0 \<Longrightarrow> X ! i = M ! i"
    using oper_bad_nth_pre[OF opeq _ j1len j0j1] by blast
  have nc: "\<And>k q. k < n \<Longrightarrow> q < L \<Longrightarrow>
        X ! (j0 + (k * L + q)) = (entry M 0 (j0 + q) + k * d0, entry M 1 (j0 + q))"
    unfolding L_def using oper_bad_nth_copy[OF opeq j0j1 j1len] by blast
  show ?thesis
    unfolding X_def[symmetric] r1ok_def
  proof (intro allI impI)
    fix i assume il: "i < length X" and ip: "0 < fst (X ! i)"
    show "\<exists>w. w < i \<and> Suc (fst (X ! w)) = fst (X ! i)
        \<and> (\<forall>l. w < l \<and> l < i \<longrightarrow> fst (X ! i) \<le> fst (X ! l))
        \<and> snd (X ! i) \<le> Suc (snd (X ! w))"
    proof (cases "i < j0")
      case True
      have iM: "i < length M" using True j0j1 j1len by simp
      have Xi: "X ! i = M ! i" by (rule np[OF True])
      from R iM ip Xi obtain w where w: "w < i" "Suc (fst (M ! w)) = fst (M ! i)"
        "\<forall>l. w < l \<and> l < i \<longrightarrow> fst (M ! i) \<le> fst (M ! l)"
        "snd (M ! i) \<le> Suc (snd (M ! w))"
        unfolding r1ok_def by metis
      have eqs: "\<And>l. l \<le> i \<Longrightarrow> X ! l = M ! l" using True np by simp
      show ?thesis
        by (intro exI[of _ w]) (use w eqs Xi in auto)
    next
      case ige: False
      define m where "m = i - j0"
      define k where "k = m div L"
      define q where "q = m mod L"
      have mdec: "m = k * L + q" unfolding k_def q_def by simp
      have idec: "i = j0 + (k * L + q)" unfolding mdec[symmetric] m_def using ige by simp
      have qL: "q < L" unfolding q_def using L0 by simp
      have mn: "m < n * L" using il lenX m_def ige by simp
      have kn: "k < n" unfolding k_def using mn L0
        by (metis less_mult_imp_div_less mult.commute)
      have Xi: "X ! i = (entry M 0 (j0 + q) + k * d0, entry M 1 (j0 + q))"
        unfolding idec by (rule nc[OF kn qL])
      have jqlen: "j0 + q < length M" using qL j1len unfolding L_def by simp
      show ?thesis
      proof (cases "k = 0")
        case k0: True
        have iq: "i = j0 + q" unfolding idec k0 by simp
        have XiM: "X ! i = M ! (j0 + q)"
          unfolding Xi k0 using pairM by simp
        have idl: "\<And>l. l \<le> i \<Longrightarrow> X ! l = M ! l"
        proof -
          fix l assume li: "l \<le> i"
          show "X ! l = M ! l"
          proof (cases "l < j0")
            case True thus ?thesis by (rule np)
          next
            case False
            have lq: "l - j0 \<le> q" using li iq by simp
            have ldec: "l = j0 + (0 * L + (l - j0))" using False by simp
            have "X ! l = (entry M 0 (j0 + (l - j0)) + 0 * d0, entry M 1 (j0 + (l - j0)))"
              using nc[OF _ _] kn lq qL by (subst ldec) (intro nc, auto)
            thus ?thesis using pairM False by simp
          qed
        qed
        have ipM: "0 < fst (M ! (j0 + q))" using ip XiM by simp
        from R jqlen ipM obtain w where w: "w < j0 + q" "Suc (fst (M ! w)) = fst (M ! (j0 + q))"
          "\<forall>l. w < l \<and> l < j0 + q \<longrightarrow> fst (M ! (j0 + q)) \<le> fst (M ! l)"
          "snd (M ! (j0 + q)) \<le> Suc (snd (M ! w))"
          unfolding r1ok_def by metis
        show ?thesis
          by (intro exI[of _ w])
             (use w idl XiM iq in \<open>auto simp: less_imp_le\<close>)
      next
        case kpos: False
        have k1: "1 \<le> k" using kpos by simp
        show ?thesis
        proof (cases "\<forall>r. r < q \<longrightarrow> entry M 0 (j0 + q) \<le> entry M 0 (j0 + r)")
          case PM: True
          have pos: "0 < entry M 0 (j0 + q) + k * d0" using ip Xi by simp
          from r1ok_copy_witness[OF R B ST j1len j0j1 i1d hp j0d d0d opeq k1 kn
                 qL[unfolded L_def] PM pos]
          show ?thesis unfolding idec L_def by blast
        next
          case nPM: False
          then obtain r0 where r0: "r0 < q" "entry M 0 (j0 + r0) < entry M 0 (j0 + q)"
            by auto
          have e0pos: "0 < entry M 0 (j0 + q)" using r0(2) by simp
          have ipM: "0 < fst (M ! (j0 + q))" using e0pos unfolding entry_def by simp
          from R jqlen ipM obtain p where p: "p < j0 + q" "Suc (fst (M ! p)) = fst (M ! (j0 + q))"
            "\<forall>l. p < l \<and> l < j0 + q \<longrightarrow> fst (M ! (j0 + q)) \<le> fst (M ! l)"
            "snd (M ! (j0 + q)) \<le> Suc (snd (M ! p))"
            unfolding r1ok_def by metis
          have pj0: "j0 \<le> p"
          proof (rule ccontr)
            assume "\<not> j0 \<le> p"
            hence "p < j0 + r0 \<and> j0 + r0 < j0 + q" using r0(1) by simp
            hence "fst (M ! (j0 + q)) \<le> fst (M ! (j0 + r0))" using p(3) by blast
            thus False using r0(2) unfolding entry_def by simp
          qed
          define rp where "rp = p - j0"
          have prp: "p = j0 + rp" unfolding rp_def using pj0 by simp
          have rpq: "rp < q" using p(1) prp by simp
          define w where "w = j0 + (k * L + rp)"
          have wi: "w < i" unfolding w_def idec using rpq by simp
          have Xw: "X ! w = (entry M 0 (j0 + rp) + k * d0, entry M 1 (j0 + rp))"
            unfolding w_def by (rule nc[OF kn]) (use rpq qL in simp)
          have fstw: "Suc (fst (X ! w)) = fst (X ! i)"
            unfolding Xw Xi using p(2) prp unfolding entry_def by simp
          have ndip: "\<forall>l. w < l \<and> l < i \<longrightarrow> fst (X ! i) \<le> fst (X ! l)"
          proof (intro allI impI)
            fix l assume lw: "w < l \<and> l < i"
            have lge: "j0 \<le> l" using lw unfolding w_def by simp
            define rl where "rl = l - j0 - k * L"
            have lrl: "l = j0 + (k * L + rl)"
              unfolding rl_def using lw unfolding w_def idec by simp
            have rlq: "rp < rl \<and> rl < q" using lw unfolding w_def idec lrl by simp
            have Xl: "X ! l = (entry M 0 (j0 + rl) + k * d0, entry M 1 (j0 + rl))"
              unfolding lrl by (rule nc[OF kn]) (use rlq qL in simp)
            have "fst (M ! (j0 + q)) \<le> fst (M ! (j0 + rl))"
              using p(3) rlq prp by simp
            thus "fst (X ! i) \<le> fst (X ! l)"
              unfolding Xi Xl entry_def by simp
          qed
          have sndw: "snd (X ! i) \<le> Suc (snd (X ! w))"
            unfolding Xi Xw using p(4) prp unfolding entry_def by simp
          show ?thesis using wi fstw ndip sndw by blast
        qed
      qed
    qed
  qed
qed

lemma r1ok_oper:
  assumes R: "r1ok M" and ST: "M \<in> ST_PS" and n1: "1 \<le> n"
  shows "r1ok (oper M n)"
proof -
  define j1 where "j1 = Lng M - 1"
  have b: "blockok 0 M" by (rule blockok_ST_PS[OF ST])
  show ?thesis
  proof (cases "j1 = 0")
    case True thus ?thesis using R unfolding oper_def Let_def j1_def by simp
  next
    case False
    show ?thesis
    proof (cases "entry M 0 j1 = 0 \<and> entry M 1 j1 = 0")
      case True
      have "oper M n = Pred M"
        unfolding oper_def Let_def j1_def[symmetric] using False True by auto
      moreover have "r1ok (Pred M)"
        unfolding Pred_def using R r1ok_butlast by simp
      ultimately show ?thesis by simp
    next
      case Fz: False
      define i1 where "i1 = idx1 M j1"
      show ?thesis
      proof (cases "hasParent M i1 j1")
        case False2: False
        have "oper M n = Pred M"
          unfolding oper_def Let_def j1_def[symmetric] i1_def[symmetric]
          using False Fz False2 by auto
        moreover have "r1ok (Pred M)"
          unfolding Pred_def using R r1ok_butlast by simp
        ultimately show ?thesis by simp
      next
        case hp: True
        define j0 where "j0 = parent M i1 j1"
        define d0 where "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
        have d1z: "(if 1 < i1 then entry M 1 j1 - entry M 1 j0 else 0) = 0"
          using idx1_le[of M j1] unfolding i1_def by simp
        have opeq: "oper M n = take j0 M @ concat (map (\<lambda>k.
               map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j)) [j0..<j1]) [0..<n])"
        proof -
          have "oper M n = take j0 M @ concat (map (\<lambda>k.
                 map (\<lambda>j. (entry M 0 j + k * d0,
                            entry M 1 j + k * (if 1 < i1 then entry M 1 j1 - entry M 1 j0 else 0)))
                 [j0..<j1]) [0..<n])"
            unfolding oper_def Let_def j1_def[symmetric] i1_def[symmetric]
              j0_def[symmetric] d0_def[symmetric]
            using False Fz hp by auto
          thus ?thesis unfolding d1z by simp
        qed
        show ?thesis
          by (rule r1ok_oper_bad[OF R b ST n1 j1_def False Fz i1_def hp j0_def d0_def opeq])
      qed
    qed
  qed
qed

theorem r1ok_ST_PS: "M \<in> ST_PS \<Longrightarrow> r1ok M"
proof (induction M rule: ST_PS.induct)
  case (diag v) show ?case by (rule r1ok_diagSeq)
next
  case (oper M n)
  show ?case by (rule r1ok_oper[OF oper.IH oper.hyps(1) oper.hyps(2)])
qed

definition fbseg :: "nat \<Rightarrow> pairseq \<Rightarrow> bool" where
  "fbseg u S \<longleftrightarrow> S \<noteq> [] \<and> (\<exists>pre pp mid post. pre @ (pp # mid @ S) @ post \<in> ST_PS
                 \<and> (\<forall>r \<in> set (mid @ S). fst pp < fst r)
                 \<and> (\<forall>r \<in> set mid. fst (hd S) \<le> fst r) \<and> u = snd pp)"

lemma dseg_fbseg: "dseg u S \<Longrightarrow> fbseg u S"
proof -
  assume "dseg u S"
  then obtain pre pp post where h: "pre @ (pp # S) @ post \<in> ST_PS"
    and dom: "\<forall>r \<in> set S. fst pp < fst r" and u: "u = snd pp" and ne: "S \<noteq> []"
    unfolding dseg_def by blast
  have h2: "pre @ (pp # [] @ S) @ post \<in> ST_PS" using h by simp
  have dom2: "\<forall>r \<in> set ([] @ S). fst pp < fst r" using dom by simp
  have fb2: "\<forall>r \<in> set []. fst (hd S) \<le> fst r" by simp
  show ?thesis unfolding fbseg_def using ne h2 dom2 fb2 u by blast
qed

lemma fbseg_K_desc:
  assumes "fbseg u (c # rest)"
    and ne: "takeWhile (\<lambda>r. fst c < fst r) rest \<noteq> []"
  shows "fbseg (snd c) (takeWhile (\<lambda>r. fst c < fst r) rest)"
proof -
  let ?K = "takeWhile (\<lambda>r. fst c < fst r) rest"
  let ?T = "dropWhile (\<lambda>r. fst c < fst r) rest"
  from assms(1) obtain pre pp mid post
    where h: "pre @ (pp # mid @ (c # rest)) @ post \<in> ST_PS"
    unfolding fbseg_def by blast
  have r: "rest = ?K @ ?T" by simp
  have eq: "pre @ (pp # mid @ (c # rest)) @ post
            = (pre @ (pp # mid)) @ (c # [] @ ?K) @ (?T @ post)"
    by (subst r) simp
  have h2: "(pre @ (pp # mid)) @ (c # [] @ ?K) @ (?T @ post) \<in> ST_PS"
    using h unfolding eq .
  have dom2: "\<forall>r \<in> set ([] @ ?K). fst c < fst r"
    using set_takeWhileD by fastforce
  have fb2: "\<forall>r \<in> set []. fst (hd ?K) \<le> fst r" by simp
  show ?thesis unfolding fbseg_def using ne h2 dom2 fb2 by blast
qed

lemma fbseg_T_desc:
  assumes A: "fbseg u (c # rest)"
    and ne: "dropWhile (\<lambda>r. fst c < fst r) rest \<noteq> []"
  shows "fbseg u (dropWhile (\<lambda>r. fst c < fst r) rest)"
proof -
  let ?K = "takeWhile (\<lambda>r. fst c < fst r) rest"
  let ?T = "dropWhile (\<lambda>r. fst c < fst r) rest"
  from A obtain pre pp mid post
    where h: "pre @ (pp # mid @ (c # rest)) @ post \<in> ST_PS"
    and dom: "\<forall>r \<in> set (mid @ (c # rest)). fst pp < fst r"
    and fb: "\<forall>r \<in> set mid. fst (hd (c # rest)) \<le> fst r"
    and u: "u = snd pp"
    unfolding fbseg_def by blast
  have r: "rest = ?K @ ?T" by simp
  have hdT: "fst (hd ?T) \<le> fst c" using hd_dropWhile[OF ne] by simp
  have eq: "pre @ (pp # mid @ (c # rest)) @ post
            = pre @ (pp # (mid @ (c # ?K)) @ ?T) @ post"
    by (subst r) simp
  have h2: "pre @ (pp # (mid @ (c # ?K)) @ ?T) @ post \<in> ST_PS"
    using h unfolding eq .
  have dom2: "\<forall>r \<in> set ((mid @ (c # ?K)) @ ?T). fst pp < fst r"
  proof
    fix x assume "x \<in> set ((mid @ (c # ?K)) @ ?T)"
    hence "x \<in> set (mid @ (c # rest))" by auto
    thus "fst pp < fst x" using dom by blast
  qed
  have fb2: "\<forall>r \<in> set (mid @ (c # ?K)). fst (hd ?T) \<le> fst r"
  proof
    fix x assume "x \<in> set (mid @ (c # ?K))"
    then consider "x \<in> set mid" | "x = c" | "x \<in> set ?K" by auto
    thus "fst (hd ?T) \<le> fst x"
    proof cases
      case 1
      have "fst c \<le> fst x" using fb 1 by simp
      thus ?thesis using hdT by simp
    next
      case 2 thus ?thesis using hdT by simp
    next
      case 3
      have "fst c < fst x" using set_takeWhileD 3 by fast
      thus ?thesis using hdT by simp
    qed
  qed
  show ?thesis unfolding fbseg_def using ne h2 dom2 fb2 u by blast
qed

text \<open>Depth-uniform piece class: the head is level-minimal in the piece and
  in the skipped prefix.  Subsumes \<open>fbseg\<close> (where blockok pins the head to
  \<open>fst pp + 1\<close>) and the top level (head at 0).  The level-equality of
  sum-adjacent successors is free from the definition.\<close>

definition fbsegD :: "pairseq \<Rightarrow> bool" where
  "fbsegD S \<longleftrightarrow> S \<noteq> [] \<and> (\<exists>pre mid post. pre @ mid @ S @ post \<in> ST_PS
       \<and> (\<forall>r \<in> set mid. fst (hd S) \<le> fst r)
       \<and> (\<forall>r \<in> set S. fst (hd S) \<le> fst r))"

lemma fbseg_fbsegD:
  assumes "fbseg u S"
  shows "fbsegD S"
proof -
  from assms obtain pre pp mid post
    where h: "pre @ (pp # mid @ S) @ post \<in> ST_PS"
    and dom: "\<forall>r \<in> set (mid @ S). fst pp < fst r"
    and fb: "\<forall>r \<in> set mid. fst (hd S) \<le> fst r"
    and ne: "S \<noteq> []"
    unfolding fbseg_def by blast
  let ?Y = "mid @ S @ post"
  let ?h = "pre @ (pp # mid @ S) @ post"
  have hh: "?h = pre @ pp # ?Y" by simp
  have Yne: "?Y \<noteq> []" using ne by (cases mid) auto
  have so: "stepsok ?h"
    using blockok_stepsok blockok_ST_PS[OF h] by blast
  have n0: "?h ! length pre = pp"
    unfolding hh by (simp add: nth_append_length)
  have n1: "?h ! Suc (length pre) = ?Y ! 0"
    unfolding hh by (simp add: nth_append)
  have ln: "Suc (length pre) < length ?h"
    unfolding hh using Yne by (cases ?Y) auto
  have step1: "fst (?Y ! 0) \<le> Suc (fst pp)"
    using so[unfolded stepsok_def, rule_format, OF ln] n0 n1 by simp
  have hc: "fst (hd S) = Suc (fst pp)"
  proof (cases mid)
    case Nil
    have "?Y ! 0 = hd S" unfolding Nil using ne by (cases S) auto
    hence "fst (hd S) \<le> Suc (fst pp)" using step1 by simp
    moreover have "fst pp < fst (hd S)" using dom ne by (cases S) auto
    ultimately show ?thesis by simp
  next
    case (Cons m0 mid')
    have "?Y ! 0 = m0" unfolding Cons by simp
    hence "fst m0 \<le> Suc (fst pp)" using step1 by simp
    moreover have "fst pp < fst m0" using dom unfolding Cons by simp
    ultimately have m0l: "fst m0 = Suc (fst pp)" by simp
    have "fst (hd S) \<le> fst m0" using fb unfolding Cons by simp
    moreover have "fst pp < fst (hd S)" using dom ne by (cases S) auto
    ultimately show ?thesis using m0l by simp
  qed
  have hS: "\<forall>r \<in> set S. fst (hd S) \<le> fst r"
  proof
    fix r assume "r \<in> set S"
    hence "fst pp < fst r" using dom by auto
    thus "fst (hd S) \<le> fst r" using hc by simp
  qed
  have h2: "(pre @ [pp]) @ mid @ S @ post \<in> ST_PS" using h by simp
  show ?thesis unfolding fbsegD_def using ne h2 fb hS by blast
qed

lemma fbsegD_hd_level:
  assumes "fbsegD (c # rest)"
    and "dropWhile (\<lambda>r. fst c < fst r) rest = c1 # rest1"
  shows "fst c1 = fst c"
proof -
  have c1S: "c1 \<in> set (c # rest)"
    using assms(2) by (metis hd_dropWhile list.sel(1) list.set_intros(2)
      list.simps(3) hd_in_set set_dropWhileD)
  have ge: "fst c \<le> fst c1"
    using assms(1) c1S unfolding fbsegD_def by auto
  have le: "\<not> fst c < fst c1"
    using hd_dropWhile assms(2) by (metis list.sel(1) list.simps(3))
  show ?thesis using ge le by simp
qed

text \<open>(C1) Shape of the normalized image on the class: the \<open>ins\<close> at the head
  never absorbs, so the head subscript is the head column's row-1 value.
  (Empirical: zero absorptions on all 8768 closure pieces.)\<close>

text \<open>(C1 core) The head of a piece dominates the head of its sum-tail: the
  subscript cannot rise across a level drop, and on subscript ties the
  projected argument of the earlier head is not below that of the later one.
  This is the \<open>ins\<close> no-absorb condition as a sequence-level class fact.\<close>

lemma fbseg_pair_host:
  assumes "fbseg u (c # rest)"
    and T: "dropWhile (\<lambda>r. fst c < fst r) rest = c1 # rest1"
  shows "\<exists>pre' post'. pre' @ (c # takeWhile (\<lambda>r. fst c < fst r) rest) @ [c1] @ post' \<in> ST_PS"
proof -
  let ?K = "takeWhile (\<lambda>r. fst c < fst r) rest"
  from assms(1) obtain pre pp mid post
    where h: "pre @ (pp # mid @ (c # rest)) @ post \<in> ST_PS"
    unfolding fbseg_def by blast
  have r: "rest = ?K @ (c1 # rest1)" using T by (metis takeWhile_dropWhile_id)
  have eq: "pre @ (pp # mid @ (c # rest)) @ post
            = (pre @ (pp # mid)) @ (c # ?K) @ [c1] @ (rest1 @ post)"
    by (subst r) simp
  show ?thesis using h unfolding eq by blast
qed

text \<open>Within a piece the sum-adjacent successor sits at exactly the head's
  level: \<open>blockok\<close> forces the first dominated column to level \<open>fst pp + 1\<close>,
  and the forest-boundary condition pins the piece head (and hence, by the
  domination sandwich, every sum-root) to that same level.\<close>

lemma fbseg_hd_level:
  assumes "fbseg u (c # rest)"
    and T: "dropWhile (\<lambda>r. fst c < fst r) rest = c1 # rest1"
  shows "fst c1 = fst c"
proof -
  from assms(1) obtain pre pp mid post
    where h: "pre @ (pp # mid @ (c # rest)) @ post \<in> ST_PS"
    and dom: "\<forall>r \<in> set (mid @ (c # rest)). fst pp < fst r"
    and fb: "\<forall>r \<in> set mid. fst (hd (c # rest)) \<le> fst r"
    unfolding fbseg_def by blast
  let ?Y = "mid @ (c # rest) @ post"
  let ?h = "pre @ (pp # mid @ (c # rest)) @ post"
  have hh: "?h = pre @ pp # ?Y" by simp
  have Yne: "?Y \<noteq> []" by (cases mid) auto
  have so: "stepsok ?h"
    using blockok_stepsok blockok_ST_PS[OF h] by blast
  have n0: "?h ! length pre = pp"
    unfolding hh by (simp add: nth_append_length)
  have n1: "?h ! Suc (length pre) = ?Y ! 0"
    unfolding hh by (simp add: nth_append)
  have ln: "Suc (length pre) < length ?h"
    unfolding hh using Yne by (cases ?Y) auto
  have step1: "fst (?Y ! 0) \<le> Suc (fst pp)"
    using so[unfolded stepsok_def, rule_format, OF ln] n0 n1 by simp
  have hc: "fst c = Suc (fst pp)"
  proof (cases mid)
    case Nil
    have "?Y ! 0 = c" unfolding Nil by simp
    hence "fst c \<le> Suc (fst pp)" using step1 by simp
    moreover have "fst pp < fst c" using dom by simp
    ultimately show ?thesis by simp
  next
    case (Cons m0 mid')
    have "?Y ! 0 = m0" unfolding Cons by simp
    hence "fst m0 \<le> Suc (fst pp)" using step1 by simp
    moreover have "fst pp < fst m0" using dom unfolding Cons by simp
    ultimately have m0l: "fst m0 = Suc (fst pp)" by simp
    have "fst c \<le> fst m0" using fb unfolding Cons by simp
    moreover have "fst pp < fst c" using dom by simp
    ultimately show ?thesis using m0l by simp
  qed
  have c1r: "c1 \<in> set rest"
    using T set_dropWhileD by (metis list.set_intros(1))
  have c1d: "fst pp < fst c1" using dom c1r by simp
  have c1u: "\<not> fst c < fst c1"
    using hd_dropWhile T by (metis list.sel(1) list.simps(3))
  show ?thesis using hc c1d c1u by simp
qed

lemma STS_A_aux:
  "\<forall>r\<in>set rest. fst p < fst r \<Longrightarrow> fst q = fst p \<Longrightarrow>
   cnf (translate (pre @ (p # rest) @ [q] @ post)) \<Longrightarrow> snd q \<le> snd p"
proof (induct pre arbitrary: post rule: length_induct)
  case (1 pre post)
  note IH = 1(1) and dom = 1(2) and fq = 1(3) and CNF = 1(4)
  show ?case
  proof (cases pre)
    case Nil
    have Tc: "[q] @ post = [] \<or> \<not> fst p < fst (hd ([q] @ post))" using fq by simp
    have e: "translate ((p # rest) @ [q] @ post)
              = P (snd p) (translate rest) (translate ([q] @ post))"
      using translate_block_append[of rest "fst p" "[q] @ post" "snd p"] dom Tc
      by (simp add: append.assoc)
    have e2: "translate ([q] @ post)
              = P (snd q) (translate (takeWhile (\<lambda>r. fst q < fst r) post))
                          (translate (dropWhile (\<lambda>r. fst q < fst r) post))"
      by (cases q) (simp only: append_Cons append_Nil translate.simps(2) fst_conv snd_conv)
    have c: "cnf (P (snd p) (translate rest)
                    (P (snd q) (translate (takeWhile (\<lambda>r. fst q < fst r) post))
                               (translate (dropWhile (\<lambda>r. fst q < fst r) post))))"
      using CNF unfolding Nil append_Nil e e2 .
    have nlt: "\<not> (P (snd p) (translate rest) Z
                  <o P (snd q) (translate (takeWhile (\<lambda>r. fst q < fst r) post)) Z)"
      using c by simp
    show ?thesis
    proof (rule ccontr)
      assume "\<not> snd q \<le> snd p"
      hence "snd p < snd q" by simp
      hence "P (snd p) (translate rest) Z
             <o P (snd q) (translate (takeWhile (\<lambda>r. fst q < fst r) post)) Z" by simp
      thus False using nlt by blast
    qed
  next
    case (Cons e pre')
    let ?Pe = "\<lambda>r. fst e < fst r"
    let ?tail = "pre' @ (p # rest) @ [q] @ post"
    have et: "translate (pre @ (p # rest) @ [q] @ post)
               = P (snd e) (translate (takeWhile ?Pe ?tail)) (translate (dropWhile ?Pe ?tail))"
      unfolding Cons by (simp only: append_Cons translate.simps(2))
    show ?thesis
    proof (cases "(\<forall>x \<in> set pre'. ?Pe x) \<and> fst e < fst p")
      case all: True
      have segP: "\<forall>x \<in> set ((p # rest) @ [q]). ?Pe x"
      proof
        fix x assume "x \<in> set ((p # rest) @ [q])"
        then consider "x = p" | "x \<in> set rest" | "x = q" by auto
        thus "?Pe x"
        proof cases
          case 1 thus ?thesis using all by simp
        next
          case 2 thus ?thesis using all dom by fastforce
        next
          case 3 thus ?thesis using all fq by simp
        qed
      qed
      have tw: "takeWhile ?Pe ?tail
                = pre' @ (p # rest) @ [q] @ takeWhile ?Pe post"
        using all segP by (simp add: takeWhile_append2)
      have cnfK: "cnf (translate (pre' @ (p # rest) @ [q] @ takeWhile ?Pe post))"
      proof -
        have "cnf (P (snd e) (translate (takeWhile ?Pe ?tail))
                             (translate (dropWhile ?Pe ?tail)))"
          using CNF unfolding et .
        hence "cnf (translate (takeWhile ?Pe ?tail))"
          by (cases "translate (dropWhile ?Pe ?tail)") auto
        thus ?thesis unfolding tw .
      qed
      have lp: "length pre' < length pre" by (simp add: Cons)
      show ?thesis using IH[rule_format, OF lp] dom fq cnfK by blast
    next
      case ncut: False
      have Dform: "\<exists>pre''. dropWhile ?Pe ?tail = pre'' @ (p # rest) @ [q] @ post
                            \<and> length pre'' < length pre"
      proof (cases "\<forall>x \<in> set pre'. ?Pe x")
        case True
        hence "\<not> fst e < fst p" using ncut by blast
        hence "dropWhile ?Pe ((p # rest) @ [q] @ post) = (p # rest) @ [q] @ post" by simp
        hence "dropWhile ?Pe ?tail = (p # rest) @ [q] @ post"
          using True by (simp add: dropWhile_append2)
        thus ?thesis unfolding Cons by (intro exI[of _ "[]"]) simp
      next
        case False
        then obtain w where w: "w \<in> set pre'" "\<not> ?Pe w" by blast
        have "dropWhile ?Pe ?tail = dropWhile ?Pe pre' @ (p # rest) @ [q] @ post"
          using w by (simp add: dropWhile_append1)
        moreover have "length (dropWhile ?Pe pre') < length pre"
          unfolding Cons using length_dropWhile_le[of ?Pe pre']
          by (simp add: le_imp_less_Suc)
        ultimately show ?thesis by blast
      qed
      obtain pre'' where D: "dropWhile ?Pe ?tail = pre'' @ (p # rest) @ [q] @ post"
        and lpre'': "length pre'' < length pre" using Dform by blast
      have cnfD: "cnf (translate (dropWhile ?Pe ?tail))"
      proof -
        have c0: "cnf (P (snd e) (translate (takeWhile ?Pe ?tail)) (translate (dropWhile ?Pe ?tail)))"
          using CNF unfolding et .
        thus ?thesis by (cases "translate (dropWhile ?Pe ?tail)") auto
      qed
      show ?thesis using IH[rule_format, OF lpre''] dom fq cnfD[unfolded D] by blast
    qed
  qed
qed

lemma STS_A:
  assumes "pre @ (p # rest) @ [q] @ post \<in> ST_PS"
    and "dropWhile (\<lambda>r. fst p < fst r) rest = []"
    and "fst q = fst p"
  shows "snd q \<le> snd p"
proof -
  have dom: "\<forall>r\<in>set rest. fst p < fst r"
    using assms(2) by (simp add: dropWhile_eq_Nil_conv)
  have "cnf (translate (pre @ (p # rest) @ [q] @ post))"
    using cnf_ST_PS[OF assms(1)] .
  thus ?thesis using STS_A_aux dom assms(3) by blast
qed

text \<open>The subscript bound of \<open>NT_dom\<close> in the level-equal case, via \<open>STS_A\<close>.\<close>

lemma NT_dom_sub_eq:
  assumes A: "fbseg u (c # rest)"
    and T: "dropWhile (\<lambda>r. fst c < fst r) rest = c1 # rest1"
    and F: "fst c1 = fst c"
  shows "snd c1 \<le> snd c"
proof -
  obtain pre' post' where h: "pre' @ (c # takeWhile (\<lambda>r. fst c < fst r) rest) @ [c1] @ post' \<in> ST_PS"
    using fbseg_pair_host[OF A T] by blast
  have d: "dropWhile (\<lambda>r. fst c < fst r) (takeWhile (\<lambda>r. fst c < fst r) rest) = []"
    unfolding dropWhile_eq_Nil_conv by (meson set_takeWhileD)
  show ?thesis by (rule STS_A[OF h d F])
qed

text \<open>(SIB core) On subscript ties the projected argument of the earlier head
  is not below that of its sum-successor.  This is the single remaining
  irreducible class fact of the C1 layer (empirically 0/1037 violations).\<close>

text \<open>Host-level sibling-run invariant: at every adjacent tie-sibling pair
  (positive level, equal level and row-1) the second run is the first or a
  proper prefix of it, and both runs are head-maximal.  (Empirically exact:
  2964 pairs, 2405 equal + 559 prefix, all head-max.)\<close>

definition mrun :: "pairseq \<Rightarrow> nat \<Rightarrow> pairseq" where
  "mrun M a = takeWhile (\<lambda>r. fst (M ! a) < fst r) (drop (Suc a) M)"

definition sibm :: "pairseq \<Rightarrow> bool" where
  "sibm M \<longleftrightarrow> (\<forall>a b. a < length M \<longrightarrow> 0 < fst (M ! a) \<longrightarrow>
      b = Suc a + length (mrun M a) \<longrightarrow> b < length M \<longrightarrow>
      fst (M ! b) = fst (M ! a) \<longrightarrow> snd (M ! b) = snd (M ! a) \<longrightarrow>
      ((mrun M b = mrun M a \<or> (\<exists>D. D \<noteq> [] \<and> mrun M a = mrun M b @ D))
       \<and> (mrun M a \<noteq> [] \<longrightarrow> snd (hd (mrun M a)) = maxr1 (mrun M a))
       \<and> (mrun M b \<noteq> [] \<longrightarrow> snd (hd (mrun M b)) = maxr1 (mrun M b))))"

lemma sibm_diagSeq: "sibm (diagSeq 0 v)"
proof -
  have len: "length (diagSeq 0 v) = Suc v" unfolding diagSeq_def by simp
  have nth: "\<And>j. j < Suc v \<Longrightarrow> diagSeq 0 v ! j = (j, j)"
    unfolding diagSeq_def by (simp del: upt_Suc)
  show ?thesis
    unfolding sibm_def
  proof (intro allI impI)
    fix a b assume al: "a < length (diagSeq 0 v)"
      and bp: "b = Suc a + length (mrun (diagSeq 0 v) a)"
      and bl: "b < length (diagSeq 0 v)"
      and fb: "fst (diagSeq 0 v ! b) = fst (diagSeq 0 v ! a)"
    have av: "a < Suc v" using al len by simp
    have bv: "b < Suc v" using bl len by simp
    have ab: "a < b" using bp by linarith
    have e1: "diagSeq 0 v ! b = (b, b)" by (rule nth[OF bv])
    have e2: "diagSeq 0 v ! a = (a, a)" by (rule nth[OF av])
    have "b = a" using fb unfolding e1 e2 by simp
    hence False using ab by simp
    thus "(mrun (diagSeq 0 v) b = mrun (diagSeq 0 v) a \<or>
           (\<exists>D. D \<noteq> [] \<and> mrun (diagSeq 0 v) a = mrun (diagSeq 0 v) b @ D))
       \<and> (mrun (diagSeq 0 v) a \<noteq> [] \<longrightarrow>
          snd (hd (mrun (diagSeq 0 v) a)) = maxr1 (mrun (diagSeq 0 v) a))
       \<and> (mrun (diagSeq 0 v) b \<noteq> [] \<longrightarrow>
          snd (hd (mrun (diagSeq 0 v) b)) = maxr1 (mrun (diagSeq 0 v) b))"
      by blast
  qed
qed

lemma takeWhile_take_comm: "takeWhile Q (take n xs) = take n (takeWhile Q xs)"
proof (induct xs arbitrary: n)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases n)
    case 0 thus ?thesis by simp
  next
    case (Suc n')
    show ?thesis unfolding Suc by (cases "Q x") (simp_all add: Cons.hyps)
  qed
qed

lemma mrun_take:
  assumes "a < m"
  shows "mrun (take m M) a = take (m - Suc a) (mrun M a)"
proof -
  have n: "take m M ! a = M ! a" using assms by simp
  have d: "drop (Suc a) (take m M) = take (m - Suc a) (drop (Suc a) M)"
    by (simp add: drop_take)
  show ?thesis
    unfolding mrun_def n d by (rule takeWhile_take_comm)
qed

lemma sibm_take:
  assumes S: "sibm M"
  shows "sibm (take m M)"
  unfolding sibm_def
proof (intro allI impI)
  fix a b assume al: "a < length (take m M)"
    and ap: "0 < fst (take m M ! a)"
    and bp: "b = Suc a + length (mrun (take m M) a)"
    and bl: "b < length (take m M)"
    and fb: "fst (take m M ! b) = fst (take m M ! a)"
    and sb: "snd (take m M ! b) = snd (take m M ! a)"
  have am: "a < m" and aM: "a < length M" using al by auto
  have bm: "b < m" and bM: "b < length M" using bl by auto
  have na: "take m M ! a = M ! a" using am by simp
  have nb: "take m M ! b = M ! b" using bm by simp
  have mt: "mrun (take m M) a = take (m - Suc a) (mrun M a)"
    by (rule mrun_take[OF am])
  have full: "mrun (take m M) a = mrun M a"
  proof (rule ccontr)
    assume "mrun (take m M) a \<noteq> mrun M a"
    hence "m - Suc a < length (mrun M a)" using mt by auto
    hence "length (mrun (take m M) a) = m - Suc a" using mt by simp
    hence "b = Suc a + (m - Suc a)" using bp by simp
    hence "b = m" using am by simp
    thus False using bm by simp
  qed
  have bp': "b = Suc a + length (mrun M a)" using bp full by simp
  have fb': "fst (M ! b) = fst (M ! a)" using fb na nb by simp
  have sb': "snd (M ! b) = snd (M ! a)" using sb na nb by simp
  have ap': "0 < fst (M ! a)" using ap na by simp
  from S[unfolded sibm_def, rule_format, OF aM ap' bp' bM fb' sb']
  have core: "mrun M b = mrun M a \<or> (\<exists>D. D \<noteq> [] \<and> mrun M a = mrun M b @ D)"
    and hA: "mrun M a \<noteq> [] \<longrightarrow> snd (hd (mrun M a)) = maxr1 (mrun M a)"
    and hB: "mrun M b \<noteq> [] \<longrightarrow> snd (hd (mrun M b)) = maxr1 (mrun M b)"
    by blast+
  have mtb: "mrun (take m M) b = take (m - Suc b) (mrun M b)"
    by (rule mrun_take[OF bm])
  have pre: "\<exists>G. mrun M b = mrun (take m M) b @ G"
    using mtb by (metis append_take_drop_id)
  then obtain G where G: "mrun M b = mrun (take m M) b @ G" by blast
  have coreT: "mrun (take m M) b = mrun (take m M) a \<or>
        (\<exists>D. D \<noteq> [] \<and> mrun (take m M) a = mrun (take m M) b @ D)"
  proof -
    from core show ?thesis
    proof
      assume e: "mrun M b = mrun M a"
      show ?thesis
      proof (cases "G = []")
        case True
        thus ?thesis using G e full by simp
      next
        case False
        have "mrun (take m M) a = mrun (take m M) b @ G"
          using full e G by simp
        thus ?thesis using False by blast
      qed
    next
      assume "\<exists>D. D \<noteq> [] \<and> mrun M a = mrun M b @ D"
      then obtain D where D: "D \<noteq> []" "mrun M a = mrun M b @ D" by blast
      have "mrun (take m M) a = mrun (take m M) b @ (G @ D)"
        using full D(2) G by simp
      moreover have "G @ D \<noteq> []" using D(1) by simp
      ultimately show ?thesis by blast
    qed
  qed
  have hAT: "mrun (take m M) a \<noteq> [] \<longrightarrow>
        snd (hd (mrun (take m M) a)) = maxr1 (mrun (take m M) a)"
    using hA full by simp
  have hBT: "mrun (take m M) b \<noteq> [] \<longrightarrow>
        snd (hd (mrun (take m M) b)) = maxr1 (mrun (take m M) b)"
  proof
    assume ne: "mrun (take m M) b \<noteq> []"
    have mbne: "mrun M b \<noteq> []" using G ne by auto
    have hdeq: "hd (mrun M b) = hd (mrun (take m M) b)" using G ne by auto
    have "snd (hd (mrun M b)) = maxr1 (mrun M b)" using hB mbne by blast
    hence ub: "snd (hd (mrun (take m M) b)) = maxr1 (mrun M b)" using hdeq by simp
    have "maxr1 (mrun (take m M) b) \<le> maxr1 (mrun M b)"
      unfolding maxr1_def using G ne by (intro Max_mono) auto
    moreover have "snd (hd (mrun (take m M) b)) \<le> maxr1 (mrun (take m M) b)"
      using maxr1_ub ne by (metis hd_in_set)
    ultimately show "snd (hd (mrun (take m M) b)) = maxr1 (mrun (take m M) b)"
      using ub by simp
  qed
  show "(mrun (take m M) b = mrun (take m M) a \<or>
         (\<exists>D. D \<noteq> [] \<and> mrun (take m M) a = mrun (take m M) b @ D))
      \<and> (mrun (take m M) a \<noteq> [] \<longrightarrow>
         snd (hd (mrun (take m M) a)) = maxr1 (mrun (take m M) a))
      \<and> (mrun (take m M) b \<noteq> [] \<longrightarrow>
         snd (hd (mrun (take m M) b)) = maxr1 (mrun (take m M) b))"
    using coreT hAT hBT by blast
qed

lemma sibm_butlast: "sibm M \<Longrightarrow> sibm (butlast M)"
  using sibm_take[of M "length M - 1"] by (simp add: butlast_conv_take)

lemma sibm_oper:
  assumes "sibm M" and "M \<in> ST_PS" and "1 \<le> n"
  shows "sibm (oper M n)"
  sorry

theorem sibm_ST_PS: "M \<in> ST_PS \<Longrightarrow> sibm M"
proof (induction M rule: ST_PS.induct)
  case (diag v) show ?case by (rule sibm_diagSeq)
next
  case (oper M n)
  show ?case by (rule sibm_oper[OF oper.IH oper.hyps(1) oper.hyps(2)])
qed

text \<open>(SIB) On subscript ties the successor's run is the same as, or a
  proper prefix of, the head's run, and in the proper-prefix case both runs
  are head-maximal (empirically 1418 equal + 650 prefix with both head-max,
  0 other).  A pure sequence-shape fact \<dash> the no-fire facts follow via
  \<open>E6_hdom\<close>.\<close>

lemma SIB_shape:
  assumes A: "fbseg u (c # rest)"
    and T: "dropWhile (\<lambda>r. fst c < fst r) rest = c1 # rest1"
    and tie: "snd c1 = snd c"
  shows "takeWhile (\<lambda>r. fst c1 < fst r) rest1 = takeWhile (\<lambda>r. fst c < fst r) rest
         \<or> (\<exists>D. D \<noteq> [] \<and> takeWhile (\<lambda>r. fst c < fst r) rest
                  = takeWhile (\<lambda>r. fst c1 < fst r) rest1 @ D
             \<and> snd (hd (takeWhile (\<lambda>r. fst c < fst r) rest))
                = maxr1 (takeWhile (\<lambda>r. fst c < fst r) rest)
             \<and> (takeWhile (\<lambda>r. fst c1 < fst r) rest1 \<noteq> [] \<longrightarrow>
                snd (hd (takeWhile (\<lambda>r. fst c1 < fst r) rest1))
                = maxr1 (takeWhile (\<lambda>r. fst c1 < fst r) rest1)))"
proof -
  let ?K = "takeWhile (\<lambda>r. fst c < fst r) rest"
  let ?K1 = "takeWhile (\<lambda>r. fst c1 < fst r) rest1"
  from A obtain pre pp mid post
    where h: "pre @ (pp # mid @ (c # rest)) @ post \<in> ST_PS"
    and dom: "\<forall>r \<in> set (mid @ (c # rest)). fst pp < fst r"
    unfolding fbseg_def by blast
  define H where "H = pre @ (pp # mid @ (c # rest)) @ post"
  define ic where "ic = length pre + 1 + length mid"
  have lvl: "fst c1 = fst c" by (rule fbseg_hd_level[OF A T])
  have cpos: "0 < fst c" using dom by auto
  have rsplit: "rest = ?K @ (c1 # rest1)"
    using T by (metis takeWhile_dropWhile_id)
  have Hic: "H ! ic = c"
  proof -
    have "H = (pre @ pp # mid) @ c # (rest @ post)"
      unfolding H_def by simp
    moreover have "length (pre @ pp # mid) = ic" unfolding ic_def by simp
    ultimately show ?thesis by (metis nth_append_length)
  qed
  have dic: "drop (Suc ic) H = rest @ post"
  proof -
    have "H = (pre @ pp # mid @ [c]) @ rest @ post" unfolding H_def by simp
    moreover have "length (pre @ pp # mid @ [c]) = Suc ic" unfolding ic_def by simp
    ultimately show ?thesis
      by (metis append_eq_conv_conj)
  qed
  have mric: "mrun H ic = ?K"
  proof -
    have "c1 \<in> set rest" using rsplit by (metis in_set_conv_decomp)
    moreover have "\<not> fst c < fst c1" using lvl by simp
    ultimately have "takeWhile (\<lambda>r. fst c < fst r) (rest @ post)
                     = takeWhile (\<lambda>r. fst c < fst r) rest"
      by (rule takeWhile_append1)
    thus ?thesis unfolding mrun_def dic Hic .
  qed
  define b where "b = Suc ic + length ?K"
  have icH: "ic < length H" unfolding H_def ic_def by simp
  have Hb: "H ! b = c1"
  proof -
    have "H = (pre @ pp # mid @ c # ?K) @ c1 # (rest1 @ post)"
      unfolding H_def by (subst rsplit) simp
    moreover have "length (pre @ pp # mid @ c # ?K) = b"
      unfolding b_def ic_def by simp
    ultimately show ?thesis by (metis nth_append_length)
  qed
  have bH: "b < length H"
  proof -
    have "length H = length pre + 1 + length mid + 1 + length rest + length post"
      unfolding H_def by simp
    moreover have "length rest = length ?K + 1 + length rest1"
      by (subst rsplit) simp
    ultimately show ?thesis unfolding b_def ic_def by simp
  qed
  have db: "drop (Suc b) H = rest1 @ post"
  proof -
    have "H = (pre @ pp # mid @ c # ?K @ [c1]) @ rest1 @ post"
      unfolding H_def by (subst rsplit) simp
    moreover have "length (pre @ pp # mid @ c # ?K @ [c1]) = Suc b"
      unfolding b_def ic_def by simp
    ultimately show ?thesis by (metis append_eq_conv_conj)
  qed
  have mrb_pre: "\<exists>E. mrun H b = ?K1 @ E"
  proof (cases "dropWhile (\<lambda>r. fst c1 < fst r) rest1 = []")
    case True
    have allr: "\<forall>r \<in> set rest1. fst c1 < fst r"
      using True by (simp add: dropWhile_eq_Nil_conv)
    have k1all: "?K1 = rest1" using allr by (simp add: takeWhile_eq_all_conv)
    have "takeWhile (\<lambda>r. fst c1 < fst r) (rest1 @ post)
          = rest1 @ takeWhile (\<lambda>r. fst c1 < fst r) post"
      using allr by (simp add: takeWhile_append2)
    hence "mrun H b = rest1 @ takeWhile (\<lambda>r. fst c1 < fst r) post"
      unfolding mrun_def db Hb by simp
    thus ?thesis using k1all by metis
  next
    case False
    then obtain w where w: "w \<in> set rest1" "\<not> fst c1 < fst w"
      by (metis dropWhile_eq_Nil_conv)
    have "takeWhile (\<lambda>r. fst c1 < fst r) (rest1 @ post)
          = takeWhile (\<lambda>r. fst c1 < fst r) rest1"
      using w by (rule takeWhile_append1)
    hence "mrun H b = ?K1" unfolding mrun_def db Hb by simp
    thus ?thesis by (metis append_Nil2)
  qed
  have sm: "sibm H" unfolding H_def by (rule sibm_ST_PS[OF h])
  have bb: "b = Suc ic + length (mrun H ic)" unfolding b_def mric by simp
  have fstb: "fst (H ! b) = fst (H ! ic)" unfolding Hb Hic using lvl by simp
  have sndb: "snd (H ! b) = snd (H ! ic)" unfolding Hb Hic using tie by simp
  have icpos: "0 < fst (H ! ic)" unfolding Hic using cpos by simp
  from sm[unfolded sibm_def, rule_format, OF icH icpos bb bH fstb sndb]
  have core: "mrun H b = mrun H ic \<or> (\<exists>D. D \<noteq> [] \<and> mrun H ic = mrun H b @ D)"
    and hmA: "mrun H ic \<noteq> [] \<longrightarrow> snd (hd (mrun H ic)) = maxr1 (mrun H ic)"
    and hmB: "mrun H b \<noteq> [] \<longrightarrow> snd (hd (mrun H b)) = maxr1 (mrun H b)"
    by blast+
  have hmK: "?K \<noteq> [] \<longrightarrow> snd (hd ?K) = maxr1 ?K" using hmA mric by simp
  from mrb_pre obtain E where E: "mrun H b = ?K1 @ E" by blast
  have K1K: "\<exists>F. ?K = ?K1 @ F"
    using core E mric by (metis append.assoc)
  have hmK1: "?K1 \<noteq> [] \<longrightarrow> snd (hd ?K1) = maxr1 ?K1"
  proof
    assume K1ne: "?K1 \<noteq> []"
    have mbne: "mrun H b \<noteq> []" using E K1ne by auto
    have hdeq: "hd (mrun H b) = hd ?K1" using E K1ne by auto
    have "snd (hd (mrun H b)) = maxr1 (mrun H b)" using hmB mbne by blast
    hence ub: "snd (hd ?K1) = maxr1 (mrun H b)" using hdeq by simp
    have "maxr1 ?K1 \<le> maxr1 (mrun H b)"
      unfolding maxr1_def using E K1ne by (intro Max_mono) auto
    moreover have "snd (hd ?K1) \<le> maxr1 ?K1"
      using maxr1_ub K1ne by (metis hd_in_set)
    ultimately show "snd (hd ?K1) = maxr1 ?K1" using ub by simp
  qed
  from K1K obtain F where F: "?K = ?K1 @ F" by blast
  show ?thesis
  proof (cases "F = []")
    case True
    have "?K1 = ?K" using F True by simp
    thus ?thesis by blast
  next
    case False
    have "?K \<noteq> []" using F False by auto
    thus ?thesis using F False hmK hmK1 by blast
  qed
qed

lemma NT_tie:
  assumes "fbseg u (c # rest)"
    and "dropWhile (\<lambda>r. fst c < fst r) rest = c1 # rest1"
    and "snd c1 = snd c"
  shows "\<not> olt (proj (snd c) (nrm (translate (takeWhile (\<lambda>r. fst c < fst r) rest))))
               (proj (snd c1) (nrm (translate (takeWhile (\<lambda>r. fst c1 < fst r) rest1))))"
  sorry

lemma NT_dom:
  assumes A: "fbseg u (c # rest)"
    and T: "dropWhile (\<lambda>r. fst c < fst r) rest = c1 # rest1"
  shows "\<not> (snd c < snd c1 \<or> (snd c = snd c1 \<and>
            olt (proj (snd c) (nrm (translate (takeWhile (\<lambda>r. fst c < fst r) rest))))
                (proj (snd c1) (nrm (translate (takeWhile (\<lambda>r. fst c1 < fst r) rest1))))))"
proof -
  have lvl: "fst c1 = fst c" by (rule fbseg_hd_level[OF A T])
  have sub: "snd c1 \<le> snd c" by (rule NT_dom_sub_eq[OF A T lvl])
  show ?thesis using sub NT_tie[OF A T] by auto
qed

lemma Gterm_mono:
  "u \<le> v \<Longrightarrow> Gterm v t \<subseteq> Gterm u t"
proof (induction t)
  case (P a b c)
  thus ?case by (auto split: if_splits)
qed simp

lemma NT_shape:
  "fbseg u S \<Longrightarrow> S = c # rest \<Longrightarrow>
   nrm (translate (c # rest))
   = P (snd c) (proj (snd c) (nrm (translate (takeWhile (\<lambda>r. fst c < fst r) rest))))
               (nrm (translate (dropWhile (\<lambda>r. fst c < fst r) rest)))"
proof (induct S arbitrary: c rest rule: length_induct)
  case (1 S)
  note IH = 1(1) and fb = 1(2) and C = 1(3)
  let ?K = "takeWhile (\<lambda>r. fst c < fst r) rest"
  let ?T = "dropWhile (\<lambda>r. fst c < fst r) rest"
  let ?A = "proj (snd c) (nrm (translate ?K))"
  have un: "nrm (translate (c # rest)) = ins (snd c) ?A (nrm (translate ?T))"
    by (simp only: translate.simps(2) nrm.simps(2))
  show ?case
  proof (cases ?T)
    case Nil
    have "nrm (translate ?T) = Z" unfolding Nil by simp
    thus ?thesis unfolding un by simp
  next
    case (Cons c1 rest1)
    have fbT: "fbseg u ?T"
      by (rule fbseg_T_desc[OF fb[unfolded C]]) (simp add: Cons)
    have lT: "length ?T < length S"
      unfolding C using length_dropWhile_le[of "\<lambda>r. fst c < fst r" rest] by simp
    have shT: "nrm (translate ?T)
               = P (snd c1) (proj (snd c1) (nrm (translate (takeWhile (\<lambda>r. fst c1 < fst r) rest1))))
                            (nrm (translate (dropWhile (\<lambda>r. fst c1 < fst r) rest1)))"
      using IH[rule_format, OF lT fbT Cons] unfolding Cons .
    have nab: "\<not> (snd c < snd c1 \<or> (snd c = snd c1 \<and>
              olt ?A (proj (snd c1) (nrm (translate (takeWhile (\<lambda>r. fst c1 < fst r) rest1))))))"
      by (rule NT_dom[OF fb[unfolded C] Cons])
    show ?thesis unfolding un shT using nab by auto
  qed
qed

lemma NT_hd:
  assumes "fbseg u S"
  shows "\<exists>A R. nrm (translate S) = P (snd (hd S)) A R"
proof -
  obtain c rest where C: "S = c # rest" using assms unfolding fbseg_def by (cases S) auto
  show ?thesis unfolding C using NT_shape[OF assms[unfolded C] refl] by simp
qed

text \<open>The normalized image of a sum-tail is strictly below that of the whole
  (the \<open>nrm\<close>-level analogue of \<open>translate_butlast_decrease\<close>'s sum order).\<close>

lemma NT_noabsorb:
  assumes sh: "nrm (translate (c # rest))
               = P (snd c) (proj (snd c) (nrm (translate (takeWhile (\<lambda>r. fst c < fst r) rest))))
                           (nrm (translate (dropWhile (\<lambda>r. fst c < fst r) rest)))"
    and Tform: "nrm (translate (dropWhile (\<lambda>r. fst c < fst r) rest)) = P e f g"
  shows "\<not> (snd c < e \<or> (snd c = e \<and>
            olt (proj (snd c) (nrm (translate (takeWhile (\<lambda>r. fst c < fst r) rest)))) f))"
proof
  let ?A = "proj (snd c) (nrm (translate (takeWhile (\<lambda>r. fst c < fst r) rest)))"
  let ?T = "nrm (translate (dropWhile (\<lambda>r. fst c < fst r) rest))"
  assume ab: "snd c < e \<or> (snd c = e \<and> olt ?A f)"
  have un: "nrm (translate (c # rest)) = ins (snd c) ?A ?T"
    by (simp only: translate.simps(2) nrm.simps(2))
  have "ins (snd c) ?A ?T = ?T" unfolding Tform using ab by auto
  hence e: "P (snd c) ?A ?T = ?T" using un sh by simp
  have "size ?T < size (P (snd c) ?A ?T)" by simp
  thus False using e by simp
qed

lemma NT_tail_lt:
  "fbseg u S \<Longrightarrow> S = c # rest \<Longrightarrow> dropWhile (\<lambda>r. fst c < fst r) rest \<noteq> [] \<Longrightarrow>
   olt (nrm (translate (dropWhile (\<lambda>r. fst c < fst r) rest))) (nrm (translate S))"
proof (induct S arbitrary: c rest rule: length_induct)
  case (1 S)
  note IH = 1(1) and fb = 1(2) and C = 1(3) and ne = 1(4)
  let ?K = "takeWhile (\<lambda>r. fst c < fst r) rest"
  let ?T = "dropWhile (\<lambda>r. fst c < fst r) rest"
  let ?A = "proj (snd c) (nrm (translate ?K))"
  have shS: "nrm (translate (c # rest)) = P (snd c) ?A (nrm (translate ?T))"
    by (rule NT_shape[OF fb[unfolded C] refl])
  have fbT: "fbseg u ?T" by (rule fbseg_T_desc[OF fb[unfolded C] ne])
  obtain c1 rest1 where T: "?T = c1 # rest1" using ne by (cases ?T) auto
  let ?K1 = "takeWhile (\<lambda>r. fst c1 < fst r) rest1"
  let ?T1 = "dropWhile (\<lambda>r. fst c1 < fst r) rest1"
  let ?B1 = "proj (snd c1) (nrm (translate ?K1))"
  have shT: "nrm (translate ?T) = P (snd c1) ?B1 (nrm (translate ?T1))"
    unfolding T by (rule NT_shape[OF fbT[unfolded T] refl])
  have nab: "\<not> (snd c < snd c1 \<or> (snd c = snd c1 \<and> olt ?A ?B1))"
    by (rule NT_noabsorb[OF shS shT])
  show ?case
  proof (cases "snd c1 < snd c")
    case True
    show ?thesis unfolding C shS shT by (simp add: True)
  next
    case False
    hence eq: "snd c1 = snd c" using nab by simp
    have nA: "\<not> olt ?A ?B1" using nab eq by simp
    show ?thesis
    proof (cases "?A = ?B1")
      case False
      hence BA: "olt ?B1 ?A" using nA olt_total by blast
      show ?thesis unfolding C shS shT using eq BA by simp
    next
      case ABeq: True
      have tl: "olt (nrm (translate ?T1)) (nrm (translate ?T))"
      proof (cases "?T1 = []")
        case True
        have z: "nrm (translate ?T1) = Z" unfolding True by simp
        show ?thesis unfolding z shT by simp
      next
        case T1ne: False
        have lT: "length ?T < length S"
          unfolding C using length_dropWhile_le[of "\<lambda>r. fst c < fst r" rest] by simp
        show ?thesis
          using IH[rule_format, OF lT fbT T T1ne] .
      qed
      show ?thesis unfolding C shS shT using eq ABeq tl[unfolded shT] by simp
    qed
  qed
qed

text \<open>(E6) When the projection at the host level fires, its value is the
  normalized image of the max-row1 suffix.\<close>

text \<open>If the level exceeds the head's row-1 value, no critical is visible:
  sum-root subscripts are non-increasing along the spine.\<close>

lemma Gterm_NT_high:
  "fbseg u S \<Longrightarrow> S = c # rest \<Longrightarrow> snd c < v \<Longrightarrow>
   Gterm v (nrm (translate S)) = {}"
proof (induct S arbitrary: c rest rule: length_induct)
  case (1 S)
  note IH = 1(1) and fb = 1(2) and C = 1(3) and cv = 1(4)
  let ?K = "takeWhile (\<lambda>r. fst c < fst r) rest"
  let ?T = "dropWhile (\<lambda>r. fst c < fst r) rest"
  have sh: "nrm (translate S) = P (snd c) (proj (snd c) (nrm (translate ?K))) (nrm (translate ?T))"
    unfolding C by (rule NT_shape[OF fb[unfolded C] refl])
  have Tpart: "Gterm v (nrm (translate ?T)) = {}"
  proof (cases ?T)
    case Nil
    show ?thesis unfolding Nil by simp
  next
    case (Cons c1 rest1)
    have fbT: "fbseg u ?T"
      by (rule fbseg_T_desc[OF fb[unfolded C]]) (simp add: Cons)
    have lT: "length ?T < length S"
      unfolding C using length_dropWhile_le[of "\<lambda>r. fst c < fst r" rest] by simp
    have "\<not> snd c < snd c1"
      using NT_dom[OF fb[unfolded C] Cons] by blast
    hence "snd c1 < v" using cv by simp
    thus ?thesis using IH[rule_format, OF lT fbT Cons] by blast
  qed
  show ?case unfolding sh using cv Tpart by simp
qed

lemma proj_fire_in:
  assumes f: "pfire u b"
  shows "proj u b \<in> Gterm u b"
proof -
  let ?gs = "filter (\<lambda>g. \<not> olt g b) (Glist u b)"
  have ne: "?gs \<noteq> []" using f pfire_filter by blast
  have "proj u b = maxo (hd ?gs) (tl ?gs)" using proj_once[of u b] ne by simp
  moreover have "maxo (hd ?gs) (tl ?gs) \<in> set ?gs" by (rule maxo_hdtl_in[OF ne])
  ultimately show ?thesis using set_Glist by auto
qed

lemma fbseg_K_dseg:
  assumes "fbseg u (c # rest)"
    and ne: "takeWhile (\<lambda>r. fst c < fst r) rest \<noteq> []"
  shows "dseg (snd c) (takeWhile (\<lambda>r. fst c < fst r) rest)"
proof -
  let ?K = "takeWhile (\<lambda>r. fst c < fst r) rest"
  let ?T = "dropWhile (\<lambda>r. fst c < fst r) rest"
  from assms(1) obtain pre pp mid post
    where h: "pre @ (pp # mid @ (c # rest)) @ post \<in> ST_PS"
    unfolding fbseg_def by blast
  have r: "rest = ?K @ ?T" by simp
  have eq: "pre @ (pp # mid @ (c # rest)) @ post
            = (pre @ (pp # mid)) @ (c # ?K) @ (?T @ post)"
    by (subst r) simp
  have h2: "(pre @ (pp # mid)) @ (c # ?K) @ (?T @ post) \<in> ST_PS"
    using h unfolding eq .
  have dom2: "\<forall>r \<in> set ?K. fst c < fst r"
    using set_takeWhileD by fastforce
  show ?thesis unfolding dseg_def using ne h2 dom2 by blast
qed

text \<open>(G-catalogue) Every critical of a normalized class image is \<open>Z\<close> or the
  normalized image of a nonempty contiguous sub-piece whose head realizes the
  head subscript.  Stated \<open>u\<close>-uniformly; the level only decides visibility.\<close>

lemma GCAT:
  "(\<exists>v. fbseg v S) \<Longrightarrow> g \<in> Gterm u (nrm (translate S)) \<Longrightarrow>
   g = Z \<or> (\<exists>pre' C post'. S = pre' @ C @ post' \<and> C \<noteq> [] \<and> g = nrm (translate C)
            \<and> hdsub g = snd (hd C))"
proof (induct S arbitrary: g u rule: length_induct)
  case (1 S)
  note IH = 1(1)
  obtain v where fb: "fbseg v S" using 1(2) by blast
  obtain c rest where C: "S = c # rest" using fb unfolding fbseg_def by (cases S) auto
  let ?K = "takeWhile (\<lambda>r. fst c < fst r) rest"
  let ?T = "dropWhile (\<lambda>r. fst c < fst r) rest"
  let ?A = "proj (snd c) (nrm (translate ?K))"
  have sh: "nrm (translate (c # rest)) = P (snd c) ?A (nrm (translate ?T))"
    by (rule NT_shape[OF fb[unfolded C] refl])
  have gin: "g \<in> Gterm u (P (snd c) ?A (nrm (translate ?T)))"
    using 1(3) unfolding C sh .
  consider (a) "u \<le> snd c" "g = ?A" | (b) "u \<le> snd c" "g \<in> Gterm u ?A"
         | (t) "g \<in> Gterm u (nrm (translate ?T))"
    using gin by (auto split: if_splits)
  thus ?case
  proof cases
    case a
    show ?thesis
    proof (cases "?K = []")
      case True
      have "?A = Z" unfolding True by (simp add: proj_Z)
      thus ?thesis using a by simp
    next
      case Kne: False
      show ?thesis
      proof (cases "pfire (snd c) (nrm (translate ?K))")
        case False
        have gA: "g = nrm (translate ?K)" using a proj_nofire[OF False] by simp
        have "\<exists>A R. nrm (translate ?K) = P (snd (hd ?K)) A R"
          by (rule NT_hd[OF fbseg_K_desc[OF fb[unfolded C] Kne]])
        hence hs: "hdsub g = snd (hd ?K)" using gA by auto
        have dec: "S = [c] @ ?K @ ?T" unfolding C by simp
        show ?thesis using gA hs dec Kne by blast
      next
        case True
        have "?A \<in> Gterm (snd c) (nrm (translate ?K))" by (rule proj_fire_in[OF True])
        hence gK: "g \<in> Gterm u (nrm (translate ?K))"
          using a Gterm_mono by blast
        have lK: "length ?K < length S"
          unfolding C using length_takeWhile_le[of "\<lambda>r. fst c < fst r" rest] by simp
        have pcK: "\<exists>v. fbseg v ?K"
          using fbseg_K_desc[OF fb[unfolded C] Kne] by blast
        from IH[rule_format, OF lK pcK gK]
        show ?thesis
        proof
          assume "g = Z" thus ?thesis by simp
        next
          assume "\<exists>pre' C' post'. ?K = pre' @ C' @ post' \<and> C' \<noteq> [] \<and> g = nrm (translate C')
                  \<and> hdsub g = snd (hd C')"
          then obtain pre' C' post' where w: "?K = pre' @ C' @ post'" "C' \<noteq> []"
            "g = nrm (translate C')" "hdsub g = snd (hd C')" by blast
          have "S = (c # pre') @ C' @ (post' @ ?T)"
            unfolding C by (metis w(1) append.assoc append_Cons takeWhile_dropWhile_id)
          thus ?thesis using w by blast
        qed
      qed
    qed
  next
    case b
    have Kne: "?K \<noteq> []"
    proof
      assume "?K = []"
      hence "?A = Z" by (simp add: proj_Z)
      thus False using b by simp
    qed
    have gK: "g \<in> Gterm u (nrm (translate ?K))"
    proof (cases "pfire (snd c) (nrm (translate ?K))")
      case False
      thus ?thesis using b proj_nofire[OF False] by simp
    next
      case True
      have "?A \<in> Gterm (snd c) (nrm (translate ?K))" by (rule proj_fire_in[OF True])
      hence "?A \<in> Gterm u (nrm (translate ?K))" using Gterm_mono b(1) by blast
      thus ?thesis using Gterm_trans b(2) by blast
    qed
    have lK: "length ?K < length S"
      unfolding C using length_takeWhile_le[of "\<lambda>r. fst c < fst r" rest] by simp
    have pcK: "\<exists>v. fbseg v ?K"
      using fbseg_K_desc[OF fb[unfolded C] Kne] by blast
    from IH[rule_format, OF lK pcK gK]
    show ?thesis
    proof
      assume "g = Z" thus ?thesis by simp
    next
      assume "\<exists>pre' C' post'. ?K = pre' @ C' @ post' \<and> C' \<noteq> [] \<and> g = nrm (translate C')
              \<and> hdsub g = snd (hd C')"
      then obtain pre' C' post' where w: "?K = pre' @ C' @ post'" "C' \<noteq> []"
        "g = nrm (translate C')" "hdsub g = snd (hd C')" by blast
      have "S = (c # pre') @ C' @ (post' @ ?T)"
        unfolding C by (metis w(1) append.assoc append_Cons takeWhile_dropWhile_id)
      thus ?thesis using w by blast
    qed
  next
    case t
    show ?thesis
    proof (cases "?T = []")
      case True
      have "nrm (translate ?T) = Z" unfolding True by simp
      thus ?thesis using t by simp
    next
      case Tne: False
      have lT: "length ?T < length S"
        unfolding C using length_dropWhile_le[of "\<lambda>r. fst c < fst r" rest] by simp
      have pcT: "\<exists>v. fbseg v ?T"
        using fbseg_T_desc[OF fb[unfolded C] Tne] by blast
      from IH[rule_format, OF lT pcT t]
      show ?thesis
      proof
        assume "g = Z" thus ?thesis by simp
      next
        assume "\<exists>pre' C' post'. ?T = pre' @ C' @ post' \<and> C' \<noteq> [] \<and> g = nrm (translate C')
                \<and> hdsub g = snd (hd C')"
        then obtain pre' C' post' where w: "?T = pre' @ C' @ post'" "C' \<noteq> []"
          "g = nrm (translate C')" "hdsub g = snd (hd C')" by blast
        have "S = (c # ?K @ pre') @ C' @ post'"
          unfolding C by (metis w(1) append.assoc append_Cons takeWhile_dropWhile_id)
        thus ?thesis using w by blast
      qed
    qed
  qed
qed

text \<open>(E6 membership) Under fire the suffix image is itself a critical above
  the whole: reached through the visible ancestor chain of the first max-row1
  column.\<close>

lemma E6_mem:
  assumes "dseg u S" and "pfire u (nrm (translate S))"
  shows "nrm (translate (msfx S)) \<in> Gterm u (nrm (translate S))
         \<and> \<not> olt (nrm (translate (msfx S))) (nrm (translate S))"
  sorry

text \<open>(E6 tie dominance) A violating critical whose head subscript reaches the
  max row-1 is still at most the suffix image (first-max priority).\<close>

text \<open>The deep tie case: a violating critical piece starting at a
  \<^emph>\<open>later\<close> max-row1 column than the first one (first-max priority; the
  remaining recursive core of the dominance).\<close>

lemma E6_dom_deep:
  assumes "dseg u S" and "pfire u (nrm (translate S))"
    and "S = pre' @ C @ post'" and "C \<noteq> []" and "snd (hd C) = maxr1 S"
    and "length (takeWhile (\<lambda>c. snd c < maxr1 S) S) < length pre'"
    and "nrm (translate C) \<in> Gterm u (nrm (translate S))"
    and "\<not> olt (nrm (translate C)) (nrm (translate S))"
  shows "ole (nrm (translate C)) (nrm (translate (msfx S)))"
  sorry

lemma E6_dom_tie:
  assumes "dseg u S" and "pfire u (nrm (translate S))"
    and "g \<in> Gterm u (nrm (translate S))" and "\<not> olt g (nrm (translate S))"
    and "g \<noteq> Z" and "hdsub g = maxr1 S"
  shows "ole g (nrm (translate (msfx S)))"
  sorry

lemma E6_value:
  assumes D: "dseg u S" and F: "pfire u (nrm (translate S))"
  shows "proj u (nrm (translate S)) = nrm (translate (msfx S))"
proof -
  let ?x = "nrm (translate S)"
  let ?ms = "nrm (translate (msfx S))"
  let ?gs = "filter (\<lambda>g. \<not> olt g ?x) (Glist u ?x)"
  let ?mx = "maxo (hd ?gs) (tl ?gs)"
  have Sne: "S \<noteq> []" using D unfolding dseg_def by blast
  obtain c rest where C: "S = c # rest" using Sne by (cases S) auto
  have xnz: "?x \<noteq> Z" unfolding C by (rule NT_neZ)
  have ne: "?gs \<noteq> []" using F pfire_filter by blast
  have po: "proj u ?x = ?mx" using proj_once[of u ?x] ne by simp
  have mxin: "?mx \<in> set ?gs" by (rule maxo_hdtl_in[OF ne])
  have mxG: "?mx \<in> Gterm u ?x" and mxv: "\<not> olt ?mx ?x"
    using mxin set_Glist by auto
  have msin: "?ms \<in> set ?gs"
    using E6_mem[OF D F] set_Glist by auto
  have msins: "?ms \<in> insert (hd ?gs) (set (tl ?gs))"
    using msin by (cases ?gs) auto
  have m2: "\<not> olt ?mx ?ms" using maxo_ub[OF msins] .
  have mxnz: "?mx \<noteq> Z"
  proof
    assume "?mx = Z"
    hence "\<not> olt Z ?x" using mxv by simp
    thus False using xnz by (cases ?x) auto
  qed
  have m1: "ole ?mx ?ms"
  proof (cases "hdsub ?mx = maxr1 S")
    case True
    show ?thesis by (rule E6_dom_tie[OF D F mxG mxv mxnz True])
  next
    case False
    have "hdsub ?mx \<le> maxr1 S" by (rule Gterm_NT_hdsub_le[OF mxG mxnz])
    hence "hdsub ?mx < maxr1 S" using False by simp
    hence "olt ?mx ?ms" using olt_msfx_lowsub[OF Sne] by blast
    thus ?thesis by simp
  qed
  have "?mx = ?ms" using m1 m2 by auto
  thus ?thesis using po by simp
qed

text \<open>(V4) In the both-fire q-cut configuration the x-side suffix is the last
  column alone.\<close>

lemma E6_qcut_last:
  assumes "segprov u S q" and "S \<noteq> []"
    and "pfire u (nrm (translate S))" and "pfire u (nrm (translate (S @ [q])))"
    and "maxr1 S < snd q"
  shows "msfx S = [last S]"
  sorry

text \<open>(V5) In the extension-only-fire configuration the segment is a single
  column.\<close>

lemma E6_iii_singleton:
  assumes "segprov u S q" and "S \<noteq> []"
    and "\<not> pfire u (nrm (translate S))" and "pfire u (nrm (translate (S @ [q])))"
  shows "\<exists>c. S = [c]"
  sorry

text \<open>(seam) In the both-fire same-cut configuration the max-row1 suffix
  satisfies the spiral invariants against the appended column.\<close>

lemma E6_seam:
  assumes "segprov u S q" and "S \<noteq> []"
    and "pfire u (nrm (translate S))" and "pfire u (nrm (translate (S @ [q])))"
    and "snd q \<le> maxr1 S"
  shows "fst (hd (msfx S)) \<le> fst q \<and> (\<forall>x \<in> set (msfx S). fst (hd (msfx S)) \<le> fst x)"
  sorry

subsection \<open>Standardness supplies the bundle\<close>

text \<open>The two remaining leaf obligations of the structural bundle against a
  standard host: the appended column's row-1 value does not exceed the head's
  at a new-summand position (sibling tops), and the no-absorb pair at tail
  positions (head preservation of \<open>nrm\<close> + sibling order).\<close>

text \<open>With equal row-0 values, the appended column is the next summand after
  \<open>p\<close>'s block at the same level of the host's translation; the \<open>cnf\<close> discipline
  of standard forms (non-increasing summand heads) gives the row-1 comparison.\<close>

lemma STS_B:
  assumes "pre @ (p # rest) @ [q] @ post \<in> ST_PS"
    and "dropWhile (\<lambda>r. fst p < fst r) rest \<noteq> []"
    and "fst (hd (dropWhile (\<lambda>r. fst p < fst r) rest)) = fst p"
  shows "\<not> (snd p < hdsub (nrm (translate (dropWhile (\<lambda>r. fst p < fst r) rest)))
            \<or> (snd p = hdsub (nrm (translate (dropWhile (\<lambda>r. fst p < fst r) rest)))
               \<and> olt (proj (snd p) (nrm (translate (takeWhile (\<lambda>r. fst p < fst r) rest))))
                     (hdarg (nrm (translate (dropWhile (\<lambda>r. fst p < fst r) rest))))))
      \<and> \<not> (snd p < hdsub (nrm (translate (dropWhile (\<lambda>r. fst p < fst r) rest @ [q])))
            \<or> (snd p = hdsub (nrm (translate (dropWhile (\<lambda>r. fst p < fst r) rest @ [q])))
               \<and> olt (proj (snd p) (nrm (translate (takeWhile (\<lambda>r. fst p < fst r) rest))))
                     (hdarg (nrm (translate (dropWhile (\<lambda>r. fst p < fst r) rest @ [q]))))))"
  sorry

lemma ST_snocokS_gen:
  "pre @ C @ [q] @ post \<in> ST_PS \<Longrightarrow> C \<noteq> [] \<Longrightarrow> fst (hd C) \<le> fst q \<Longrightarrow>
   \<forall>x \<in> set C. fst (hd C) \<le> fst x \<Longrightarrow> snocokS C q"
proof (induct C arbitrary: pre rule: length_induct)
  case (1 C)
  note IH = 1(1) and host = 1(2) and ne = 1(3) and INV = 1(4) and INV2 = 1(5)
  obtain p rest where C: "C = p # rest" using ne by (cases C) auto
  have stepsC: "stepsok (p # rest)"
  proof -
    have "blockok 0 (pre @ (p # rest) @ [q] @ post)"
      using blockok_ST_PS host[unfolded C] by blast
    hence "stepsok (pre @ (p # rest) @ ([q] @ post))" by (rule blockok_stepsok)
    thus ?thesis by (rule stepsok_sub)
  qed
  show ?case
  proof (cases "dropWhile (\<lambda>r. fst p < fst r) rest = []")
    case Tnil: True
    show ?thesis
    proof (cases "fst p < fst q")
      case qd: True
      have EI: "Einc (proj (snd p) (nrm (translate rest)))
                     (proj (snd p) (nrm (translate (rest @ [q]))))"
      proof (cases "rest = []")
        case True
        have l: "proj (snd p) (nrm (translate rest)) = Z"
          unfolding True by (simp add: proj_Z)
        have r: "proj (snd p) (nrm (translate (rest @ [q]))) = P (snd q) Z Z"
          unfolding True by (simp add: proj_Z proj_leaf)
        show ?thesis unfolding l r using einc.einc_end by blast
      next
        case rne: False
        have host2: "(pre @ [p]) @ rest @ [q] @ post \<in> ST_PS"
          using host unfolding C by simp
        have len2: "length rest < length C" unfolding C by simp
        have hdr: "fst (hd rest) \<le> Suc (fst p)"
        proof -
          have "Suc 0 < length (p # rest)" using rne by (cases rest) auto
          hence "fst ((p # rest) ! Suc 0) \<le> Suc (fst ((p # rest) ! 0))"
            using stepsC unfolding stepsok_def by blast
          thus ?thesis using rne by (simp add: hd_conv_nth)
        qed
        have INVq2: "fst (hd rest) \<le> fst q" using hdr qd by simp
        have allPr: "\<forall>r \<in> set rest. fst p < fst r"
          using Tnil by (simp add: dropWhile_eq_Nil_conv)
        have hdr2: "fst p < fst (hd rest)" using allPr rne by auto
        have INV2r: "\<forall>x \<in> set rest. fst (hd rest) \<le> fst x"
        proof
          fix x assume "x \<in> set rest"
          hence "fst p < fst x" using allPr by blast
          moreover have "fst (hd rest) \<le> Suc (fst p)" using hdr .
          ultimately show "fst (hd rest) \<le> fst x" by simp
        qed
        have sok2: "snocokS rest q" using IH len2 host2 rne INVq2 INV2r by blast
        have E2: "Einc (nrm (translate rest)) (nrm (translate (rest @ [q])))"
          by (rule nrm_snoc_str[OF sok2 rne])
        have allP: "\<forall>r \<in> set rest. fst p < fst r"
          using Tnil by (simp add: dropWhile_eq_Nil_conv)
        have PV: "segprov (snd p) rest q"
          unfolding segprov_def using host[unfolded C] allP qd by blast
        let ?x = "nrm (translate rest)" and ?x' = "nrm (translate (rest @ [q]))"
        show ?thesis
        proof (cases "pfire (snd p) ?x")
          case xf: True
          have x'f: "pfire (snd p) ?x'"
          proof -
            obtain g where "g \<in> Gterm (snd p) ?x" "\<not> olt g ?x" using xf by blast
            from fire_transport[OF E2 this] show ?thesis .
          qed
          have px: "proj (snd p) ?x = nrm (translate (msfx rest))"
            by (rule E6_value[OF segprov_dseg[OF PV rne] xf])
          have px': "proj (snd p) ?x' = nrm (translate (msfx (rest @ [q])))"
            by (rule E6_value[OF segprov_dsegq[OF PV] x'f])
          show ?thesis
          proof (cases "snd q \<le> maxr1 rest")
            case sc: True
            have meq: "msfx (rest @ [q]) = msfx rest @ [q]"
              by (rule msfx_append_le[OF rne sc])
            have Tne': "msfx rest \<noteq> []" by (rule msfx_ne[OF rne])
            have lenT': "length (msfx rest) < length C"
              unfolding C msfx_def
              using length_dropWhile_le[of "\<lambda>c. snd c < maxr1 rest" rest] by simp
            have Tsplit': "rest = takeWhile (\<lambda>c. snd c < maxr1 rest) rest @ msfx rest"
              by (rule msfx_decomp)
            have hostT': "(pre @ [p] @ takeWhile (\<lambda>c. snd c < maxr1 rest) rest)
                          @ msfx rest @ [q] @ post \<in> ST_PS"
              using host unfolding C
              by (metis Tsplit' append.assoc append_Cons append_Nil)
            have seam: "fst (hd (msfx rest)) \<le> fst q \<and>
                        (\<forall>x \<in> set (msfx rest). fst (hd (msfx rest)) \<le> fst x)"
              by (rule E6_seam[OF PV rne xf x'f sc])
            have sokT': "snocokS (msfx rest) q"
              using IH lenT' hostT' Tne' seam by blast
            have EiT: "Einc (nrm (translate (msfx rest)))
                            (nrm (translate (msfx rest @ [q])))"
              by (rule nrm_snoc_str[OF sokT' Tne'])
            show ?thesis unfolding px px' meq by (rule EiT)
          next
            case qc: False
            hence gt: "maxr1 rest < snd q" by simp
            have ml: "msfx rest = [last rest]"
              by (rule E6_qcut_last[OF PV rne xf x'f gt])
            have mq: "msfx (rest @ [q]) = [q]" by (rule msfx_append_gt[OF gt])
            have l1: "nrm (translate (msfx rest)) = P (snd (last rest)) Z Z"
              unfolding ml by (rule NT_single)
            have l2: "nrm (translate (msfx (rest @ [q]))) = P (snd q) Z Z"
              unfolding mq by (rule NT_single)
            have sl: "snd (last rest) = maxr1 rest"
              using msfx_hd[OF rne] unfolding ml by simp
            have "eflip (P (snd (last rest)) Z Z) (P (snd q) Z Z)"
              using sl gt eflip.eflip_leaf by simp
            thus ?thesis unfolding px px' l1 l2 by blast
          qed
        next
          case xnf: False
          have px: "proj (snd p) ?x = ?x" by (rule proj_nofire[OF xnf])
          show ?thesis
          proof (cases "pfire (snd p) ?x'")
            case x'f: True
            obtain c where Sc: "rest = [c]"
              using E6_iii_singleton[OF PV rne xnf x'f] by blast
            have px': "proj (snd p) ?x' = nrm (translate (msfx (rest @ [q])))"
              by (rule E6_value[OF segprov_dsegq[OF PV] x'f])
            have xc: "?x = P (snd c) Z Z" unfolding Sc by (rule NT_single)
            have cq: "snd c < snd q"
            proof (rule ccontr)
              assume "\<not> snd c < snd q"
              hence le: "snd q \<le> maxr1 rest" unfolding Sc maxr1_def by simp
              have mr: "msfx rest = rest"
                unfolding Sc msfx_def maxr1_def by simp
              have "msfx (rest @ [q]) = msfx rest @ [q]"
                by (rule msfx_append_le[OF rne le])
              hence "msfx (rest @ [q]) = rest @ [q]" using mr by simp
              hence "proj (snd p) ?x' = ?x'" using px' by simp
              thus False using proj_fire_ne[OF x'f] by simp
            qed
            have gt: "maxr1 rest < snd q" unfolding Sc maxr1_def using cq by simp
            have mq: "msfx (rest @ [q]) = [q]" by (rule msfx_append_gt[OF gt])
            have l2: "nrm (translate (msfx (rest @ [q]))) = P (snd q) Z Z"
              unfolding mq by (rule NT_single)
            have pxl: "proj (snd p) ?x = P (snd c) Z Z"
              unfolding xc by (rule proj_leaf)
            have "eflip (P (snd c) Z Z) (P (snd q) Z Z)"
              using cq eflip.eflip_leaf by simp
            thus ?thesis unfolding pxl px' l2 by blast
          next
            case x'nf: False
            have px': "proj (snd p) ?x' = ?x'" by (rule proj_nofire[OF x'nf])
            show ?thesis unfolding px px' by (rule E2)
          qed
        qed
      qed
      have unfA: "snocokS (p # rest) q \<longleftrightarrow>
            Einc (proj (snd p) (nrm (translate rest)))
                 (proj (snd p) (nrm (translate (rest @ [q]))))"
        by (simp only: snocokS.simps if_P[OF Tnil] if_P[OF qd])
      show ?thesis unfolding C unfA by (rule EI)
    next
      case qnd: False
      have unfA: "snocokS (p # rest) q \<longleftrightarrow> snd q \<le> snd p"
        by (simp only: snocokS.simps if_P[OF Tnil] if_not_P[OF qnd])
      have fpq: "fst q = fst p" using qnd INV unfolding C by simp
      show ?thesis unfolding C unfA
        by (rule STS_A[OF host[unfolded C] Tnil fpq])
    qed
  next
    case Tne: False
    let ?T = "dropWhile (\<lambda>r. fst p < fst r) rest"
    have Tsplit: "rest = takeWhile (\<lambda>r. fst p < fst r) rest @ ?T" by simp
    have host': "(pre @ [p] @ takeWhile (\<lambda>r. fst p < fst r) rest) @ ?T @ [q] @ post \<in> ST_PS"
      using host unfolding C by (metis Tsplit append.assoc append_Cons append_Nil)
    have lenT: "length ?T < length C"
      unfolding C using length_dropWhile_le[of "\<lambda>r. fst p < fst r" rest] by simp
    have hdT: "\<not> fst p < fst (hd ?T)"
      using hd_dropWhile[OF Tne] by blast
    have hdTin: "hd ?T \<in> set C"
      using Tne unfolding C by (meson hd_in_set set_dropWhileD list.set_intros(2))
    have hdTeq: "fst (hd ?T) = fst p"
    proof -
      have "fst p \<le> fst (hd ?T)" using INV2 hdTin unfolding C by auto
      thus ?thesis using hdT by simp
    qed
    have INVT: "fst (hd ?T) \<le> fst q" using hdTeq INV unfolding C by simp
    have INV2T: "\<forall>x \<in> set ?T. fst (hd ?T) \<le> fst x"
    proof
      fix x assume "x \<in> set ?T"
      hence "x \<in> set C" unfolding C
        by (meson set_dropWhileD list.set_intros(2))
      hence "fst p \<le> fst x" using INV2 unfolding C by auto
      thus "fst (hd ?T) \<le> fst x" using hdTeq by simp
    qed
    have sokT: "snocokS ?T q" using IH lenT host' Tne INVT INV2T by blast
    have nab: "\<not> (snd p < hdsub (nrm (translate ?T))
            \<or> (snd p = hdsub (nrm (translate ?T))
               \<and> olt (proj (snd p) (nrm (translate (takeWhile (\<lambda>r. fst p < fst r) rest))))
                     (hdarg (nrm (translate ?T)))))
      \<and> \<not> (snd p < hdsub (nrm (translate (?T @ [q])))
            \<or> (snd p = hdsub (nrm (translate (?T @ [q])))
               \<and> olt (proj (snd p) (nrm (translate (takeWhile (\<lambda>r. fst p < fst r) rest))))
                     (hdarg (nrm (translate (?T @ [q]))))))"
      by (rule STS_B[OF host[unfolded C] Tne hdTeq])
    have unfB: "snocokS (p # rest) q \<longleftrightarrow>
           (snocokS ?T q \<and>
            \<not> (snd p < hdsub (nrm (translate ?T))
               \<or> (snd p = hdsub (nrm (translate ?T))
                  \<and> olt (proj (snd p) (nrm (translate (takeWhile (\<lambda>r. fst p < fst r) rest))))
                        (hdarg (nrm (translate ?T))))) \<and>
            \<not> (snd p < hdsub (nrm (translate (?T @ [q])))
               \<or> (snd p = hdsub (nrm (translate (?T @ [q])))
                  \<and> olt (proj (snd p) (nrm (translate (takeWhile (\<lambda>r. fst p < fst r) rest))))
                        (hdarg (nrm (translate (?T @ [q])))))))"
      by (simp only: snocokS.simps if_not_P[OF Tne])
    show ?thesis unfolding C unfB using sokT nab by blast
  qed
qed

lemma ST_snoc_C:
  assumes H: "pre @ (p # rest) @ [q] @ post \<in> ST_PS"
    and T: "dropWhile (\<lambda>r. fst p < fst r) rest = []"
    and Q: "fst p < fst q"
  shows "olt (proj (snd p) (nrm (translate rest)))
             (proj (snd p) (nrm (translate (rest @ [q]))))"
proof -
  have hd0: "fst (hd (p # rest)) \<le> fst q" using Q by simp
  have allD: "\<forall>r \<in> set rest. fst p < fst r"
    using T by (simp add: dropWhile_eq_Nil_conv)
  have inv2: "\<forall>x \<in> set (p # rest). fst (hd (p # rest)) \<le> fst x"
    using allD by auto
  have S: "snocokS (p # rest) q"
    using ST_snocokS_gen[of pre "p # rest" q post] H hd0 inv2 by simp
  have unfA: "snocokS (p # rest) q \<longleftrightarrow>
        Einc (proj (snd p) (nrm (translate rest)))
             (proj (snd p) (nrm (translate (rest @ [q]))))"
    by (simp only: snocokS.simps if_P[OF T] if_P[OF Q])
  show ?thesis using S unfolding unfA using Einc_olt by blast
qed

lemma ST_snocok_gen:
  "pre @ C @ [q] @ post \<in> ST_PS \<Longrightarrow> C \<noteq> [] \<Longrightarrow> snocok C q"
proof (induct C arbitrary: pre rule: length_induct)
  case (1 C)
  note IH = 1(1) and host = 1(2) and ne = 1(3)
  obtain p rest where C: "C = p # rest" using ne by (cases C) auto
  show ?case
  proof (cases "dropWhile (\<lambda>r. fst p < fst r) rest = []")
    case Tnil: True
    have unfA: "snocok (p # rest) q \<longleftrightarrow>
          (fst p < fst q \<longrightarrow>
           olt (proj (snd p) (nrm (translate rest)))
               (proj (snd p) (nrm (translate (rest @ [q])))))"
      by (simp only: snocok.simps if_P[OF Tnil])
    show ?thesis unfolding C unfA
      using ST_snoc_C[OF host[unfolded C] Tnil] by blast
  next
    case Tne: False
    let ?T = "dropWhile (\<lambda>r. fst p < fst r) rest"
    have Tsplit: "rest = takeWhile (\<lambda>r. fst p < fst r) rest @ ?T"
      by simp
    have host': "(pre @ [p] @ takeWhile (\<lambda>r. fst p < fst r) rest) @ ?T @ [q] @ post \<in> ST_PS"
      using host unfolding C by (metis Tsplit append.assoc append_Cons append_Nil)
    have lenT: "length ?T < length C"
      unfolding C using length_dropWhile_le[of "\<lambda>r. fst p < fst r" rest]
      by simp
    have sokT: "snocok ?T q"
      using IH lenT host' Tne by blast
    have unfB: "snocok (p # rest) q \<longleftrightarrow> snocok ?T q"
      by (simp only: snocok.simps if_not_P[OF Tne])
    show ?thesis unfolding C unfB by (rule sokT)
  qed
qed

lemma ST_snocok_int:
  assumes "C @ [q] @ post \<in> ST_PS" and "C \<noteq> []"
  shows "snocok C q"
  using ST_snocok_gen[of "[]" C q post] assms by simp

lemma ST_snocok:
  assumes "C @ [q] \<in> ST_PS" and "C \<noteq> []"
  shows "snocok C q"
proof -
  have "C @ [q] @ [] \<in> ST_PS" using assms(1) by simp
  thus ?thesis using ST_snocok_int assms(2) by blast
qed

theorem nrm_snoc:
  assumes "C @ [p] \<in> ST_PS" and "C \<noteq> []"
  shows "olt (nrm (translate C)) (nrm (translate (C @ [p])))"
  by (rule nrm_snoc_seg[OF ST_snocok[OF assms] assms(2)])

theorem nrm_snoc_int:
  assumes "C @ [p] @ post \<in> ST_PS" and "C \<noteq> []"
  shows "olt (nrm (translate C)) (nrm (translate (C @ [p])))"
  by (rule nrm_snoc_seg[OF ST_snocok_int[OF assms] assms(2)])

theorem nrm_snoc_mid:
  assumes "pre @ C @ [p] @ post \<in> ST_PS" and "C \<noteq> []"
  shows "olt (nrm (translate C)) (nrm (translate (C @ [p])))"
  by (rule nrm_snoc_seg[OF ST_snocok_gen[OF assms] assms(2)])

text \<open>Iterated: the normalized image of a proper contiguous prefix is strictly
  below that of any contiguous extension within a standard host.\<close>

lemma NT_prefix_lt:
  "pre @ C @ D @ post \<in> ST_PS \<Longrightarrow> C \<noteq> [] \<Longrightarrow> D \<noteq> [] \<Longrightarrow>
   olt (nrm (translate C)) (nrm (translate (C @ D)))"
proof (induct D arbitrary: C post)
  case Nil thus ?case by simp
next
  case (Cons d0 D')
  have h1: "pre @ C @ [d0] @ (D' @ post) \<in> ST_PS" using Cons.prems(1) by simp
  have s1: "olt (nrm (translate C)) (nrm (translate (C @ [d0])))"
    by (rule nrm_snoc_mid[OF h1 Cons.prems(2)])
  show ?case
  proof (cases "D' = []")
    case True
    show ?thesis using s1 unfolding True by simp
  next
    case False
    have h2: "pre @ (C @ [d0]) @ D' @ post \<in> ST_PS" using Cons.prems(1) by simp
    have s2: "olt (nrm (translate (C @ [d0]))) (nrm (translate ((C @ [d0]) @ D')))"
      using Cons.hyps[OF h2 _ False] by simp
    have "olt (nrm (translate C)) (nrm (translate ((C @ [d0]) @ D')))"
      using olt_trans s1 s2 by blast
    thus ?thesis by simp
  qed
qed

text \<open>Resolution of \<open>E6_dom_tie\<close> using the catalogue and the prefix
  monotonicity.  Kept separate because the lemma-level dependency
  \<open>NT_prefix_lt \<rightarrow> ST_snocokS_gen \<rightarrow> E6_value \<rightarrow> E6_dom_tie\<close> is circular;
  stratified by segment length it is well-founded, so the final assembly
  inlines this proof into one simultaneous length induction
  (deep case = \<open>E6_dom_deep\<close>).\<close>

lemma E6_dom_tie_resolved:
  assumes D: "dseg u S" and F: "pfire u (nrm (translate S))"
    and G: "g \<in> Gterm u (nrm (translate S))" and V: "\<not> olt g (nrm (translate S))"
    and NZ: "g \<noteq> Z" and HS: "hdsub g = maxr1 S"
  shows "ole g (nrm (translate (msfx S)))"
proof -
  let ?m = "maxr1 S"
  let ?j0 = "length (takeWhile (\<lambda>c. snd c < ?m) S)"
  have fbS: "\<exists>v. fbseg v S" using dseg_fbseg[OF D] by blast
  from GCAT[OF fbS G] NZ obtain pre' Cp post'
    where w: "S = pre' @ Cp @ post'" "Cp \<noteq> []" "g = nrm (translate Cp)"
      "hdsub g = snd (hd Cp)" by blast
  have hdm: "snd (hd Cp) = ?m" using w(4) HS by simp
  obtain ch ct where Cp: "Cp = ch # ct" using w(2) by (cases Cp) auto
  have nthl: "S ! length pre' = hd Cp"
    unfolding w(1) Cp by (simp add: nth_append)
  have j0le: "?j0 \<le> length pre'"
  proof (rule ccontr)
    assume "\<not> ?j0 \<le> length pre'"
    hence l: "length pre' < length (takeWhile (\<lambda>c. snd c < ?m) S)" by simp
    have m1: "takeWhile (\<lambda>c. snd c < ?m) S ! length pre' = S ! length pre'"
      by (rule takeWhile_nth[OF l])
    have m2: "takeWhile (\<lambda>c. snd c < ?m) S ! length pre'
              \<in> set (takeWhile (\<lambda>c. snd c < ?m) S)"
      using l by (rule nth_mem)
    have "snd (takeWhile (\<lambda>c. snd c < ?m) S ! length pre') < ?m"
      using set_takeWhileD[OF m2] by blast
    thus False using m1 nthl hdm by simp
  qed
  have msd: "msfx S = drop ?j0 S"
    unfolding msfx_def by (rule dropWhile_eq_drop)
  show ?thesis
  proof (cases "?j0 = length pre'")
    case True
    have mC: "msfx S = Cp @ post'"
    proof -
      have "msfx S = drop ?j0 S" by (fact msd)
      also have "\<dots> = drop (length pre') S" using True by simp
      also have "\<dots> = Cp @ post'" unfolding w(1) by simp
      finally show ?thesis .
    qed
    show ?thesis
    proof (cases "post' = []")
      case True
      show ?thesis unfolding w(3) mC True by simp
    next
      case pne: False
      from D obtain preh pp posth where h: "preh @ (pp # S) @ posth \<in> ST_PS"
        unfolding dseg_def by blast
      have h2: "(preh @ (pp # pre')) @ Cp @ post' @ posth \<in> ST_PS"
        using h unfolding w(1) by simp
      have "olt (nrm (translate Cp)) (nrm (translate (Cp @ post')))"
        by (rule NT_prefix_lt[OF h2 w(2) pne])
      thus ?thesis unfolding w(3) mC by simp
    qed
  next
    case False
    hence lt: "?j0 < length pre'" using j0le by simp
    show ?thesis unfolding w(3)
      by (rule E6_dom_deep[OF D F w(1) w(2) hdm lt G[unfolded w(3)] V[unfolded w(3)]])
  qed
qed

text \<open>(LPL) A proper later piece whose head subscript matches the head-maximal
  whole loses to the whole.  The last comparison core of the exclusion side
  (empirically part of C2's zero-violation criterion).\<close>

lemma E6_lpl:
  assumes "dseg u S" and "snd (hd S) = maxr1 S"
    and "S = pre' @ C @ post'" and "C \<noteq> []" and "pre' \<noteq> []"
    and "snd (hd C) = maxr1 S"
    and "nrm (translate C) \<in> Gterm u (nrm (translate S))"
  shows "olt (nrm (translate C)) (nrm (translate S))"
  sorry

text \<open>(HDOM) A head-maximal class segment has no fire: every critical loses.
  Resolved down to \<open>E6_lpl\<close> by the catalogue, the subscript bound, and prefix
  monotonicity \<dash> the same pattern as \<open>E6_dom_tie_resolved\<close>.\<close>

lemma E6_hdom:
  assumes D: "dseg u S" and HM: "snd (hd S) = maxr1 S"
  shows "\<not> pfire u (nrm (translate S))"
proof
  assume F: "pfire u (nrm (translate S))"
  then obtain g where G: "g \<in> Gterm u (nrm (translate S))"
    and V: "\<not> olt g (nrm (translate S))" by blast
  have Sne: "S \<noteq> []" using D unfolding dseg_def by blast
  obtain AS RS where sh: "nrm (translate S) = P (snd (hd S)) AS RS"
    using NT_hd[OF dseg_fbseg[OF D]] by blast
  have NZ: "g \<noteq> Z"
  proof
    assume "g = Z"
    hence "\<not> olt Z (nrm (translate S))" using V by simp
    thus False unfolding sh by simp
  qed
  have fbS: "\<exists>v. fbseg v S" using dseg_fbseg[OF D] by blast
  from GCAT[OF fbS G] NZ obtain pre' Cp post'
    where w: "S = pre' @ Cp @ post'" "Cp \<noteq> []" "g = nrm (translate Cp)"
      "hdsub g = snd (hd Cp)" by blast
  have le: "hdsub g \<le> maxr1 S" by (rule Gterm_NT_hdsub_le[OF G NZ])
  show False
  proof (cases "hdsub g = maxr1 S")
    case False
    hence lt: "hdsub g < maxr1 S" using le by simp
    have "olt g (nrm (translate S))"
      using lt NZ unfolding sh HM by (cases g) auto
    thus False using V by blast
  next
    case True
    have hdm: "snd (hd Cp) = maxr1 S" using w(4) True by simp
    show False
    proof (cases "pre' = []")
      case pe: True
      have CpS: "Cp \<noteq> S"
      proof
        assume "Cp = S"
        hence "g = nrm (translate S)" using w(3) by simp
        moreover have "size g < size (nrm (translate S))"
          using Gterm_size[OF G] .
        ultimately show False by simp
      qed
      have pne: "post' \<noteq> []" using w(1) CpS unfolding pe by auto
      from D obtain preh pp posth where h: "preh @ (pp # S) @ posth \<in> ST_PS"
        unfolding dseg_def by blast
      have h2: "(preh @ [pp]) @ Cp @ post' @ posth \<in> ST_PS"
        using h unfolding w(1) pe by simp
      have "olt (nrm (translate Cp)) (nrm (translate (Cp @ post')))"
        by (rule NT_prefix_lt[OF h2 w(2) pne])
      hence "olt g (nrm (translate S))"
        using w(3) w(1) unfolding pe by simp
      thus False using V by blast
    next
      case pne: False
      have "olt (nrm (translate Cp)) (nrm (translate S))"
        by (rule E6_lpl[OF D HM w(1) w(2) pne hdm G[unfolded w(3)]])
      thus False using w(3) V by simp
    qed
  qed
qed

text \<open>Resolution of \<open>NT_tie\<close> from \<open>SIB_prefix\<close>: equal runs give equal
  projections; a proper-prefix run is strictly below by prefix monotonicity,
  with both projections trivial by the no-fire conjuncts.  (Same stratified
  placement as the other resolved lemmas.)\<close>

lemma NT_tie_resolved:
  assumes A: "fbseg u (c # rest)"
    and T: "dropWhile (\<lambda>r. fst c < fst r) rest = c1 # rest1"
    and tie: "snd c1 = snd c"
  shows "\<not> olt (proj (snd c) (nrm (translate (takeWhile (\<lambda>r. fst c < fst r) rest))))
               (proj (snd c1) (nrm (translate (takeWhile (\<lambda>r. fst c1 < fst r) rest1))))"
proof -
  let ?K = "takeWhile (\<lambda>r. fst c < fst r) rest"
  let ?K1 = "takeWhile (\<lambda>r. fst c1 < fst r) rest1"
  from SIB_shape[OF A T tie]
  show ?thesis
  proof
    assume eq: "?K1 = ?K"
    show ?thesis unfolding eq tie using olt_irrefl by blast
  next
    assume "\<exists>D. D \<noteq> [] \<and> ?K = ?K1 @ D
             \<and> snd (hd ?K) = maxr1 ?K
             \<and> (?K1 \<noteq> [] \<longrightarrow> snd (hd ?K1) = maxr1 ?K1)"
    then obtain D where D: "D \<noteq> []" "?K = ?K1 @ D"
      and hmK: "snd (hd ?K) = maxr1 ?K"
      and hmK1: "?K1 \<noteq> [] \<longrightarrow> snd (hd ?K1) = maxr1 ?K1" by blast
    have Kne: "?K \<noteq> []" using D by auto
    have nfK: "\<not> pfire (snd c) (nrm (translate ?K))"
      by (rule E6_hdom[OF fbseg_K_dseg[OF A Kne] hmK])
    have pK: "proj (snd c) (nrm (translate ?K)) = nrm (translate ?K)"
      by (rule proj_nofire[OF nfK])
    show ?thesis
    proof (cases "?K1 = []")
      case True
      have z: "nrm (translate ?K1) = Z" unfolding True by simp
      have "proj (snd c1) (nrm (translate ?K1)) = Z" unfolding z by (simp add: proj_Z)
      thus ?thesis using not_olt_Z by simp
    next
      case K1ne: False
      have fbT: "fbseg u (c1 # rest1)"
        using fbseg_T_desc[OF A] T by simp
      have dsK1: "dseg (snd c1) ?K1"
        by (rule fbseg_K_dseg[OF fbT K1ne])
      have hm1: "snd (hd ?K1) = maxr1 ?K1"
        using hmK1 K1ne by blast
      have nfK1: "\<not> pfire (snd c1) (nrm (translate ?K1))"
        by (rule E6_hdom[OF dsK1 hm1])
      have pK1: "proj (snd c1) (nrm (translate ?K1)) = nrm (translate ?K1)"
        by (rule proj_nofire[OF nfK1])
      from A obtain pre pp mid post
        where h: "pre @ (pp # mid @ (c # rest)) @ post \<in> ST_PS"
        unfolding fbseg_def by blast
      have r: "rest = ?K @ dropWhile (\<lambda>r. fst c < fst r) rest" by simp
      have eqh: "pre @ (pp # mid @ (c # rest)) @ post
                 = (pre @ (pp # mid) @ [c]) @ ?K1 @ D
                   @ (dropWhile (\<lambda>r. fst c < fst r) rest @ post)"
        by (subst r) (simp add: D(2))
      have h2: "(pre @ (pp # mid) @ [c]) @ ?K1 @ D
                @ (dropWhile (\<lambda>r. fst c < fst r) rest @ post) \<in> ST_PS"
        using h unfolding eqh .
      have "olt (nrm (translate ?K1)) (nrm (translate (?K1 @ D)))"
        by (rule NT_prefix_lt[OF h2 K1ne D(1)])
      hence "olt (nrm (translate ?K1)) (nrm (translate ?K))"
        using D(2) by simp
      thus ?thesis unfolding pK pK1
        using olt_total olt_irrefl olt_trans by blast
    qed
  qed
qed

text \<open>(cascade, K side) If the maximum lives in the head's dominated run and
  the segment fires, the head's run extends to the end, the head is visible,
  and the run itself fires at the head's level.\<close>

lemma E6_nbcK_T:
  assumes "dseg u (c0 # rest)" and "u \<le> snd c0"
    and "takeWhile (\<lambda>r. fst c0 < fst r) rest \<noteq> []"
    and "maxr1 (takeWhile (\<lambda>r. fst c0 < fst r) rest) = maxr1 (c0 # rest)"
    and "snd c0 < maxr1 (c0 # rest)"
  shows "dropWhile (\<lambda>r. fst c0 < fst r) rest = []"
  sorry

lemma E6_nbcK_K:
  assumes "dseg u (c0 # rest)" and "pfire u (nrm (translate (c0 # rest)))"
    and "u \<le> snd c0"
    and "takeWhile (\<lambda>r. fst c0 < fst r) rest \<noteq> []"
    and "maxr1 (takeWhile (\<lambda>r. fst c0 < fst r) rest) = maxr1 (c0 # rest)"
    and "snd c0 < maxr1 (c0 # rest)"
  shows "pfire (snd c0) (nrm (translate (takeWhile (\<lambda>r. fst c0 < fst r) rest)))
         \<or> msfx (takeWhile (\<lambda>r. fst c0 < fst r) rest) = takeWhile (\<lambda>r. fst c0 < fst r) rest"
  sorry

lemma E6_nbcK:
  assumes D: "dseg u (c0 # rest)" and F: "pfire u (nrm (translate (c0 # rest)))"
    and K: "takeWhile (\<lambda>r. fst c0 < fst r) rest \<noteq> []"
    and Km: "maxr1 (takeWhile (\<lambda>r. fst c0 < fst r) rest) = maxr1 (c0 # rest)"
    and hl: "snd c0 < maxr1 (c0 # rest)"
  shows "dropWhile (\<lambda>r. fst c0 < fst r) rest = [] \<and> u \<le> snd c0 \<and>
         (pfire (snd c0) (nrm (translate (takeWhile (\<lambda>r. fst c0 < fst r) rest)))
          \<or> msfx (takeWhile (\<lambda>r. fst c0 < fst r) rest) = takeWhile (\<lambda>r. fst c0 < fst r) rest)"
proof -
  have uv: "u \<le> snd c0"
  proof (rule ccontr)
    assume "\<not> u \<le> snd c0"
    hence "snd c0 < u" by simp
    hence "Gterm u (nrm (translate (c0 # rest))) = {}"
      by (rule Gterm_NT_high[OF dseg_fbseg[OF D] refl])
    thus False using F by blast
  qed
  show ?thesis
    using E6_nbcK_T[OF D uv K Km hl] uv E6_nbcK_K[OF D F uv K Km hl] by blast
qed

text \<open>(cascade, T side) If the maximum lives strictly in the sum tail, the
  membership and violator facts transfer to the tail with the whole as
  threshold.\<close>

lemma E6_memT:
  assumes "dseg u (c0 # rest)" and "pfire u (nrm (translate (c0 # rest)))"
    and "dropWhile (\<lambda>r. fst c0 < fst r) rest \<noteq> []"
    and "maxr1 (c0 # takeWhile (\<lambda>r. fst c0 < fst r) rest) < maxr1 (c0 # rest)"
  shows "nrm (translate (msfx (dropWhile (\<lambda>r. fst c0 < fst r) rest)))
           \<in> Gterm u (nrm (translate (dropWhile (\<lambda>r. fst c0 < fst r) rest)))
         \<and> \<not> olt (nrm (translate (msfx (dropWhile (\<lambda>r. fst c0 < fst r) rest))))
                 (nrm (translate (c0 # rest)))"
  sorry

text \<open>Resolution of \<open>E6_mem\<close>: head-max is excluded by \<open>E6_hdom\<close>; max-in-run
  assembles from the K-cascade, \<open>E6_value\<close> at the run, and pure subscript
  facts; max-in-tail transfers by the T-cascade and \<open>msfx_tail\<close>.\<close>

lemma E6_mem_resolved:
  assumes D: "dseg u S" and F: "pfire u (nrm (translate S))"
  shows "nrm (translate (msfx S)) \<in> Gterm u (nrm (translate S))
         \<and> \<not> olt (nrm (translate (msfx S))) (nrm (translate S))"
proof -
  have Sne: "S \<noteq> []" using D unfolding dseg_def by blast
  obtain c0 rest where C: "S = c0 # rest" using Sne by (cases S) auto
  let ?K = "takeWhile (\<lambda>r. fst c0 < fst r) rest"
  let ?T = "dropWhile (\<lambda>r. fst c0 < fst r) rest"
  let ?A = "proj (snd c0) (nrm (translate ?K))"
  let ?m = "maxr1 S"
  have fbC: "fbseg u (c0 # rest)" using dseg_fbseg[OF D] unfolding C .
  have sh: "nrm (translate S) = P (snd c0) ?A (nrm (translate ?T))"
    unfolding C by (rule NT_shape[OF fbC refl])
  have DC: "dseg u (c0 # rest)" using D unfolding C .
  have FC: "pfire u (nrm (translate (c0 # rest)))" using F unfolding C .
  have rsplit: "rest = ?K @ ?T" by simp
  have xs: "set (c0 # rest) = set (c0 # ?K) \<union> set ?T"
  proof -
    have "set rest = set ?K \<union> set ?T"
      by (metis rsplit set_append)
    thus ?thesis by auto
  qed
  show ?thesis
  proof (cases "snd c0 = ?m")
    case True
    have "snd (hd S) = maxr1 S" using True unfolding C by simp
    hence "\<not> pfire u (nrm (translate S))" by (rule E6_hdom[OF D])
    thus ?thesis using F by blast
  next
    case hl: False
    have hlt: "snd c0 < ?m"
      using maxr1_ub[of c0 S] hl unfolding C by simp
    show ?thesis
    proof (cases "?K \<noteq> [] \<and> maxr1 ?K = ?m")
      case Kmax: True
      have hltC: "snd c0 < maxr1 (c0 # rest)" using hlt unfolding C by simp
      from E6_nbcK[OF DC FC _ _ hltC] Kmax
      have Tnil: "?T = []" and uv: "u \<le> snd c0"
        and Kf: "pfire (snd c0) (nrm (translate ?K)) \<or> msfx ?K = ?K"
        using C by blast+
      have dsK: "dseg (snd c0) ?K"
        using fbseg_K_dseg[OF fbC] Kmax by blast
      have Aval: "?A = nrm (translate (msfx ?K))"
      proof (cases "pfire (snd c0) (nrm (translate ?K))")
        case True
        show ?thesis by (rule E6_value[OF dsK True])
      next
        case False
        have "msfx ?K = ?K" using Kf False by blast
        thus ?thesis using proj_nofire[OF False] by simp
      qed
      have rk: "rest = ?K" using rsplit Tnil by simp
      have meq: "msfx S = msfx ?K"
      proof -
        have "msfx S = dropWhile (\<lambda>c. snd c < ?m) S" by (simp add: msfx_def)
        also have "\<dots> = dropWhile (\<lambda>c. snd c < ?m) rest"
          unfolding C using hltC by simp
        also have "\<dots> = dropWhile (\<lambda>c. snd c < ?m) ?K" using rk by simp
        also have "\<dots> = msfx ?K" unfolding msfx_def using Kmax by auto
        finally show ?thesis .
      qed
      have mem: "nrm (translate (msfx S)) \<in> Gterm u (nrm (translate S))"
        unfolding sh meq Aval[symmetric] using uv by simp
      have hdms: "hdsub (nrm (translate (msfx S))) = ?m"
        using NT_msfx_hdsub[OF Sne] by simp
      obtain c' rest' where M': "msfx S = c' # rest'"
        using msfx_ne[OF Sne] by (cases "msfx S") auto
      obtain e f g where E: "nrm (translate (msfx S)) = P e f g"
        using NT_neZ unfolding M' by (cases "nrm (translate (c' # rest'))") auto
      have em: "e = ?m" using hdms unfolding E by simp
      have "\<not> olt (nrm (translate (msfx S))) (nrm (translate S))"
        unfolding sh E using em hlt by simp
      thus ?thesis using mem by blast
    next
      case nK: False
      have KleM: "maxr1 (c0 # ?K) \<le> ?m"
        unfolding maxr1_def
        by (intro Max_mono) (auto simp: C dest: set_takeWhileD)
      have noKwit: "\<And>x. x \<in> set (c0 # ?K) \<Longrightarrow> snd x \<noteq> ?m"
      proof
        fix x assume xin: "x \<in> set (c0 # ?K)" and xm: "snd x = ?m"
        have "x = c0 \<or> x \<in> set ?K" using xin by auto
        thus False
        proof
          assume "x = c0" thus False using xm hlt by simp
        next
          assume xK: "x \<in> set ?K"
          hence Kne: "?K \<noteq> []" by auto
          have "?m \<le> maxr1 ?K" using xK xm maxr1_ub by fastforce
          moreover have "maxr1 ?K \<le> ?m"
            unfolding maxr1_def
            by (intro Max_mono) (use Kne in \<open>auto simp: C dest: set_takeWhileD\<close>)
          ultimately show False using nK Kne by simp
        qed
      qed
      obtain xm where xm: "xm \<in> set S" "snd xm = ?m"
        using maxr1_in[OF Sne] by auto
      have xmT: "xm \<in> set ?T"
      proof -
        have "xm \<in> set (c0 # ?K) \<union> set ?T" using xm(1) xs unfolding C by blast
        moreover have "xm \<notin> set (c0 # ?K)" using noKwit xm(2) by blast
        ultimately show ?thesis by blast
      qed
      have Tne: "?T \<noteq> []" using xmT by (metis empty_iff empty_set)
      have mT: "maxr1 ?T = ?m"
      proof -
        have "?m \<le> maxr1 ?T" using maxr1_ub[OF xmT] xm(2) by simp
        moreover have "maxr1 ?T \<le> ?m"
          unfolding maxr1_def
          by (intro Max_mono) (use Tne in \<open>auto simp: C dest: set_dropWhileD\<close>)
        ultimately show ?thesis by simp
      qed
      have mlt: "maxr1 (c0 # ?K) < ?m"
      proof -
        have "maxr1 (c0 # ?K) \<noteq> ?m"
        proof
          assume eqm: "maxr1 (c0 # ?K) = ?m"
          have "?m \<in> snd ` set (c0 # ?K)"
            using maxr1_in[of "c0 # ?K"] eqm by simp
          then obtain x where xx: "x \<in> set (c0 # ?K)" and xsnd: "snd x = ?m" by force
          show False using noKwit[OF xx] xsnd by simp
        qed
        thus ?thesis using KleM by simp
      qed
      have mltC: "maxr1 (c0 # ?K) < maxr1 (c0 # rest)" using mlt unfolding C by simp
      from E6_memT[OF DC FC Tne mltC]
      have memT: "nrm (translate (msfx ?T)) \<in> Gterm u (nrm (translate ?T))"
        and vioT: "\<not> olt (nrm (translate (msfx ?T))) (nrm (translate (c0 # rest)))"
        by blast+
      have meq: "msfx S = msfx ?T"
      proof -
        have Ssplit: "S = (c0 # ?K) @ ?T" unfolding C by simp
        have bound: "\<forall>c \<in> set (c0 # ?K). snd c < maxr1 ?T"
        proof
          fix c assume "c \<in> set (c0 # ?K)"
          hence "snd c \<le> maxr1 (c0 # ?K)" using maxr1_ub by fast
          thus "snd c < maxr1 ?T" using mlt mT by simp
        qed
        show ?thesis unfolding Ssplit by (rule msfx_tail[OF Tne bound])
      qed
      have sub: "Gterm u (nrm (translate ?T)) \<subseteq> Gterm u (nrm (translate S))"
        unfolding sh by auto
      have m1: "nrm (translate (msfx S)) \<in> Gterm u (nrm (translate S))"
        using memT sub meq by auto
      have m2: "\<not> olt (nrm (translate (msfx S))) (nrm (translate S))"
        using vioT meq unfolding C by simp
      show ?thesis using m1 m2 by blast
    qed
  qed
qed

text \<open>\<open>Pred\<close> case of the step decrease, from \<open>nrm_snoc\<close>.\<close>

lemma nrm_step_dec_pred:
  assumes M: "M \<in> ST_PS" and L: "1 < Lng M"
    and br: "(entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)
             \<or> \<not> hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
  shows "olt (nrm (translate (M[n]))) (nrm (translate M))"
proof -
  from L have j1: "Lng M - 1 \<noteq> 0" by simp
  have MP: "M[n] = Pred M"
    using br
  proof
    assume "entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0"
    thus ?thesis using j1 by (simp add: oper_def Let_def)
  next
    assume "\<not> hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    thus ?thesis using j1 by (auto simp: oper_def Let_def)
  qed
  have Pb: "Pred M = butlast M" using L by (simp add: Pred_def)
  have ne: "M \<noteq> []" using L by auto
  have Msplit: "butlast M @ [last M] = M" using ne by simp
  have bne: "butlast M \<noteq> []" using L by (cases M) auto
  have "olt (nrm (translate (butlast M))) (nrm (translate (butlast M @ [last M])))"
    by (rule nrm_snoc) (use Msplit M bne in auto)
  thus ?thesis using MP Pb Msplit by simp
qed

end
