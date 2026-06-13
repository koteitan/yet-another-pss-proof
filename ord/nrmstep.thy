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

lemma block_head_min:
  assumes hp: "hasParent M i1 j1" and j0d: "j0 = parent M i1 j1"
  shows "\<forall>k. j0 < k \<and> k \<le> j1 \<longrightarrow> entry M 0 j0 < entry M 0 k"
proof -
  have nR: "nextR M i1 j0 j1" unfolding j0d by (rule parent_nextR[OF hp])
  have "(nextrel0 M)\<^sup>*\<^sup>* j0 j1"
  proof (cases "i1 = 0")
    case True
    hence "nextrel0 M j0 j1" using nR unfolding nextR_def by simp
    thus ?thesis by blast
  next
    case False
    hence "nextrel1 M j0 j1" using nR unfolding nextR_def by simp
    thus ?thesis unfolding nextrel1_def le0_def by blast
  qed
  thus ?thesis by (rule le0_interval_gt)
qed


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
proof -
  note ST = assms(1) and j1len = assms(2) and j0j1 = assms(3) and i1d = assms(4)
    and hp = assms(5) and j0d = assms(6) and d0d = assms(7) and qL = assms(8)
    and PM = assms(9) and rL = assms(10) and qr = assms(11) and rlvl = assms(12)
    and rlast = assms(13)
  show ?thesis
  proof (cases "r' = 0")
    case True
    hence "q = 0" using qr by simp
    thus ?thesis using True by simp
  next
    case rpos: False
    have hm0: "\<forall>k. j0 < k \<and> k \<le> j1 \<longrightarrow> entry M 0 j0 < entry M 0 k"
      by (rule block_head_min[OF hp j0d])
    have q0: "q = 0"
    proof (rule ccontr)
      assume "q \<noteq> 0"
      hence qpos: "0 < q" by simp
      have "entry M 0 (j0 + q) \<le> entry M 0 (j0 + 0)" using PM qpos by blast
      hence le: "entry M 0 (j0 + q) \<le> entry M 0 j0" by simp
      have "j0 < j0 + q \<and> j0 + q \<le> j1"
        using qpos qL by (simp add: less_diff_conv add.commute)
      hence "entry M 0 j0 < entry M 0 (j0 + q)" using hm0 by blast
      thus False using le by simp
    qed
    have rj1: "j0 + r' < j1"
      using rL by (simp add: less_diff_conv add.commute)
    have e0r: "entry M 0 (j0 + r') = entry M 0 j0 + d0 - 1"
      using rlvl unfolding q0 by simp
    have e0rgt: "entry M 0 j0 < entry M 0 (j0 + r')"
    proof -
      have "j0 < j0 + r' \<and> j0 + r' \<le> j1" using rpos rj1 by simp
      thus ?thesis using hm0 by blast
    qed
    have d02: "2 \<le> d0" using e0r e0rgt by arith
    have i1one: "i1 = 1"
      using idx1_le[of M j1] d0d d02 i1d by (cases i1) auto
    have nR: "nextR M i1 j0 j1" unfolding j0d by (rule parent_nextR[OF hp])
    have nR1: "nextrel1 M j0 j1" using nR unfolding i1one nextR_def by simp
    have e1j: "entry M 1 j0 < entry M 1 j1" using nR1 unfolding nextrel1_def by blast
    have e0j1d: "entry M 0 j1 = entry M 0 j0 + d0"
    proof -
      have dd: "d0 = entry M 0 j1 - entry M 0 j0" using d0d i1one by simp
      show ?thesis
      proof (cases "entry M 0 j0 \<le> entry M 0 j1")
        case True thus ?thesis using dd by simp
      next
        case False
        hence "d0 = 0" using dd by simp
        thus ?thesis using d02 by simp
      qed
    qed
    have n0: "nextrel0 M (j0 + r') j1"
      unfolding nextrel0_def
    proof (intro conjI allI impI)
      show "j0 + r' < Lng M" using rj1 j1len by simp
      show "j1 < Lng M" using j1len by simp
      show "j0 + r' < j1" by (rule rj1)
      show "entry M 0 (j0 + r') < entry M 0 j1"
        using e0r e0j1d d02 by arith
    next
      fix j assume jb: "j0 + r' < j \<and> j < j1"
      have j0j: "j0 \<le> j" using jb by simp
      have jj: "j0 + (j - j0) = j" by (rule le_add_diff_inverse[OF j0j])
      have rr1: "r' < j - j0"
        using jb by (simp add: less_diff_conv add.commute)
      have rr2: "j - j0 < j1 - j0"
        using jb j0j by (simp add: diff_less_mono)
      have "entry M 0 (j0 + q) + d0 - 1 < entry M 0 (j0 + (j - j0))"
        using rlast rr1 rr2 by blast
      hence "entry M 0 j0 + d0 - 1 < entry M 0 j" unfolding q0 jj by simp
      thus "entry M 0 j1 \<le> entry M 0 j" using e0j1d d02 by arith
    qed
    have le0r: "le0 M (j0 + r') j1"
      unfolding le0_def using n0 j1len rj1 by (auto intro: r_into_rtranclp)
    have anc: "entry M 1 j1 \<le> entry M 1 (j0 + r')"
    proof -
      have "j0 < j0 + r'" using rpos by simp
      thus ?thesis using nR1 le0r unfolding nextrel1_def by blast
    qed
    show ?thesis unfolding q0 using e1j anc by simp
  qed
qed

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

text \<open>\<open>ginv\<close>: the closed-window row-1 bound.  In any dominated window
  \<open>pp # S\<close> of a standard host whose opening run returns to the opener's
  level (\<open>S\<close> contains a later column at level \<open>\<le> fst (hd S)\<close>), every row-1
  value in \<open>S\<close> is bounded by \<open>max (snd pp) (snd (hd S))\<close>.  (Empirically
  exact: closure+1 14638 / closure+2 42489 closed windows, zero violations.
  The bound is acausal — a later return constrains earlier columns — so it
  is proved by generation induction like \<open>r1ok\<close>.)\<close>

definition ginv :: "pairseq \<Rightarrow> bool" where
  "ginv H \<longleftrightarrow> (\<forall>p n t l.
     Suc p + n < length H \<longrightarrow>
     (\<forall>k. p < k \<and> k \<le> Suc p + n \<longrightarrow> fst (H ! p) < fst (H ! k)) \<longrightarrow>
     0 < t \<longrightarrow> t \<le> n \<longrightarrow> fst (H ! (Suc p + t)) \<le> fst (H ! Suc p) \<longrightarrow>
     p < l \<longrightarrow> l \<le> Suc p + t \<longrightarrow>
     snd (H ! l) \<le> max (snd (H ! p)) (snd (H ! Suc p)))"

lemma ginv_diagSeq: "ginv (diagSeq 0 v)"
proof -
  have nth: "\<And>j. j < length (diagSeq 0 v) \<Longrightarrow> diagSeq 0 v ! j = (j, j)"
    unfolding diagSeq_def by (simp del: upt_Suc)
  show ?thesis
    unfolding ginv_def
  proof (intro allI impI)
    fix p n t l
    assume bnd: "Suc p + n < length (diagSeq 0 v)"
      and dom: "\<forall>k. p < k \<and> k \<le> Suc p + n \<longrightarrow>
                  fst (diagSeq 0 v ! p) < fst (diagSeq 0 v ! k)"
      and t0: "0 < t" and tn: "t \<le> n"
      and cl: "fst (diagSeq 0 v ! (Suc p + t)) \<le> fst (diagSeq 0 v ! Suc p)"
      and pl: "p < l" and ln: "l \<le> Suc p + t"
    have lt1: "Suc p + t < length (diagSeq 0 v)" using bnd tn by simp
    have lt2: "Suc p < length (diagSeq 0 v)" using bnd by simp
    have False using cl t0 unfolding nth[OF lt1] nth[OF lt2] by simp
    thus "snd (diagSeq 0 v ! l)
        \<le> max (snd (diagSeq 0 v ! p)) (snd (diagSeq 0 v ! Suc p))" ..
  qed
qed

lemma ginv_take:
  assumes G: "ginv M" shows "ginv (take m M)"
  unfolding ginv_def
proof (intro allI impI)
  fix p n t l
  assume bnd: "Suc p + n < length (take m M)"
    and dom: "\<forall>k. p < k \<and> k \<le> Suc p + n \<longrightarrow>
                fst (take m M ! p) < fst (take m M ! k)"
    and t0: "0 < t" and tn: "t \<le> n"
    and cl: "fst (take m M ! (Suc p + t)) \<le> fst (take m M ! Suc p)"
    and pl: "p < l" and ln: "l \<le> Suc p + t"
  have lnn: "l \<le> Suc p + n" using ln tn by simp
  have bm: "Suc p + n < m" and bM: "Suc p + n < length M" using bnd by auto
  have ntk: "\<And>j. j \<le> Suc p + n \<Longrightarrow> take m M ! j = M ! j"
    using bm by (auto intro: nth_take)
  have dom': "\<forall>k. p < k \<and> k \<le> Suc p + n \<longrightarrow> fst (M ! p) < fst (M ! k)"
  proof (intro allI impI)
    fix k assume kk: "p < k \<and> k \<le> Suc p + n"
    have "fst (take m M ! p) < fst (take m M ! k)" using dom kk by blast
    thus "fst (M ! p) < fst (M ! k)" using ntk kk by simp
  qed
  have cl': "fst (M ! (Suc p + t)) \<le> fst (M ! Suc p)"
    using cl ntk tn by simp
  have "snd (M ! l) \<le> max (snd (M ! p)) (snd (M ! Suc p))"
    using G[unfolded ginv_def, rule_format, of p n t l]
      bM dom' t0 tn cl' pl ln by blast
  thus "snd (take m M ! l) \<le> max (snd (take m M ! p)) (snd (take m M ! Suc p))"
    using ntk pl lnn by simp
qed

lemma ginv_butlast: "ginv M \<Longrightarrow> ginv (butlast M)"
  using ginv_take[of M "length M - 1"] by (simp add: butlast_conv_take)

text \<open>The two regional halves of the cross-copy window preservation
  (case map: memo 続36).  Prefix-anchored windows transport to \<open>M\<close>-windows
  except the \<open>p = j0 - 1, d0 = 0\<close> copy-head-tie seam; copy-anchored windows
  transport via the block twin except the \<open>qP > 0\<close> crossing seam.\<close>

text \<open>Row-0 parenthood strictly raises the level; hence a positive-index
  parent (\<open>nextrel1\<close>, whose \<open>le0\<close>-ancestry is proper) sits strictly below its
  child, and the exact-copy branch \<open>d0 = 0\<close> forces \<open>i1 = 0\<close>.\<close>

lemma rtran_nextrel0_e0: "(nextrel0 M)\<^sup>*\<^sup>* a b \<Longrightarrow> entry M 0 a \<le> entry M 0 b"
proof (induction rule: rtranclp_induct)
  case base show ?case by simp
next
  case (step y z)
  have "entry M 0 y < entry M 0 z" using step.hyps(2) unfolding nextrel0_def by blast
  thus ?case using step.IH by simp
qed

lemma nextrel1_e0_lt:
  assumes "nextrel1 M j0 j1"
  shows "entry M 0 j0 < entry M 0 j1"
proof -
  have le0: "le0 M j0 j1" and lt: "j0 < j1" using assms unfolding nextrel1_def by blast+
  have rt: "(nextrel0 M)\<^sup>*\<^sup>* j0 j1" using le0 unfolding le0_def by blast
  from rtranclpD[OF rt] lt obtain z where z: "nextrel0 M j0 z" "(nextrel0 M)\<^sup>*\<^sup>* z j1"
    by (metis less_irrefl tranclpD)
  have "entry M 0 j0 < entry M 0 z" using z(1) unfolding nextrel0_def by blast
  also have "\<dots> \<le> entry M 0 j1" by (rule rtran_nextrel0_e0[OF z(2)])
  finally show ?thesis .
qed

text \<open>(OSC discipline, the frozen oscillation cores; memo 続61/続63補/続64/続78.
  The bad-block forms GCD/O2 are now \<^emph>\<open>derived\<close> from universal
  \<open>nextrel0\<close>-window cores (any window \<open>a = parent0(om)\<close> with a zero-row-1
  closing column \<open>om\<close> — position-local, hence take-stable):
  \<^item> GCDV: the gap-clear level+1 child of a positive-row-1 column inside such
    a window strictly drops in row 1 (closure+3: 118667 instances, zero
    violations);
  \<^item> O2V: if the window head has row 1 zero, is dominated by its immediate
    predecessor, and some interior column attains row 1 one, the predecessor
    already carries at least one (closure+3: 66088, zero violations);
  \<^item> O1P: a \<^emph>\<open>positive\<close>-row-1 head of an \<open>i1 = 0\<close> bad block bounds the whole
    block interior (closure+3: 16901 blocks, zero violations; the universal
    \<open>om\<close>-window analogue is false — last-column anchoring is essential).\<close>

lemma ginv_GCDV:
  assumes "M \<in> ST_PS"
    and "om < Lng M"
    and "entry M 0 a < entry M 0 om"
    and "\<forall>j. a < j \<and> j < om \<longrightarrow> entry M 0 om \<le> entry M 0 j"
    and "entry M 1 om = 0"
    and "a < w" and "w < x" and "x < om"
    and "0 < entry M 1 w"
    and "entry M 0 x = Suc (entry M 0 w)"
    and "\<forall>t. w < t \<and> t < x \<longrightarrow> entry M 0 x \<le> fst (M ! t)"
  shows "entry M 1 x < entry M 1 w"
  sorry

lemma ginv_O2V:
  assumes "M \<in> ST_PS"
    and "om < Lng M"
    and "entry M 0 a < entry M 0 om"
    and "\<forall>j. a < j \<and> j < om \<longrightarrow> entry M 0 om \<le> entry M 0 j"
    and "entry M 1 om = 0"
    and "entry M 1 a = 0"
    and "0 < a" and "fst (M ! (a - 1)) < entry M 0 a"
    and "a < r" and "r < om"
    and "entry M 1 r = Suc (entry M 1 a)"
  shows "Suc (entry M 1 a) \<le> snd (M ! (a - 1))"
  sorry

lemma ginv_O1P:
  assumes "M \<in> ST_PS"
    and "j1 = Lng M - 1" and "j1 \<noteq> 0"
    and "\<not> (entry M 0 j1 = 0 \<and> entry M 1 j1 = 0)"
    and "idx1 M j1 = 0" and "hasParent M 0 j1"
    and "j0 = parent M 0 j1"
    and "0 < entry M 1 j0"
    and "j0 < l" and "l < j1"
  shows "entry M 1 l \<le> entry M 1 j0"
  sorry

lemma ginv_GCD:
  assumes "M \<in> ST_PS"
    and "j1 = Lng M - 1" and "j1 \<noteq> 0"
    and "\<not> (entry M 0 j1 = 0 \<and> entry M 1 j1 = 0)"
    and "idx1 M j1 = 0" and "hasParent M 0 j1"
    and "j0 = parent M 0 j1"
    and "j0 < w" and "w < x" and "x < j1"
    and "0 < entry M 1 w"
    and "entry M 0 x = Suc (entry M 0 w)"
    and "\<forall>t. w < t \<and> t < x \<longrightarrow> entry M 0 x \<le> fst (M ! t)"
  shows "entry M 1 x < entry M 1 w"
proof -
  have n0: "nextrel0 M j0 j1"
    using parent_nextR[OF assms(6)] unfolding assms(7)[symmetric] nextR_def
    by simp
  have j1L: "j1 < Lng M" and e0lt: "entry M 0 j0 < entry M 0 j1"
    using n0 unfolding nextrel0_def by blast+
  have gap: "\<forall>j. j0 < j \<and> j < j1 \<longrightarrow> entry M 0 j1 \<le> entry M 0 j"
    using n0 unfolding nextrel0_def by blast
  have s0: "entry M 1 j1 = 0"
    using assms(5) unfolding idx1_def by (simp split: if_splits)
  show ?thesis
    by (rule ginv_GCDV[OF assms(1) j1L e0lt gap s0 assms(8) assms(9)
          assms(10) assms(11) assms(12) assms(13)])
qed

text \<open>(CT) Tight-node child drop (memo 続52): on an exact-copy dominated
  tail, a child of a node that has already spent the +1 budget drops back to
  the anchor level (closure+2: the 7 realized tight-parent instances, zero
  violations).\<close>

lemma ginv_CT:
  assumes ST: "M \<in> ST_PS"
    and j1d: "j1 = Lng M - 1" and j1nz: "j1 \<noteq> 0"
    and Fz: "\<not> (entry M 0 j1 = 0 \<and> entry M 1 j1 = 0)"
    and i1d: "i1 = idx1 M j1" and hp: "hasParent M i1 j1"
    and j0d: "j0 = parent M i1 j1"
    and d0d: "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
    and d00: "d0 = 0"
    and qab: "qa < j1 - j0"
    and anc: "\<forall>q. qa < q \<and> q < j1 - j0 \<longrightarrow> entry M 0 (j0 + qa) < entry M 0 (j0 + q)"
    and qw: "qa < w" and wb: "w < j1 - j0" and qx: "qa < x" and xb: "x < j1 - j0"
    and wx: "w < x"
    and chld: "Suc (entry M 0 (j0 + w)) = entry M 0 (j0 + x)"
    and gap: "\<forall>r. j0 + w < r \<and> r < j0 + x \<longrightarrow> entry M 0 (j0 + x) \<le> fst (M ! r)"
    and tight: "entry M 1 (j0 + w) = Suc (entry M 1 (j0 + qa))"
  shows "entry M 1 (j0 + x) \<le> entry M 1 (j0 + qa)"
proof (cases "i1 = 0")
  case False
  hence pos: "0 < i1" by simp
  have nR: "nextR M i1 j0 j1" unfolding j0d by (rule parent_nextR[OF hp])
  hence "nextrel1 M j0 j1" unfolding nextR_def using False by simp
  hence "entry M 0 j0 < entry M 0 j1" by (rule nextrel1_e0_lt)
  hence "d0 \<noteq> 0" unfolding d0d using pos by simp
  thus ?thesis using d00 by simp
next
  case True
  have hp0: "hasParent M 0 j1" and j0d0: "j0 = parent M 0 j1"
    using hp j0d unfolding i1d[symmetric] True by auto
  have i10: "idx1 M j1 = 0" using i1d True by simp
  have jlt: "j0 < j1"
  proof -
    have nR: "nextR M i1 j0 j1" unfolding j0d by (rule parent_nextR[OF hp])
    hence "nextrel0 M j0 j1" unfolding nextR_def using True i1d by simp
    thus ?thesis unfolding nextrel0_def by blast
  qed
  have wgt: "j0 < j0 + w" using qw by simp
  have wxa: "j0 + w < j0 + x" using wx by simp
  have xlt: "j0 + x < j1" using xb jlt by simp
  have wpos: "0 < entry M 1 (j0 + w)" using tight by simp
  have chld': "entry M 0 (j0 + x) = Suc (entry M 0 (j0 + w))" using chld by simp
  have gap': "\<forall>t. j0 + w < t \<and> t < j0 + x \<longrightarrow> entry M 0 (j0 + x) \<le> fst (M ! t)"
    using gap by blast
  have "entry M 1 (j0 + x) < entry M 1 (j0 + w)"
    by (rule ginv_GCD[OF ST j1d j1nz Fz i10 hp0 j0d0 wgt wxa xlt wpos chld' gap'])
  thus ?thesis using tight by simp
qed

text \<open>(BT-WRAP-U) The untied exact-copy wrap bounds (memo 続49): with
  \<open>d0 = 0\<close>, a level-anchored dominated block tail is bounded without any tie
  (closure+2: 21537 / T3 5867, zero violations).\<close>

lemma ginv_BTWRAPU:
  assumes "M \<in> ST_PS"
    and "j1 = Lng M - 1" and "j1 \<noteq> 0"
    and "\<not> (entry M 0 j1 = 0 \<and> entry M 1 j1 = 0)"
    and "i1 = idx1 M j1" and "hasParent M i1 j1"
    and "j0 = parent M i1 j1"
    and "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
    and "d0 = 0"
    and "qa < j1 - j0"
    and "entry M 0 j0 \<le> entry M 0 (j0 + qa)"
    and "\<forall>q. qa < q \<and> q < j1 - j0 \<longrightarrow> entry M 0 (j0 + qa) < entry M 0 (j0 + q)"
    and "qa < q" and "q < j1 - j0"
  shows "entry M 1 (j0 + q) \<le> Suc (entry M 1 (j0 + qa))"
proof -
  note ST = assms(1) and j1d = assms(2) and j1nz = assms(3) and Fz = assms(4)
    and i1d = assms(5) and hp = assms(6) and j0d = assms(7) and d0d = assms(8)
    and d00 = assms(9) and qaL = assms(10) and e0c = assms(11) and dom = assms(12)
  have lenM: "length M = Suc j1" using j1d j1nz by (cases M) auto
  have j1len: "j1 < length M" using lenM by simp
  have R: "r1ok M" using r1ok_ST_PS[OF ST] .
  have main: "\<And>x. qa < x \<Longrightarrow> x < j1 - j0 \<Longrightarrow>
      entry M 1 (j0 + x) \<le> Suc (entry M 1 (j0 + qa))"
  proof -
    fix x
    show "qa < x \<Longrightarrow> x < j1 - j0 \<Longrightarrow>
        entry M 1 (j0 + x) \<le> Suc (entry M 1 (j0 + qa))"
    proof (induction x rule: less_induct)
      case (less x)
      have xw: "qa < x" "x < j1 - j0" using less.prems by auto
      have xM: "j0 + x < length M" using xw(2) j1len by arith
      have xpos: "0 < fst (M ! (j0 + x))"
      proof -
        have "entry M 0 (j0 + qa) < entry M 0 (j0 + x)" using dom xw by blast
        thus ?thesis unfolding entry_def by simp
      qed
      obtain k where k: "k < j0 + x" "Suc (fst (M ! k)) = fst (M ! (j0 + x))"
          "\<forall>l. k < l \<and> l < j0 + x \<longrightarrow> fst (M ! (j0 + x)) \<le> fst (M ! l)"
          "snd (M ! (j0 + x)) \<le> Suc (snd (M ! k))"
        using R[unfolded r1ok_def, rule_format, OF xM xpos] by blast
      have kanch: "j0 + qa \<le> k"
      proof (rule ccontr)
        assume "\<not> j0 + qa \<le> k"
        hence kqa: "k < j0 + qa" by simp
        have inq: "k < j0 + qa \<and> j0 + qa < j0 + x" using kqa xw(1) by simp
        have "fst (M ! (j0 + x)) \<le> fst (M ! (j0 + qa))" using k(3) inq by blast
        moreover have "entry M 0 (j0 + qa) < entry M 0 (j0 + x)" using dom xw by blast
        ultimately show False unfolding entry_def by simp
      qed
      show ?case
      proof (cases "k = j0 + qa")
        case True
        have "snd (M ! (j0 + x)) \<le> Suc (snd (M ! (j0 + qa)))" using k(4) True by simp
        thus ?thesis unfolding entry_def by simp
      next
        case False
        hence kin: "j0 + qa < k" using kanch by simp
        define w where "w = k - j0"
        have wk: "k = j0 + w" unfolding w_def using kin by arith
        have ww: "qa < w" unfolding w_def using kin by arith
        have wx: "w < x" unfolding w_def using k(1) kin by arith
        have wL: "w < j1 - j0" using wx xw(2) by arith
        have IH: "entry M 1 (j0 + w) \<le> Suc (entry M 1 (j0 + qa))"
          by (rule less.IH[OF wx ww wL])
        show ?thesis
        proof (cases "entry M 1 (j0 + w) \<le> entry M 1 (j0 + qa)")
          case True
          have "snd (M ! (j0 + x)) \<le> Suc (snd (M ! (j0 + w)))" using k(4) wk by simp
          hence "entry M 1 (j0 + x) \<le> Suc (entry M 1 (j0 + w))"
            unfolding entry_def by simp
          thus ?thesis using True by simp
        next
          case False
          have tight: "entry M 1 (j0 + w) = Suc (entry M 1 (j0 + qa))"
            using False IH by simp
          have e0wx: "Suc (entry M 0 (j0 + w)) = entry M 0 (j0 + x)"
            using k(2) wk unfolding entry_def by simp
          have gap: "\<forall>r. j0 + w < r \<and> r < j0 + x \<longrightarrow>
              entry M 0 (j0 + x) \<le> fst (M ! r)"
          proof (intro allI impI)
            fix r assume rr: "j0 + w < r \<and> r < j0 + x"
            have "fst (M ! (j0 + x)) \<le> fst (M ! r)" using k(3) rr wk by simp
            thus "entry M 0 (j0 + x) \<le> fst (M ! r)" unfolding entry_def by simp
          qed
          have "entry M 1 (j0 + x) \<le> entry M 1 (j0 + qa)"
            by (rule ginv_CT[OF ST j1d j1nz Fz i1d hp j0d d0d d00 qaL dom
                  ww wL xw(1) xw(2) wx e0wx gap tight])
          thus ?thesis by simp
        qed
      qed
    qed
  qed
  show ?thesis by (rule main[OF assms(13) assms(14)])
qed

text \<open>(NT3) Under a head tie the +1 budget is never attained on an
  exact-copy dominated tail (closure+2: 16783 elements, zero attainments).\<close>

lemma ginv_NT3:
  assumes "M \<in> ST_PS"
    and "j1 = Lng M - 1" and "j1 \<noteq> 0"
    and "\<not> (entry M 0 j1 = 0 \<and> entry M 1 j1 = 0)"
    and "i1 = idx1 M j1" and "hasParent M i1 j1"
    and "j0 = parent M i1 j1"
    and "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
    and "d0 = 0"
    and "qa < j1 - j0"
    and "\<forall>q. qa < q \<and> q < j1 - j0 \<longrightarrow> entry M 0 (j0 + qa) < entry M 0 (j0 + q)"
    and "entry M 1 (j0 + Suc qa) = entry M 1 (j0 + qa)"
    and "qa < q" and "q < j1 - j0"
  shows "entry M 1 (j0 + q) \<noteq> Suc (entry M 1 (j0 + qa))"
  sorry

lemma ginv_BTWRAPU3:
  assumes "M \<in> ST_PS"
    and "j1 = Lng M - 1" and "j1 \<noteq> 0"
    and "\<not> (entry M 0 j1 = 0 \<and> entry M 1 j1 = 0)"
    and "i1 = idx1 M j1" and "hasParent M i1 j1"
    and "j0 = parent M i1 j1"
    and "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
    and "d0 = 0"
    and "qa < j1 - j0"
    and "entry M 0 j0 \<le> entry M 0 (j0 + qa)"
    and "\<forall>q. qa < q \<and> q < j1 - j0 \<longrightarrow> entry M 0 (j0 + qa) < entry M 0 (j0 + q)"
    and "entry M 1 (j0 + Suc qa) = entry M 1 (j0 + qa)"
    and "qa < q" and "q < j1 - j0"
  shows "entry M 1 (j0 + q) \<le> entry M 1 (j0 + qa)"
proof -
  have "entry M 1 (j0 + q) \<le> Suc (entry M 1 (j0 + qa))"
    by (rule ginv_BTWRAPU[OF assms(1-8) assms(9) assms(10) assms(11) assms(12)
          assms(14) assms(15)])
  moreover have "entry M 1 (j0 + q) \<noteq> Suc (entry M 1 (j0 + qa))"
    by (rule ginv_NT3[OF assms(1-8) assms(9) assms(10) assms(12) assms(13)
          assms(14) assms(15)])
  ultimately show ?thesis by simp
qed

lemma ginv_O1:
  assumes "M \<in> ST_PS"
    and "j1 = Lng M - 1" and "j1 \<noteq> 0"
    and "\<not> (entry M 0 j1 = 0 \<and> entry M 1 j1 = 0)"
    and "idx1 M j1 = 0" and "hasParent M 0 j1"
    and "j0 = parent M 0 j1"
    and "j0 < r" and "r < j1"
  shows "entry M 1 r \<le> Suc (entry M 1 j0)"
proof -
  have n0: "nextrel0 M j0 j1"
    using parent_nextR[OF assms(6)] assms(7) unfolding nextR_def by simp
  have jlt: "j0 < j1" and e0lt: "entry M 0 j0 < entry M 0 j1"
    using n0 unfolding nextrel0_def by blast+
  have gapc: "\<And>j. j0 < j \<Longrightarrow> j < j1 \<Longrightarrow> entry M 0 j1 \<le> entry M 0 j"
    using n0 unfolding nextrel0_def by blast
  have dom: "\<forall>q. 0 < q \<and> q < j1 - j0 \<longrightarrow> entry M 0 (j0 + 0) < entry M 0 (j0 + q)"
  proof (intro allI impI)
    fix q assume q: "0 < q \<and> q < j1 - j0"
    hence b1: "j0 < j0 + q" and b2: "j0 + q < j1" by auto
    have "entry M 0 j1 \<le> entry M 0 (j0 + q)" using gapc[OF b1 b2] .
    thus "entry M 0 (j0 + 0) < entry M 0 (j0 + q)" using e0lt by simp
  qed
  have d0d: "(0::nat) = (if 0 < (0::nat) then entry M 0 j1 - entry M 0 j0 else 0)"
    by simp
  have qaL: "(0::nat) < j1 - j0" using jlt by simp
  have e0c: "entry M 0 j0 \<le> entry M 0 (j0 + 0)" by simp
  have qpos: "0 < r - j0" and qb: "r - j0 < j1 - j0" using assms(8,9) by auto
  have "entry M 1 (j0 + (r - j0)) \<le> Suc (entry M 1 (j0 + 0))"
    by (rule ginv_BTWRAPU[OF assms(1) assms(2) assms(3) assms(4) assms(5)[symmetric]
          assms(6) assms(7) d0d refl qaL e0c dom qpos qb])
  thus ?thesis using assms(8) by simp
qed

lemma ginv_O2:
  assumes "M \<in> ST_PS"
    and "j1 = Lng M - 1" and "j1 \<noteq> 0"
    and "\<not> (entry M 0 j1 = 0 \<and> entry M 1 j1 = 0)"
    and "idx1 M j1 = 0" and "hasParent M 0 j1"
    and "j0 = parent M 0 j1"
    and "0 < j0" and "fst (M ! (j0 - 1)) < entry M 0 j0"
    and "j0 < r" and "r < j1"
    and "entry M 1 r = Suc (entry M 1 j0)"
  shows "Suc (entry M 1 j0) \<le> snd (M ! (j0 - 1))"
proof (cases "entry M 1 j0 = 0")
  case True
  have n0: "nextrel0 M j0 j1"
    using parent_nextR[OF assms(6)] unfolding assms(7)[symmetric] nextR_def
    by simp
  have j1L: "j1 < Lng M" and e0lt: "entry M 0 j0 < entry M 0 j1"
    using n0 unfolding nextrel0_def by blast+
  have gap: "\<forall>j. j0 < j \<and> j < j1 \<longrightarrow> entry M 0 j1 \<le> entry M 0 j"
    using n0 unfolding nextrel0_def by blast
  have s0: "entry M 1 j1 = 0"
    using assms(5) unfolding idx1_def by (simp split: if_splits)
  show ?thesis
    by (rule ginv_O2V[OF assms(1) j1L e0lt gap s0 True assms(8) assms(9)
          assms(10) assms(11) assms(12)])
next
  case False
  hence pos: "0 < entry M 1 j0" by simp
  have "entry M 1 r \<le> entry M 1 j0"
    by (rule ginv_O1P[OF assms(1) assms(2) assms(3) assms(4) assms(5)
          assms(6) assms(7) pos assms(10) assms(11)])
  thus ?thesis using assms(12) by simp
qed

text \<open>(GAP) In a dominated exact-copy branch, any block column whose row 1
  exceeds the head's is bounded by the dominating prefix predecessor —
  derived: O1 pins the exceeder to exactly head-plus-one, O2 bounds it by
  the predecessor; a positive \<open>i1\<close> contradicts \<open>d0 = 0\<close>.\<close>

lemma ginv_GAP:
  assumes ST: "M \<in> ST_PS"
    and j1d: "j1 = Lng M - 1" and j1nz: "j1 \<noteq> 0"
    and Fz: "\<not> (entry M 0 j1 = 0 \<and> entry M 1 j1 = 0)"
    and i1d: "i1 = idx1 M j1" and hp: "hasParent M i1 j1"
    and j0d: "j0 = parent M i1 j1"
    and d0d: "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
    and d00: "d0 = 0" and j0pos: "0 < j0"
    and domp: "fst (M ! (j0 - 1)) < entry M 0 j0"
    and qb: "q < j1 - j0"
    and exc: "entry M 1 j0 < entry M 1 (j0 + q)"
  shows "entry M 1 (j0 + q) \<le> snd (M ! (j0 - 1))"
proof (cases "i1 = 0")
  case False
  hence pos: "0 < i1" by simp
  have nR: "nextR M i1 j0 j1" unfolding j0d by (rule parent_nextR[OF hp])
  hence "nextrel1 M j0 j1" unfolding nextR_def using False by simp
  hence "entry M 0 j0 < entry M 0 j1" by (rule nextrel1_e0_lt)
  hence "d0 \<noteq> 0" unfolding d0d using pos by simp
  thus ?thesis using d00 by simp
next
  case True
  have hp0: "hasParent M 0 j1" and j0d0: "j0 = parent M 0 j1"
    using hp j0d unfolding i1d[symmetric] True by auto
  have i10: "idx1 M j1 = 0" using i1d True by simp
  have qpos: "0 < q" using exc by (cases q) auto
  have jlt: "j0 < j1"
  proof -
    have nR: "nextR M i1 j0 j1" unfolding j0d by (rule parent_nextR[OF hp])
    hence "nextrel0 M j0 j1" unfolding nextR_def using True i1d by simp
    thus ?thesis unfolding nextrel0_def by blast
  qed
  have rlt: "j0 + q < j1" using qb jlt by simp
  have rgt: "j0 < j0 + q" using qpos by simp
  have le1: "entry M 1 (j0 + q) \<le> Suc (entry M 1 j0)"
    by (rule ginv_O1[OF ST j1d j1nz Fz i10 hp0 j0d0 rgt rlt])
  have eq1: "entry M 1 (j0 + q) = Suc (entry M 1 j0)" using le1 exc by simp
  show ?thesis
    using ginv_O2[OF ST j1d j1nz Fz i10 hp0 j0d0 j0pos domp rgt rlt eq1] eq1 by simp
qed

text \<open>(GBLK0) The \<open>d0 = 0\<close> copy-head-tie seam: with an exact-copy bad branch
  whose block head is dominated by its immediate predecessor, the block's
  row-1 values are bounded by that predecessor and the block head.
  (Empirically exact: closure+1, 1549 instances, zero violations; the
  \<open>\<le> e1j0\<close>-only form is false — 32 counterexamples need the max.)\<close>

lemma ginv_GBLK0:
  assumes "M \<in> ST_PS"
    and "j1 = Lng M - 1" and "j1 \<noteq> 0"
    and "\<not> (entry M 0 j1 = 0 \<and> entry M 1 j1 = 0)"
    and "i1 = idx1 M j1" and "hasParent M i1 j1"
    and "j0 = parent M i1 j1"
    and "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
    and "d0 = 0" and "0 < j0"
    and "fst (M ! (j0 - 1)) < entry M 0 j0"
    and "q < j1 - j0"
  shows "entry M 1 (j0 + q) \<le> max (snd (M ! (j0 - 1))) (entry M 1 j0)"
proof (cases "entry M 1 (j0 + q) \<le> entry M 1 j0")
  case True
  thus ?thesis by simp
next
  case False
  hence gt: "entry M 1 j0 < entry M 1 (j0 + q)" by simp
  have q0: "q \<noteq> 0"
  proof
    assume "q = 0"
    thus False using gt by simp
  qed
  have "entry M 1 (j0 + q) \<le> snd (M ! (j0 - 1))"
    by (rule ginv_GAP[OF assms(1-8) assms(9) assms(10) assms(11) assms(12) gt])
  thus ?thesis by simp
qed

text \<open>(cross, frozen) Stop-restricted windows on the oper-bad image, queried
  at or beyond the block head: the crossing content of the \<open>ginv\<close>
  preservation in one X-side fact (implied by the closure+3 audit of the
  restricted \<open>ginv\<close> form: 0 violations on 95182 hosts; the prefix-anchored
  subset audited directly, 0/491080).\<close>

lemma ginv_ob_cross:
  assumes G: "ginv M" and B: "blockok 0 M" and ST: "M \<in> ST_PS" and n1: "1 \<le> n"
    and j1d: "j1 = Lng M - 1" and j1nz: "j1 \<noteq> 0"
    and Fz: "\<not> (entry M 0 j1 = 0 \<and> entry M 1 j1 = 0)"
    and i1d: "i1 = idx1 M j1" and hp: "hasParent M i1 j1"
    and j0d: "j0 = parent M i1 j1"
    and d0d: "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
    and opeq: "X = take j0 M @ concat (map (\<lambda>k.
           map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j)) [j0..<j1]) [0..<n])"
    and bnd: "Suc p + N < length X"
    and dom: "\<forall>k. p < k \<and> k \<le> Suc p + N \<longrightarrow> fst (X ! p) < fst (X ! k)"
    and t0: "0 < t" and tN: "t \<le> N"
    and cl: "fst (X ! (Suc p + t)) \<le> fst (X ! Suc p)"
    and pl: "p < l" and lN: "l \<le> Suc p + t"
    and lj0: "j0 \<le> l"
  shows "snd (X ! l) \<le> max (snd (X ! p)) (snd (X ! Suc p))"
  sorry

lemma ginv_ob_pre:
  assumes G: "ginv M" and B: "blockok 0 M" and ST: "M \<in> ST_PS" and n1: "1 \<le> n"
    and j1d: "j1 = Lng M - 1" and j1nz: "j1 \<noteq> 0"
    and Fz: "\<not> (entry M 0 j1 = 0 \<and> entry M 1 j1 = 0)"
    and i1d: "i1 = idx1 M j1" and hp: "hasParent M i1 j1"
    and j0d: "j0 = parent M i1 j1"
    and d0d: "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
    and opeq: "X = take j0 M @ concat (map (\<lambda>k.
           map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j)) [j0..<j1]) [0..<n])"
    and bnd: "Suc p + N < length X"
    and dom: "\<forall>k. p < k \<and> k \<le> Suc p + N \<longrightarrow> fst (X ! p) < fst (X ! k)"
    and t0: "0 < t" and tN: "t \<le> N"
    and cl: "fst (X ! (Suc p + t)) \<le> fst (X ! Suc p)"
    and pl: "p < l" and lN: "l \<le> Suc p + t"
    and pj0: "p < j0"
  shows "snd (X ! l) \<le> max (snd (X ! p)) (snd (X ! Suc p))"
proof -
  have nR: "nextR M i1 j0 j1" unfolding j0d by (rule parent_nextR[OF hp])
  have j0j1: "j0 < j1" using nR by (rule nextR_less)
  have lenM: "length M = Suc j1" using j1d j1nz by (cases M) auto
  have j1len: "j1 < length M" using lenM by simp
  define L where "L = j1 - j0"
  have L0: "0 < L" unfolding L_def using j0j1 by simp
  have lenX: "length X = j0 + n * L"
    unfolding L_def by (rule oper_bad_len[OF opeq j0j1 j1len])
  have npre: "\<And>i. i < j0 \<Longrightarrow> X ! i = M ! i"
    using oper_bad_nth_pre[OF opeq _ j1len j0j1] by blast
  have ncopy: "\<And>k q. k < n \<Longrightarrow> q < L \<Longrightarrow>
        X ! (j0 + (k * L + q)) = (entry M 0 (j0 + q) + k * d0, entry M 1 (j0 + q))"
    unfolding L_def using oper_bad_nth_copy[OF opeq j0j1 j1len] by blast
  have hm0: "\<forall>k. j0 < k \<and> k \<le> j1 \<longrightarrow> entry M 0 j0 < entry M 0 k"
    by (rule block_head_min[OF hp j0d])
  have pairM: "\<And>j. (entry M 0 j, entry M 1 j) = M ! j"
    unfolding entry_def by simp
  have j0Lj1: "j0 + L = j1" unfolding L_def using j0j1 by simp
  have Xv0: "\<And>i. i < j0 + L \<Longrightarrow> X ! i = M ! i"
  proof -
    fix i assume iL: "i < j0 + L"
    show "X ! i = M ! i"
    proof (cases "i < j0")
      case True thus ?thesis by (rule npre)
    next
      case False
      have qL: "i - j0 < L" using iL False by simp
      have c0: "X ! (j0 + (0 * L + (i - j0)))
          = (entry M 0 (j0 + (i - j0)) + 0 * d0, entry M 1 (j0 + (i - j0)))"
        by (rule ncopy) (use n1 qL in simp_all)
      have ii: "j0 + (i - j0) = i" using False by simp
      have "X ! i = (entry M 0 i, entry M 1 i)" using c0 ii by simp
      thus ?thesis using pairM by simp
    qed
  qed
  have Xpv: "X ! p = M ! p" using npre pj0 by simp
  have spj0: "Suc p \<le> j0" using pj0 by simp
  have c0v: "X ! Suc p = M ! Suc p" using Xv0 spj0 L0 by simp
  have idxE: "\<And>i. j0 \<le> i \<Longrightarrow> i < length X \<Longrightarrow>
       \<exists>k q. k < n \<and> q < L \<and> i = j0 + (k * L + q)
           \<and> X ! i = (entry M 0 (j0 + q) + k * d0, entry M 1 (j0 + q))"
  proof -
    fix i assume ji: "j0 \<le> i" and iX: "i < length X"
    define k where "k = (i - j0) div L"
    define q where "q = (i - j0) mod L"
    have kq: "i - j0 = k * L + q" unfolding k_def q_def by simp
    have qL: "q < L" unfolding q_def using L0 by simp
    have kn: "k < n"
    proof -
      have "i - j0 < n * L" using iX lenX ji by simp
      thus ?thesis unfolding k_def
        by (metis less_mult_imp_div_less mult.commute)
    qed
    have ii: "i = j0 + (k * L + q)" using kq ji by simp
    have "X ! (j0 + (k * L + q)) = (entry M 0 (j0 + q) + k * d0, entry M 1 (j0 + q))"
      by (rule ncopy[OF kn qL])
    thus "\<exists>k q. k < n \<and> q < L \<and> i = j0 + (k * L + q)
           \<and> X ! i = (entry M 0 (j0 + q) + k * d0, entry M 1 (j0 + q))"
      using kn qL ii by blast
  qed
  show ?thesis
  proof (cases "Suc p + N < j0 + L")
    case C1: True
    have XM: "\<And>i. i \<le> Suc p + N \<Longrightarrow> X ! i = M ! i"
      using Xv0 C1 by simp
    have bndM: "Suc p + N < length M" using C1 j0Lj1 j1len by simp
    have domM: "\<forall>k. p < k \<and> k \<le> Suc p + N \<longrightarrow> fst (M ! p) < fst (M ! k)"
    proof (intro allI impI)
      fix k assume kk: "p < k \<and> k \<le> Suc p + N"
      have "fst (X ! p) < fst (X ! k)" using dom kk by blast
      thus "fst (M ! p) < fst (M ! k)" using XM kk by simp
    qed
    have clM: "fst (M ! (Suc p + t)) \<le> fst (M ! Suc p)"
      using cl XM tN by simp
    have "snd (M ! l) \<le> max (snd (M ! p)) (snd (M ! Suc p))"
      using G[unfolded ginv_def, rule_format, of p N t l]
        bndM domM t0 tN clM pl lN by blast
    thus ?thesis using XM pl lN tN by simp
  next
    case C2: False
    hence C2': "j0 + L \<le> Suc p + N" by simp
    show ?thesis
    proof (cases "Suc p = j0")
      case sp: True
      have cpos: "j0 \<le> Suc p + t" using sp by simp
      have cX: "Suc p + t < length X" using bnd tN by simp
      obtain kc qc where kc: "kc < n" "qc < L" "Suc p + t = j0 + (kc * L + qc)"
          and Xc: "X ! (Suc p + t) = (entry M 0 (j0 + qc) + kc * d0, entry M 1 (j0 + qc))"
        using idxE[OF cpos cX] by blast
      have fc0: "fst (X ! Suc p) = entry M 0 j0"
        using c0v unfolding sp entry_def by simp
      have clq: "entry M 0 (j0 + qc) + kc * d0 \<le> entry M 0 j0"
        using cl Xc fc0 by simp
      have qc0: "qc = 0"
      proof (rule ccontr)
        assume "qc \<noteq> 0"
        hence "j0 < j0 + qc \<and> j0 + qc \<le> j1" using kc(2) j0Lj1 by simp
        hence "entry M 0 j0 < entry M 0 (j0 + qc)" using hm0 by blast
        thus False using clq by simp
      qed
      have kc1: "0 < kc"
      proof (rule ccontr)
        assume "\<not> 0 < kc"
        hence "Suc p + t = j0" using kc(3) qc0 by simp
        thus False using sp t0 by simp
      qed
      have d00: "d0 = 0" using clq qc0 kc1 by auto
      have lX: "l < length X" using bnd lN tN by simp
      have lj0: "j0 \<le> l" using pl sp by simp
      obtain kl ql where kl: "kl < n" "ql < L" "l = j0 + (kl * L + ql)"
          and Xl: "X ! l = (entry M 0 (j0 + ql) + kl * d0, entry M 1 (j0 + ql))"
        using idxE[OF lj0 lX] by blast
      have j0pos: "0 < j0" using sp by simp
      have pj: "p = j0 - 1" using sp by simp
      have fpp: "fst (M ! (j0 - 1)) < entry M 0 j0"
      proof -
        have "fst (X ! p) < fst (X ! Suc p)" using dom by simp
        thus ?thesis using Xpv fc0 pj by simp
      qed
      have qlj1: "ql < j1 - j0" using kl(2) unfolding L_def .
      have "entry M 1 (j0 + ql) \<le> max (snd (M ! (j0 - 1))) (entry M 1 j0)"
        by (rule ginv_GBLK0[OF ST j1d j1nz Fz i1d hp j0d d0d d00 j0pos fpp qlj1])
      moreover have "snd (X ! l) = entry M 1 (j0 + ql)" using Xl by simp
      moreover have "snd (X ! p) = snd (M ! (j0 - 1))" using Xpv pj by simp
      moreover have "snd (X ! Suc p) = entry M 1 j0"
        using c0v unfolding sp entry_def by simp
      ultimately show ?thesis by simp
    next
      case spl: False
      hence spj0': "Suc p < j0" using spj0 by simp
      define NM where "NM = j1 - 1 - Suc p"
      have NMe: "Suc p + NM = j1 - 1" unfolding NM_def using spj0' j0j1 by arith
      have bndM: "Suc p + NM < length M" unfolding NMe using j1len j1nz by simp
      have domM: "\<forall>k. p < k \<and> k \<le> Suc p + NM \<longrightarrow> fst (M ! p) < fst (M ! k)"
      proof (intro allI impI)
        fix k assume kk: "p < k \<and> k \<le> Suc p + NM"
        show "fst (M ! p) < fst (M ! k)"
        proof (cases "k < j0")
          case True
          have "k \<le> Suc p + N" using True C2' by simp
          hence "fst (X ! p) < fst (X ! k)" using dom kk by blast
          thus ?thesis using Xpv npre[OF True] by simp
        next
          case False
          hence kj0: "j0 \<le> k" by simp
          have kj1: "k \<le> j1 - 1" using kk NMe by simp
          define q where "q = k - j0"
          have qL: "q < L" unfolding q_def L_def using kj1 kj0 j0j1 by arith
          have kpos: "j0 + q = k" unfolding q_def using kj0 by simp
          have wX: "j0 + (0 * L + q) \<le> Suc p + N" using C2' qL by simp
          have pw: "p < j0 + (0 * L + q)" using pj0 by simp
          have "fst (X ! p) < fst (X ! (j0 + (0 * L + q)))"
            using dom wX pw by blast
          moreover have "X ! (j0 + (0 * L + q))
              = (entry M 0 (j0 + q) + 0 * d0, entry M 1 (j0 + q))"
            by (rule ncopy) (use n1 qL in simp_all)
          ultimately have "fst (X ! p) < entry M 0 (j0 + q)" by simp
          thus ?thesis using Xpv kpos unfolding entry_def by simp
        qed
      qed
      have clX: "Suc p + t < length X" using bnd tN by simp
      have EXcl: "\<exists>tm. 0 < tm \<and> tm \<le> NM \<and> fst (M ! (Suc p + tm)) \<le> fst (M ! Suc p)
                    \<and> (tm = t \<or> j0 \<le> Suc p + tm)"
      proof (cases "Suc p + t < j0")
        case True
        have a1: "fst (M ! (Suc p + t)) \<le> fst (M ! Suc p)"
          using cl Xv0[of "Suc p + t"] c0v True L0 by simp
        have a2: "t \<le> NM" unfolding NM_def using True j0j1 by arith
        show ?thesis by (intro exI[of _ t]) (use a1 a2 t0 in simp)
      next
        case False
        hence cj0: "j0 \<le> Suc p + t" by simp
        obtain kc qc where kc: "kc < n" "qc < L" "Suc p + t = j0 + (kc * L + qc)"
            and Xc: "X ! (Suc p + t) = (entry M 0 (j0 + qc) + kc * d0, entry M 1 (j0 + qc))"
          using idxE[OF cj0 clX] by blast
        have "entry M 0 (j0 + qc) + kc * d0 \<le> fst (M ! Suc p)"
          using cl Xc c0v by simp
        hence ec: "entry M 0 (j0 + qc) \<le> fst (M ! Suc p)" by simp
        define tm where "tm = j0 + qc - Suc p"
        have tm1: "0 < tm" unfolding tm_def using spj0' by arith
        have qcj1: "j0 + qc \<le> j1 - 1" using kc(2) j0Lj1 by arith
        have tm2: "tm \<le> NM" unfolding tm_def NM_def using qcj1 by arith
        have tme: "Suc p + tm = j0 + qc" unfolding tm_def using spj0' by arith
        have b1: "fst (M ! (Suc p + tm)) \<le> fst (M ! Suc p)"
          unfolding tme using ec unfolding entry_def by simp
        have b2: "j0 \<le> Suc p + tm" unfolding tme by simp
        show ?thesis by (intro exI[of _ tm]) (use b1 b2 tm1 tm2 in simp)
      qed
      obtain tm where tm: "0 < tm" "tm \<le> NM" "fst (M ! (Suc p + tm)) \<le> fst (M ! Suc p)"
          and tmpos: "tm = t \<or> j0 \<le> Suc p + tm"
        using EXcl by blast
      have lX: "l < length X" using bnd lN tN by simp
      show ?thesis
      proof (cases "l < j0")
        case True
        have ltm: "l \<le> Suc p + tm"
          using tmpos lN True by auto
        have "snd (M ! l) \<le> max (snd (M ! p)) (snd (M ! Suc p))"
          using G[unfolded ginv_def, rule_format, of p NM tm l]
            bndM domM tm pl ltm by blast
        thus ?thesis using npre[OF True] Xpv c0v by simp
      next
        case False
        hence lj0: "j0 \<le> l" by simp
        show ?thesis
          by (rule ginv_ob_cross[OF G B ST n1 j1d j1nz Fz i1d hp j0d d0d opeq
                bnd dom t0 tN cl pl lN lj0])
      qed
    qed
  qed
qed

text \<open>(qpos) The copy-anchored crossing seam with a positive in-copy offset:
  the only remaining live class of the cross-copy preservation (mining:
  realized 171 at base closure; sub-elements all satisfy \<open>snd \<le> e1 j1\<close> —
  candidate route via the row-1 parent minimality).\<close>

lemma ginv_ob_copy:
  assumes G: "ginv M" and B: "blockok 0 M" and ST: "M \<in> ST_PS" and n1: "1 \<le> n"
    and j1d: "j1 = Lng M - 1" and j1nz: "j1 \<noteq> 0"
    and Fz: "\<not> (entry M 0 j1 = 0 \<and> entry M 1 j1 = 0)"
    and i1d: "i1 = idx1 M j1" and hp: "hasParent M i1 j1"
    and j0d: "j0 = parent M i1 j1"
    and d0d: "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
    and opeq: "X = take j0 M @ concat (map (\<lambda>k.
           map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j)) [j0..<j1]) [0..<n])"
    and bnd: "Suc p + N < length X"
    and dom: "\<forall>k. p < k \<and> k \<le> Suc p + N \<longrightarrow> fst (X ! p) < fst (X ! k)"
    and t0: "0 < t" and tN: "t \<le> N"
    and cl: "fst (X ! (Suc p + t)) \<le> fst (X ! Suc p)"
    and pl: "p < l" and lN: "l \<le> Suc p + t"
    and pj0: "j0 \<le> p"
  shows "snd (X ! l) \<le> max (snd (X ! p)) (snd (X ! Suc p))"
proof -
  have nR: "nextR M i1 j0 j1" unfolding j0d by (rule parent_nextR[OF hp])
  have j0j1: "j0 < j1" using nR by (rule nextR_less)
  have lenM: "length M = Suc j1" using j1d j1nz by (cases M) auto
  have j1len: "j1 < length M" using lenM by simp
  define L where "L = j1 - j0"
  have L0: "0 < L" unfolding L_def using j0j1 by simp
  have lenX: "length X = j0 + n * L"
    unfolding L_def by (rule oper_bad_len[OF opeq j0j1 j1len])
  have ncopy: "\<And>k q. k < n \<Longrightarrow> q < L \<Longrightarrow>
        X ! (j0 + (k * L + q)) = (entry M 0 (j0 + q) + k * d0, entry M 1 (j0 + q))"
    unfolding L_def using oper_bad_nth_copy[OF opeq j0j1 j1len] by blast
  have hm0: "\<forall>k. j0 < k \<and> k \<le> j1 \<longrightarrow> entry M 0 j0 < entry M 0 k"
    by (rule block_head_min[OF hp j0d])
  have j0Lj1: "j0 + L = j1" unfolding L_def using j0j1 by simp
  have idxE: "\<And>i. j0 \<le> i \<Longrightarrow> i < length X \<Longrightarrow>
       \<exists>k q. k < n \<and> q < L \<and> i = j0 + (k * L + q)
           \<and> X ! i = (entry M 0 (j0 + q) + k * d0, entry M 1 (j0 + q))"
  proof -
    fix i assume ji: "j0 \<le> i" and iX: "i < length X"
    define k where "k = (i - j0) div L"
    define q where "q = (i - j0) mod L"
    have kq: "i - j0 = k * L + q" unfolding k_def q_def by simp
    have qL: "q < L" unfolding q_def using L0 by simp
    have kn: "k < n"
    proof -
      have "i - j0 < n * L" using iX lenX ji by simp
      thus ?thesis unfolding k_def
        by (metis less_mult_imp_div_less mult.commute)
    qed
    have ii: "i = j0 + (k * L + q)" using kq ji by simp
    have "X ! (j0 + (k * L + q)) = (entry M 0 (j0 + q) + k * d0, entry M 1 (j0 + q))"
      by (rule ncopy[OF kn qL])
    thus "\<exists>k q. k < n \<and> q < L \<and> i = j0 + (k * L + q)
           \<and> X ! i = (entry M 0 (j0 + q) + k * d0, entry M 1 (j0 + q))"
      using kn qL ii by blast
  qed
  define kP where "kP = (p - j0) div L"
  define qP where "qP = (p - j0) mod L"
  have pdec: "p = j0 + (kP * L + qP)" unfolding kP_def qP_def using pj0 by simp
  have qPL: "qP < L" unfolding qP_def using L0 by simp
  have kPn: "kP < n"
  proof -
    have "p - j0 < n * L" using bnd lenX pj0 by simp
    thus ?thesis unfolding kP_def by (metis less_mult_imp_div_less mult.commute)
  qed
  have Xp: "X ! p = (entry M 0 (j0 + qP) + kP * d0, entry M 1 (j0 + qP))"
    using ncopy[OF kPn qPL] pdec by simp
  show ?thesis
  proof (cases "Suc p + N < j0 + (kP + 1) * L")
    case EB: True
    have qN: "qP + 1 + N < L" using EB pdec by simp
    define pm where "pm = j0 + qP"
    have win: "\<And>s. s \<le> Suc N \<Longrightarrow>
        X ! (p + s) = (entry M 0 (pm + s) + kP * d0, entry M 1 (pm + s))"
    proof -
      fix s assume sN: "s \<le> Suc N"
      have ps: "p + s = j0 + (kP * L + (qP + s))" using pdec by simp
      have qsL: "qP + s < L" using sN qN by simp
      show "X ! (p + s) = (entry M 0 (pm + s) + kP * d0, entry M 1 (pm + s))"
        unfolding ps pm_def using ncopy[OF kPn qsL] by (simp add: add.assoc)
    qed
    have bndM: "Suc pm + N < length M"
      unfolding pm_def using qN j0Lj1 j1len by simp
    have domM: "\<forall>k. pm < k \<and> k \<le> Suc pm + N \<longrightarrow> fst (M ! pm) < fst (M ! k)"
    proof (intro allI impI)
      fix k assume kk: "pm < k \<and> k \<le> Suc pm + N"
      define s where "s = k - pm"
      have s1: "0 < s" and sN: "s \<le> Suc N" unfolding s_def using kk by auto
      have ks: "k = pm + s" unfolding s_def using kk by simp
      have ps: "p < p + s \<and> p + s \<le> Suc p + N" using s1 sN by auto
      have "fst (X ! p) < fst (X ! (p + s))" using dom ps by blast
      hence "entry M 0 pm + kP * d0 < entry M 0 (pm + s) + kP * d0"
        using Xp win[OF sN] unfolding pm_def by simp
      hence "entry M 0 pm < entry M 0 (pm + s)" by simp
      thus "fst (M ! pm) < fst (M ! k)" unfolding ks entry_def by simp
    qed
    have clM: "fst (M ! (Suc pm + t)) \<le> fst (M ! Suc pm)"
    proof -
      have e1: "X ! (p + Suc t) = (entry M 0 (pm + Suc t) + kP * d0, entry M 1 (pm + Suc t))"
        using win[of "Suc t"] tN by simp
      have e2: "X ! (p + 1) = (entry M 0 (pm + 1) + kP * d0, entry M 1 (pm + 1))"
        using win[of 1] by simp
      have "fst (X ! (p + Suc t)) \<le> fst (X ! (p + 1))" using cl by simp
      hence "entry M 0 (pm + Suc t) \<le> entry M 0 (pm + 1)" using e1 e2 by simp
      thus ?thesis unfolding entry_def by simp
    qed
    define sl where "sl = l - p"
    have sl1: "0 < sl" and slt: "sl \<le> Suc t" unfolding sl_def using pl lN by auto
    have slN: "sl \<le> Suc N" using slt tN by simp
    have ls: "l = p + sl" unfolding sl_def using pl by simp
    have plm: "pm < pm + sl" using sl1 by simp
    have lmm: "pm + sl \<le> Suc pm + t" using slt by simp
    have "snd (M ! (pm + sl)) \<le> max (snd (M ! pm)) (snd (M ! Suc pm))"
      using G[unfolded ginv_def, rule_format, of pm N t "pm + sl"]
        bndM domM t0 tN clM plm lmm by blast
    moreover have "snd (X ! l) = snd (M ! (pm + sl))"
      unfolding ls using win[OF slN] unfolding entry_def by simp
    moreover have "snd (X ! p) = snd (M ! pm)"
      using Xp unfolding pm_def entry_def by simp
    moreover have "snd (X ! Suc p) = snd (M ! Suc pm)"
      using win[of 1] unfolding entry_def by simp
    ultimately show ?thesis by simp
  next
    case EX: False
    hence cross: "j0 + (kP + 1) * L \<le> Suc p + N" by simp
    show ?thesis
    proof (cases "qP = 0")
      case qpos: False
      have lj0: "j0 \<le> l" using pj0 pl by simp
      show ?thesis
        by (rule ginv_ob_cross[OF G B ST n1 j1d j1nz Fz i1d hp j0d d0d opeq
              bnd dom t0 tN cl pl lN lj0])
    next
      case qP0: True
      have Xph: "X ! p = (entry M 0 j0 + kP * d0, entry M 1 j0)"
        using Xp qP0 by simp
      have nhpos: "j0 + ((kP + 1) * L + 0) \<le> Suc p + N" using cross by simp
      have kP1n: "kP + 1 < n"
      proof -
        have "j0 + ((kP + 1) * L + 0) < length X" using nhpos bnd by simp
        hence "(kP + 1) * L < n * L" unfolding lenX by simp
        thus ?thesis using L0
          by (metis gr_implies_not0 less_mult_imp_div_less nonzero_mult_div_cancel_right)
      qed
      have Xnh: "X ! (j0 + ((kP + 1) * L + 0))
          = (entry M 0 j0 + (kP + 1) * d0, entry M 1 j0)"
        using ncopy[OF kP1n L0] by simp
      have pnh: "p < j0 + ((kP + 1) * L + 0)" using pdec qP0 qPL by simp
      have "fst (X ! p) < fst (X ! (j0 + ((kP + 1) * L + 0)))"
        using dom pnh nhpos by blast
      hence d0pos: "0 < d0" using Xph Xnh by simp
      have i1one: "i1 = 1"
        using idx1_le[of M j1] d0d d0pos i1d by (cases i1) auto
      have e0j: "entry M 0 j0 < entry M 0 j1" using hm0 j0j1 by simp
      have d0ex: "entry M 0 j0 + d0 = entry M 0 j1"
        unfolding d0d using i1one e0j by simp
      have cX: "Suc p + t < length X" using bnd tN by simp
      have cj0: "j0 \<le> Suc p + t" using pj0 by simp
      obtain kc qc where kc: "kc < n" "qc < L" "Suc p + t = j0 + (kc * L + qc)"
          and Xc: "X ! (Suc p + t) = (entry M 0 (j0 + qc) + kc * d0, entry M 1 (j0 + qc))"
        using idxE[OF cj0 cX] by blast
      show ?thesis
      proof (cases "L = 1")
        case L1: True
        have False
        proof -
          have qc0: "qc = 0" using kc(2) L1 by simp
          have sdec: "Suc p = j0 + ((kP + 1) * L + 0)" using pdec qP0 L1 by simp
          have Xs: "X ! Suc p = (entry M 0 j0 + (kP + 1) * d0, entry M 1 j0)"
            unfolding sdec using ncopy[OF kP1n L0] by simp
          have kcgt: "kP + 1 < kc"
          proof -
            have "j0 + ((kP + 1) * L + 0) < j0 + (kc * L + qc)"
              using kc(3) sdec t0 by simp
            thus ?thesis using qc0 L1 by simp
          qed
          have "entry M 0 j0 + kc * d0 \<le> entry M 0 j0 + (kP + 1) * d0"
            using cl Xc Xs qc0 by simp
          moreover have "(kP + 1) * d0 < kc * d0"
            using kcgt d0pos mult_less_mono1 by blast
          ultimately show False by simp
        qed
        thus ?thesis ..
      next
        case L2: False
        hence oneL: "(1::nat) < L" using L0 by simp
        have c0pos: "Suc p = j0 + (kP * L + 1)" using pdec qP0 by simp
        have Xc0: "X ! Suc p = (entry M 0 (j0 + 1) + kP * d0, entry M 1 (j0 + 1))"
          unfolding c0pos using ncopy[OF kPn oneL] by simp
        have e01step: "entry M 0 (j0 + 1) \<le> Suc (entry M 0 j0)"
        proof -
          have "Suc j0 < length M" using j0j1 j1len by simp
          hence "fst (M ! Suc j0) \<le> Suc (fst (M ! j0))"
            using B unfolding blockok_def by simp
          thus ?thesis unfolding entry_def by simp
        qed
        have e01gt: "entry M 0 j0 < entry M 0 (j0 + 1)"
          using hm0 oneL j0Lj1 by simp
        define NM where "NM = L - 1"
        have NMe: "Suc j0 + NM = j1" unfolding NM_def using L0 j0Lj1 by arith
        have NM1: "1 \<le> NM" unfolding NM_def using oneL by arith
        have bndM: "Suc j0 + NM < length M" unfolding NMe using lenM by simp
        have domM: "\<forall>k. j0 < k \<and> k \<le> Suc j0 + NM \<longrightarrow> fst (M ! j0) < fst (M ! k)"
        proof (intro allI impI)
          fix k assume kk: "j0 < k \<and> k \<le> Suc j0 + NM"
          have "entry M 0 j0 < entry M 0 k" using hm0 kk NMe by blast
          thus "fst (M ! j0) < fst (M ! k)" unfolding entry_def by simp
        qed
        have EXcl: "\<exists>tm. 0 < tm \<and> tm \<le> NM \<and> fst (M ! (Suc j0 + tm)) \<le> fst (M ! Suc j0)"
        proof (cases "d0 = 1")
          case d01: True
          have a3: "entry M 0 j1 = Suc (entry M 0 j0)" using d0ex d01 by arith
          have a4: "entry M 0 j1 \<le> entry M 0 (j0 + 1)" using a3 e01gt by arith
          have a6: "fst (M ! (Suc j0 + NM)) \<le> fst (M ! Suc j0)"
          proof -
            have "fst (M ! j1) \<le> fst (M ! Suc j0)"
              using a4 unfolding entry_def by simp
            thus ?thesis unfolding NMe .
          qed
          have a7: "0 < NM" using NM1 by simp
          show ?thesis by (intro exI[of _ NM]) (use a6 a7 in simp)
        next
          case d02: False
          hence d02': "2 \<le> d0" using d0pos by simp
          have clq: "entry M 0 (j0 + qc) + kc * d0 \<le> entry M 0 (j0 + 1) + kP * d0"
            using cl Xc Xc0 by simp
          have kckP: "kP \<le> kc"
          proof (rule ccontr)
            assume "\<not> kP \<le> kc"
            hence "Suc kc \<le> kP" by simp
            hence "Suc kc * L \<le> kP * L" by (rule mult_le_mono1)
            hence "kc * L + qc < kP * L + 1" using kc(2) by simp
            thus False using kc(3) c0pos t0 by arith
          qed
          have qc2: "2 \<le> qc"
          proof (rule ccontr)
            assume "\<not> 2 \<le> qc"
            hence "qc = 0 \<or> qc = 1" by arith
            thus False
            proof
              assume q0: "qc = 0"
              have "kP + 1 \<le> kc"
              proof (rule ccontr)
                assume "\<not> kP + 1 \<le> kc"
                hence "kc = kP" using kckP by simp
                hence "Suc p + t = p" using kc(3) q0 pdec qP0 by simp
                thus False by simp
              qed
              hence m1: "d0 + kP * d0 \<le> kc * d0"
                using mult_le_mono1[of "kP + 1" kc d0] by simp
              have clq0: "entry M 0 j0 + kc * d0 \<le> entry M 0 (j0 + 1) + kP * d0"
                using clq q0 by simp
              show False using m1 clq0 e01step d02' by arith
            next
              assume q1: "qc = 1"
              have "kP < kc"
              proof (rule ccontr)
                assume "\<not> kP < kc"
                hence "kc = kP" using kckP by simp
                hence "Suc p + t = Suc p" using kc(3) q1 c0pos by simp
                thus False using t0 by simp
              qed
              hence m1: "d0 + kP * d0 \<le> kc * d0"
                using mult_le_mono1[of "kP + 1" kc d0] by simp
              have clq1: "entry M 0 (j0 + 1) + kc * d0 \<le> entry M 0 (j0 + 1) + kP * d0"
                using clq q1 by simp
              show False using m1 clq1 d0pos by arith
            qed
          qed
          have m2: "kP * d0 \<le> kc * d0" using kckP by (rule mult_le_mono1)
          have ecl: "entry M 0 (j0 + qc) \<le> entry M 0 (j0 + 1)"
            using clq m2 by arith
          define tm where "tm = qc - 1"
          have tm1: "0 < tm" unfolding tm_def using qc2 by simp
          have tm2: "tm \<le> NM" unfolding tm_def NM_def using kc(2) by arith
          have tme: "Suc j0 + tm = j0 + qc" unfolding tm_def using qc2 by arith
          have a6: "fst (M ! (Suc j0 + tm)) \<le> fst (M ! Suc j0)"
            unfolding tme using ecl unfolding entry_def by simp
          show ?thesis by (intro exI[of _ tm]) (use a6 tm1 tm2 in simp)
        qed
        obtain tm where tm: "0 < tm" "tm \<le> NM"
            "fst (M ! (Suc j0 + tm)) \<le> fst (M ! Suc j0)"
          using EXcl by blast
        have lj0: "j0 \<le> l" using pj0 pl by simp
        show ?thesis
          by (rule ginv_ob_cross[OF G B ST n1 j1d j1nz Fz i1d hp j0d d0d opeq
                bnd dom t0 tN cl pl lN lj0])
      qed
    qed
  qed
qed

lemma ginv_oper_bad:
  assumes G: "ginv M" and B: "blockok 0 M" and ST: "M \<in> ST_PS" and n1: "1 \<le> n"
    and j1d: "j1 = Lng M - 1" and j1nz: "j1 \<noteq> 0"
    and Fz: "\<not> (entry M 0 j1 = 0 \<and> entry M 1 j1 = 0)"
    and i1d: "i1 = idx1 M j1" and hp: "hasParent M i1 j1"
    and j0d: "j0 = parent M i1 j1"
    and d0d: "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
    and opeq: "X = take j0 M @ concat (map (\<lambda>k.
           map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j)) [j0..<j1]) [0..<n])"
  shows "ginv X"
  unfolding ginv_def
proof (intro allI impI)
  fix p N t l
  assume bnd: "Suc p + N < length X"
    and dom: "\<forall>k. p < k \<and> k \<le> Suc p + N \<longrightarrow> fst (X ! p) < fst (X ! k)"
    and t0: "0 < t" and tN: "t \<le> N"
    and cl: "fst (X ! (Suc p + t)) \<le> fst (X ! Suc p)"
    and pl: "p < l" and lN: "l \<le> Suc p + t"
  show "snd (X ! l) \<le> max (snd (X ! p)) (snd (X ! Suc p))"
  proof (cases "p < j0")
    case True
    show ?thesis
      by (rule ginv_ob_pre[OF G B ST n1 j1d j1nz Fz i1d hp j0d d0d opeq
            bnd dom t0 tN cl pl lN True])
  next
    case False
    hence ge: "j0 \<le> p" by simp
    show ?thesis
      by (rule ginv_ob_copy[OF G B ST n1 j1d j1nz Fz i1d hp j0d d0d opeq
            bnd dom t0 tN cl pl lN ge])
  qed
qed

lemma ginv_oper:
  assumes G: "ginv M" and ST: "M \<in> ST_PS" and n1: "1 \<le> n"
  shows "ginv (oper M n)"
proof -
  define j1 where "j1 = Lng M - 1"
  have b: "blockok 0 M" by (rule blockok_ST_PS[OF ST])
  show ?thesis
  proof (cases "j1 = 0")
    case True thus ?thesis using G unfolding oper_def Let_def j1_def by simp
  next
    case False
    show ?thesis
    proof (cases "entry M 0 j1 = 0 \<and> entry M 1 j1 = 0")
      case True
      have "oper M n = Pred M"
        unfolding oper_def Let_def j1_def[symmetric] using False True by auto
      moreover have "ginv (Pred M)"
        unfolding Pred_def using G ginv_butlast by simp
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
        moreover have "ginv (Pred M)"
          unfolding Pred_def using G ginv_butlast by simp
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
          by (rule ginv_oper_bad[OF G b ST n1 j1_def False Fz i1_def hp j0_def d0_def opeq])
      qed
    qed
  qed
qed

theorem ginv_ST_PS: "M \<in> ST_PS \<Longrightarrow> ginv M"
proof (induction M rule: ST_PS.induct)
  case (diag v) show ?case by (rule ginv_diagSeq)
next
  case (oper M n)
  show ?case by (rule ginv_oper[OF oper.IH oper.hyps(1) oper.hyps(2)])
qed

text \<open>Bridge: the closed-window bound in \<open>dseg\<close> form.\<close>

lemma ginv_dseg_bound:
  assumes D: "dseg u (c0 # rest)"
    and cl: "dropWhile (\<lambda>r. fst c0 < fst r) rest \<noteq> []"
    and x: "x \<in> set (c0 # takeWhile (\<lambda>r. fst c0 < fst r) rest)"
  shows "snd x \<le> max u (snd c0)"
proof -
  obtain pre pp post where H: "pre @ (pp # (c0 # rest)) @ post \<in> ST_PS"
    and dom0: "\<forall>r \<in> set (c0 # rest). fst pp < fst r" and ud: "u = snd pp"
    using D unfolding dseg_def by blast
  define H' where "H' = pre @ (pp # (c0 # rest)) @ post"
  have GH: "ginv H'" unfolding H'_def by (rule ginv_ST_PS[OF H])
  define p where "p = length pre"
  define n where "n = length rest"
  define K where "K = takeWhile (\<lambda>r. fst c0 < fst r) rest"
  define t where "t = Suc (length K)"
  have Klt: "length K < length rest"
  proof -
    have deq: "K @ dropWhile (\<lambda>r. fst c0 < fst r) rest = rest"
      unfolding K_def by simp
    have "length K + length (dropWhile (\<lambda>r. fst c0 < fst r) rest) = length rest"
      using arg_cong[OF deq, of length] by simp
    moreover have "0 < length (dropWhile (\<lambda>r. fst c0 < fst r) rest)"
      using cl by simp
    ultimately show ?thesis by arith
  qed
  have nthpp: "H' ! p = pp"
    unfolding H'_def p_def by (simp add: nth_append)
  have nthW: "\<And>i. i \<le> n \<Longrightarrow> H' ! (p + Suc i) = (c0 # rest) ! i"
  proof -
    fix i assume iL: "i \<le> n"
    have "H' ! (p + Suc i) = ((pp # (c0 # rest)) @ post) ! Suc i"
      unfolding H'_def p_def by (simp add: nth_append)
    also have "\<dots> = (pp # (c0 # rest)) ! Suc i"
      using iL unfolding n_def by (cases i) (simp_all add: nth_append)
    also have "\<dots> = (c0 # rest) ! i" by simp
    finally show "H' ! (p + Suc i) = (c0 # rest) ! i" .
  qed
  have nthc0: "H' ! Suc p = c0" using nthW[of 0] by simp
  have lenH: "Suc p + n < length H'"
    unfolding H'_def p_def n_def by simp
  have dom: "\<forall>k. p < k \<and> k \<le> Suc p + n \<longrightarrow> fst (H' ! p) < fst (H' ! k)"
  proof (intro allI impI)
    fix k assume kk: "p < k \<and> k \<le> Suc p + n"
    define i where "i = k - Suc p"
    have ki: "k = p + Suc i" unfolding i_def using kk by arith
    have iL: "i \<le> n" unfolding i_def using kk by arith
    have "H' ! k = (c0 # rest) ! i" unfolding ki by (rule nthW[OF iL])
    moreover have "(c0 # rest) ! i \<in> set (c0 # rest)"
      by (rule nth_mem) (use iL n_def in simp)
    ultimately show "fst (H' ! p) < fst (H' ! k)"
      using dom0 nthpp by auto
  qed
  have tcl: "0 < t" "t \<le> n" unfolding t_def n_def using Klt by simp_all
  have stopv: "(c0 # rest) ! t = rest ! length K"
    unfolding t_def by simp
  have stopd: "rest ! length K = hd (dropWhile (\<lambda>r. fst c0 < fst r) rest)"
  proof -
    have "dropWhile (\<lambda>r. fst c0 < fst r) rest = drop (length K) rest"
      unfolding K_def by (rule dropWhile_eq_drop)
    thus ?thesis using hd_drop_conv_nth[OF Klt] by simp
  qed
  have stopf: "\<not> fst c0 < fst (rest ! length K)"
    unfolding stopd using hd_dropWhile[OF cl] by blast
  have clw: "fst (H' ! (Suc p + t)) \<le> fst (H' ! Suc p)"
  proof -
    have "H' ! (p + Suc t) = (c0 # rest) ! t"
      by (rule nthW) (use tcl(2) in simp)
    thus ?thesis using stopv stopf nthc0 by simp
  qed
  obtain jj where jl: "jj < length (c0 # K)" and jx0: "(c0 # K) ! jj = x"
    using x unfolding K_def[symmetric] in_set_conv_nth by blast
  have jj: "jj < Suc (length K)" "(c0 # K) ! jj = x"
    using jl jx0 by simp_all
  have jx: "(c0 # rest) ! jj = x"
  proof (cases jj)
    case 0 thus ?thesis using jj(2) by simp
  next
    case (Suc m)
    have mK: "m < length K" using jj(1) Suc by simp
    have "(c0 # K) ! jj = K ! m" using Suc by simp
    moreover have "K ! m = rest ! m"
      unfolding K_def using mK[unfolded K_def] by (rule takeWhile_nth)
    ultimately show ?thesis using jj(2) Suc by simp
  qed
  have jn: "jj \<le> n" using jj(1) tcl(2) unfolding t_def by simp
  have lj: "p < p + Suc jj" by simp
  have ljt: "p + Suc jj \<le> Suc p + t" using jj(1) unfolding t_def by simp
  have "snd (H' ! (p + Suc jj)) \<le> max (snd (H' ! p)) (snd (H' ! Suc p))"
    using GH[unfolded ginv_def, rule_format, of p n t "p + Suc jj"]
      lenH dom tcl clw lj ljt by blast
  thus ?thesis using nthW[OF jn] jx nthpp nthc0 ud by simp
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

text \<open>Host-level sibling-run invariant (repaired, cf. memo 続29: the earlier
  equal-or-prefix-with-head-max form is FALSE on \<open>ST_PS\<close>).  At every adjacent
  tie-sibling pair the second run \<open>K1\<close> relates to the first run \<open>K\<close> by
  \<open>sibrel\<close>: equal, or a proper prefix, or — with both runs head-maximal —
  a first-difference descent (same level and smaller row 1, or smaller level
  and same row 1).  Empirically exact at closure+2 sampling: 58116 pairs,
  families E 44567 / P 12941 / F1 324 / F2 284, zero others; head-max can
  fail only in the equal family.\<close>

definition mrun :: "pairseq \<Rightarrow> nat \<Rightarrow> pairseq" where
  "mrun M a = takeWhile (\<lambda>r. fst (M ! a) < fst r) (drop (Suc a) M)"

definition sibrel :: "pairseq \<Rightarrow> pairseq \<Rightarrow> bool" where
  "sibrel K K1 \<longleftrightarrow> K1 = K
     \<or> (\<exists>D. D \<noteq> [] \<and> K = K1 @ D)
     \<or> (\<exists>p x x1 r r1. K = p @ x # r \<and> K1 = p @ x1 # r1
          \<and> (fst x1 < fst x \<or> (fst x1 = fst x \<and> snd x1 < snd x)))"

definition sibm2 :: "pairseq \<Rightarrow> bool" where
  "sibm2 M \<longleftrightarrow> (\<forall>a b. a < length M \<longrightarrow> 0 < fst (M ! a) \<longrightarrow>
      b = Suc a + length (mrun M a) \<longrightarrow> b < length M \<longrightarrow>
      fst (M ! b) = fst (M ! a) \<longrightarrow> snd (M ! b) = snd (M ! a) \<longrightarrow>
      sibrel (mrun M a) (mrun M b))"

lemma sibm2_diagSeq: "sibm2 (diagSeq 0 v)"
proof -
  have len: "length (diagSeq 0 v) = Suc v" unfolding diagSeq_def by simp
  have nth: "\<And>j. j < Suc v \<Longrightarrow> diagSeq 0 v ! j = (j, j)"
    unfolding diagSeq_def by (simp del: upt_Suc)
  show ?thesis
    unfolding sibm2_def
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
    thus "sibrel (mrun (diagSeq 0 v) a) (mrun (diagSeq 0 v) b)"
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

lemma hm_take:
  assumes ne: "take s K1 \<noteq> []" and hm: "snd (hd K1) = maxr1 K1"
  shows "snd (hd (take s K1)) = maxr1 (take s K1)"
proof -
  have ne1: "K1 \<noteq> []" using ne by auto
  have hdeq: "hd (take s K1) = hd K1"
    using ne by (cases K1; cases s) auto
  have sub: "snd ` set (take s K1) \<subseteq> snd ` set K1"
    using set_take_subset by fastforce
  have "maxr1 (take s K1) \<le> maxr1 K1"
    unfolding maxr1_def using ne sub by (intro Max_mono) auto
  moreover have "snd (hd (take s K1)) \<le> maxr1 (take s K1)"
    using maxr1_ub ne by (metis hd_in_set)
  ultimately show ?thesis using hm hdeq by simp
qed

text \<open>Tie-run row-1 bounds (GRAND components T1/T3, memo 続33/続38): at any
  snd-tie run stop, every run element's row 1 is at most one above the tie
  value (\<open>t1ok\<close>), and exactly bounded by it when the run head ties (\<open>t3ok\<close>).
  (Empirically exact at closure+1: 13106 resp. 8097 pairs, zero violations,
  including non-level-tie stops.)\<close>

definition t1ok :: "pairseq \<Rightarrow> bool" where
  "t1ok M \<longleftrightarrow> (\<forall>a b. a < length M \<longrightarrow> 0 < fst (M ! a) \<longrightarrow>
      b = Suc a + length (mrun M a) \<longrightarrow> b < length M \<longrightarrow>
      snd (M ! b) = snd (M ! a) \<longrightarrow>
      (\<forall>x \<in> set (mrun M a). snd x \<le> Suc (snd (M ! a))))"

definition t3ok :: "pairseq \<Rightarrow> bool" where
  "t3ok M \<longleftrightarrow> (\<forall>a b. a < length M \<longrightarrow> 0 < fst (M ! a) \<longrightarrow>
      b = Suc a + length (mrun M a) \<longrightarrow> b < length M \<longrightarrow>
      snd (M ! b) = snd (M ! a) \<longrightarrow>
      mrun M a \<noteq> [] \<longrightarrow> snd (hd (mrun M a)) = snd (M ! a) \<longrightarrow>
      (\<forall>x \<in> set (mrun M a). snd x \<le> snd (M ! a)))"

lemma tie_diag_absurd:
  assumes bp: "b = Suc a + length (mrun (diagSeq 0 v) a)"
    and bl: "b < length (diagSeq 0 v)"
    and sb: "snd (diagSeq 0 v ! b) = snd (diagSeq 0 v ! a)"
  shows False
proof -
  have len: "length (diagSeq 0 v) = Suc v" unfolding diagSeq_def by simp
  have nth: "\<And>j. j < Suc v \<Longrightarrow> diagSeq 0 v ! j = (j, j)"
    unfolding diagSeq_def by (simp del: upt_Suc)
  have ab: "a < b" using bp by linarith
  have "a < Suc v" using ab bl len by simp
  hence "snd (diagSeq 0 v ! a) = a" using nth by simp
  moreover have "snd (diagSeq 0 v ! b) = b" using nth bl len by simp
  ultimately show False using sb ab by simp
qed

lemma t1ok_diagSeq: "t1ok (diagSeq 0 v)"
  unfolding t1ok_def using tie_diag_absurd by blast

lemma t3ok_diagSeq: "t3ok (diagSeq 0 v)"
  unfolding t3ok_def using tie_diag_absurd by blast

lemma tie_take_pair:
  assumes bp: "b = Suc a + length (mrun (take m M) a)"
    and bl: "b < length (take m M)"
  shows "mrun (take m M) a = mrun M a"
proof -
  have am: "a < m" using bp bl by simp
  have bm: "b < m" using bl by simp
  have mt: "mrun (take m M) a = take (m - Suc a) (mrun M a)"
    by (rule mrun_take[OF am])
  have lt: "length (mrun (take m M) a) = b - Suc a" using bp by simp
  have ne: "b - Suc a < m - Suc a" using bp bm by arith
  have mineq: "min (m - Suc a) (length (mrun M a)) = b - Suc a"
    using mt lt by simp
  have "length (mrun M a) = b - Suc a"
  proof (cases "m - Suc a \<le> length (mrun M a)")
    case True
    hence "min (m - Suc a) (length (mrun M a)) = m - Suc a" by simp
    thus ?thesis using mineq ne by simp
  next
    case False
    hence "min (m - Suc a) (length (mrun M a)) = length (mrun M a)" by simp
    thus ?thesis using mineq by simp
  qed
  thus ?thesis using ne unfolding mt by simp
qed

lemma t1ok_take:
  assumes T: "t1ok M" shows "t1ok (take m M)"
  unfolding t1ok_def
proof (intro allI impI)
  fix a b
  assume al: "a < length (take m M)" and pos: "0 < fst (take m M ! a)"
    and bp: "b = Suc a + length (mrun (take m M) a)"
    and bl: "b < length (take m M)"
    and sb: "snd (take m M ! b) = snd (take m M ! a)"
  have mr: "mrun (take m M) a = mrun M a" by (rule tie_take_pair[OF bp bl])
  have aM: "a < length M" and am: "a < m" using al by simp_all
  have bM: "b < length M" and bm: "b < m" using bl by simp_all
  have na: "take m M ! a = M ! a" using am by simp
  have nb: "take m M ! b = M ! b" using bm by simp
  show "\<forall>x \<in> set (mrun (take m M) a). snd x \<le> Suc (snd (take m M ! a))"
    using T[unfolded t1ok_def, rule_format, of a b] aM bM bp[unfolded mr]
      pos[unfolded na] sb[unfolded na nb] unfolding mr na by blast
qed

lemma t3ok_take:
  assumes T: "t3ok M" shows "t3ok (take m M)"
  unfolding t3ok_def
proof (intro allI impI)
  fix a b
  assume al: "a < length (take m M)" and pos: "0 < fst (take m M ! a)"
    and bp: "b = Suc a + length (mrun (take m M) a)"
    and bl: "b < length (take m M)"
    and sb: "snd (take m M ! b) = snd (take m M ! a)"
    and ne: "mrun (take m M) a \<noteq> []"
    and hd1: "snd (hd (mrun (take m M) a)) = snd (take m M ! a)"
  have mr: "mrun (take m M) a = mrun M a" by (rule tie_take_pair[OF bp bl])
  have aM: "a < length M" and am: "a < m" using al by simp_all
  have bM: "b < length M" and bm: "b < m" using bl by simp_all
  have na: "take m M ! a = M ! a" using am by simp
  have nb: "take m M ! b = M ! b" using bm by simp
  show "\<forall>x \<in> set (mrun (take m M) a). snd x \<le> snd (take m M ! a)"
    using T[unfolded t3ok_def, rule_format, of a b] aM bM bp[unfolded mr]
      pos[unfolded na] sb[unfolded na nb] ne[unfolded mr] hd1[unfolded mr na]
    unfolding mr na by blast
qed

lemma t1ok_butlast: "t1ok M \<Longrightarrow> t1ok (butlast M)"
  using t1ok_take[of M "length M - 1"] by (simp add: butlast_conv_take)

lemma t3ok_butlast: "t3ok M \<Longrightarrow> t3ok (butlast M)"
  using t3ok_take[of M "length M - 1"] by (simp add: butlast_conv_take)

text \<open>(T14) The stop column's own run after an snd-tie is head-maximal
  (closure+1: 705 runs, zero violations, both open and closed).\<close>

definition t14ok :: "pairseq \<Rightarrow> bool" where
  "t14ok M \<longleftrightarrow> (\<forall>a b. a < length M \<longrightarrow> 0 < fst (M ! a) \<longrightarrow>
      b = Suc a + length (mrun M a) \<longrightarrow> b < length M \<longrightarrow>
      snd (M ! b) = snd (M ! a) \<longrightarrow> mrun M b \<noteq> [] \<longrightarrow>
      snd (M ! b) \<le> snd (hd (mrun M b)) \<longrightarrow>
      snd (hd (mrun M b)) = maxr1 (mrun M b))"

lemma t14ok_diagSeq: "t14ok (diagSeq 0 v)"
  unfolding t14ok_def using tie_diag_absurd by blast

lemma t14ok_take:
  assumes T: "t14ok M" shows "t14ok (take m M)"
  unfolding t14ok_def
proof (intro allI impI)
  fix a b
  assume al: "a < length (take m M)" and pos: "0 < fst (take m M ! a)"
    and bp: "b = Suc a + length (mrun (take m M) a)"
    and bl: "b < length (take m M)"
    and sb: "snd (take m M ! b) = snd (take m M ! a)"
    and ne: "mrun (take m M) b \<noteq> []"
    and hi: "snd (take m M ! b) \<le> snd (hd (mrun (take m M) b))"
  have mr: "mrun (take m M) a = mrun M a" by (rule tie_take_pair[OF bp bl])
  have aM: "a < length M" and am: "a < m" using al by simp_all
  have bM: "b < length M" and bm: "b < m" using bl by simp_all
  have na: "take m M ! a = M ! a" using am by simp
  have nb: "take m M ! b = M ! b" using bm by simp
  have mrb: "mrun (take m M) b = take (m - Suc b) (mrun M b)"
    by (rule mrun_take[OF bm])
  have neM: "mrun M b \<noteq> []" using ne mrb by auto
  have hdeqb: "hd (mrun (take m M) b) = hd (mrun M b)"
    using ne unfolding mrb by (cases "mrun M b"; cases "m - Suc b") auto
  have hiM: "snd (M ! b) \<le> snd (hd (mrun M b))"
    using hi hdeqb nb by simp
  have hmM: "snd (hd (mrun M b)) = maxr1 (mrun M b)"
    using T[unfolded t14ok_def, rule_format, of a b] aM bM bp[unfolded mr]
      pos[unfolded na] sb[unfolded na nb] neM hiM by blast
  show "snd (hd (mrun (take m M) b)) = maxr1 (mrun (take m M) b)"
    unfolding mrb by (rule hm_take[OF ne[unfolded mrb] hmM])
qed

lemma t14ok_butlast: "t14ok M \<Longrightarrow> t14ok (butlast M)"
  using t14ok_take[of M "length M - 1"] by (simp add: butlast_conv_take)

lemma t14ok_oper_bad:
  assumes T: "t1ok M" and T3: "t3ok M" and T14: "t14ok M"
    and B: "blockok 0 M" and ST: "M \<in> ST_PS" and n1: "1 \<le> n"
    and j1d: "j1 = Lng M - 1" and j1nz: "j1 \<noteq> 0"
    and Fz: "\<not> (entry M 0 j1 = 0 \<and> entry M 1 j1 = 0)"
    and i1d: "i1 = idx1 M j1" and hp: "hasParent M i1 j1"
    and j0d: "j0 = parent M i1 j1"
    and d0d: "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
    and opeq: "X = take j0 M @ concat (map (\<lambda>k.
           map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j)) [j0..<j1]) [0..<n])"
  shows "t14ok X"
  sorry

text \<open>(BT-WIN / BT-WRAP) The unified block-window row-1 invariants
  (memo 続45): a dominated in-block window closed by a level drop is bounded
  one above its anchor — no tie required (closure+2: 40344 / T3 7207, zero
  violations); for exact copies (\<open>d0 = 0\<close>) the head-tie full-tail form holds
  (closure+2: 18144 / T3 without the \<open>d0\<close> restriction 5251, zero violations).
  \<open>ginv_BT1\<close>/\<open>ginv_BT1_T3\<close> are corollaries.\<close>

text \<open>\<open>btfullok\<close>: the UNIVERSAL window row-1 bound (memo 続48) — on any
  standard host, any dominated window closed by a level drop is bounded one
  above its anchor; with a head tie, exactly by it.  (Closure+2: 65178 resp.
  41100 windows, zero violations; no bad-branch context needed.)\<close>

definition btfullok :: "pairseq \<Rightarrow> bool" where
  "btfullok M \<longleftrightarrow> (\<forall>a om l. om < length M \<longrightarrow>
      (\<forall>k. a < k \<and> k < om \<longrightarrow> fst (M ! a) < fst (M ! k)) \<longrightarrow>
      fst (M ! om) \<le> fst (M ! a) \<longrightarrow> a < l \<longrightarrow> l < om \<longrightarrow>
      snd (M ! l) \<le> Suc (snd (M ! a)))"

definition btfullok3 :: "pairseq \<Rightarrow> bool" where
  "btfullok3 M \<longleftrightarrow> (\<forall>a om l. om < length M \<longrightarrow>
      (\<forall>k. a < k \<and> k < om \<longrightarrow> fst (M ! a) < fst (M ! k)) \<longrightarrow>
      fst (M ! om) \<le> fst (M ! a) \<longrightarrow>
      snd (M ! Suc a) = snd (M ! a) \<longrightarrow> a < l \<longrightarrow> l < om \<longrightarrow>
      snd (M ! l) \<le> snd (M ! a))"

lemma btfull_diag_absurd:
  assumes dom: "\<forall>k. a < k \<and> k < om \<longrightarrow>
      fst (diagSeq 0 v ! a) < fst (diagSeq 0 v ! k)"
    and st: "fst (diagSeq 0 v ! om) \<le> fst (diagSeq 0 v ! a)"
    and bl: "om < length (diagSeq 0 v)"
    and al: "a < l" and lo: "l < om"
  shows False
proof -
  have len: "length (diagSeq 0 v) = Suc v" unfolding diagSeq_def by simp
  have nth: "\<And>j. j < Suc v \<Longrightarrow> diagSeq 0 v ! j = (j, j)"
    unfolding diagSeq_def by (simp del: upt_Suc)
  have ao: "a < om" using al lo by simp
  have "fst (diagSeq 0 v ! om) = om" using nth bl len by simp
  moreover have "fst (diagSeq 0 v ! a) = a" using nth bl len ao by simp
  ultimately show False using st ao by simp
qed

lemma btfullok_diagSeq: "btfullok (diagSeq 0 v)"
  unfolding btfullok_def using btfull_diag_absurd by blast

lemma btfullok3_diagSeq: "btfullok3 (diagSeq 0 v)"
  unfolding btfullok3_def using btfull_diag_absurd by blast

lemma btfullok_take:
  assumes T: "btfullok M" shows "btfullok (take m M)"
  unfolding btfullok_def
proof (intro allI impI)
  fix a om l
  assume bl: "om < length (take m M)"
    and dom: "\<forall>k. a < k \<and> k < om \<longrightarrow> fst (take m M ! a) < fst (take m M ! k)"
    and st: "fst (take m M ! om) \<le> fst (take m M ! a)"
    and al: "a < l" and lo: "l < om"
  have bm: "om < m" and bM: "om < length M" using bl by simp_all
  have nt: "\<And>j. j \<le> om \<Longrightarrow> take m M ! j = M ! j" using bm by auto
  have dom': "\<forall>k. a < k \<and> k < om \<longrightarrow> fst (M ! a) < fst (M ! k)"
  proof (intro allI impI)
    fix k assume kk: "a < k \<and> k < om"
    have "fst (take m M ! a) < fst (take m M ! k)" using dom kk by blast
    thus "fst (M ! a) < fst (M ! k)" using nt kk al lo by simp
  qed
  have st': "fst (M ! om) \<le> fst (M ! a)" using st nt al lo by simp
  have "snd (M ! l) \<le> Suc (snd (M ! a))"
    using T[unfolded btfullok_def, rule_format, of om a l] bM dom' st' al lo by blast
  thus "snd (take m M ! l) \<le> Suc (snd (take m M ! a))" using nt al lo by simp
qed

lemma btfullok3_take:
  assumes T: "btfullok3 M" shows "btfullok3 (take m M)"
  unfolding btfullok3_def
proof (intro allI impI)
  fix a om l
  assume bl: "om < length (take m M)"
    and dom: "\<forall>k. a < k \<and> k < om \<longrightarrow> fst (take m M ! a) < fst (take m M ! k)"
    and st: "fst (take m M ! om) \<le> fst (take m M ! a)"
    and ht: "snd (take m M ! Suc a) = snd (take m M ! a)"
    and al: "a < l" and lo: "l < om"
  have bm: "om < m" and bM: "om < length M" using bl by simp_all
  have nt: "\<And>j. j \<le> om \<Longrightarrow> take m M ! j = M ! j" using bm by auto
  have dom': "\<forall>k. a < k \<and> k < om \<longrightarrow> fst (M ! a) < fst (M ! k)"
  proof (intro allI impI)
    fix k assume kk: "a < k \<and> k < om"
    have "fst (take m M ! a) < fst (take m M ! k)" using dom kk by blast
    thus "fst (M ! a) < fst (M ! k)" using nt kk al lo by simp
  qed
  have st': "fst (M ! om) \<le> fst (M ! a)" using st nt al lo by simp
  have ht': "snd (M ! Suc a) = snd (M ! a)" using ht nt al lo by simp
  have "snd (M ! l) \<le> snd (M ! a)"
    using T[unfolded btfullok3_def, rule_format, of om a l] bM dom' st' ht' al lo by blast
  thus "snd (take m M ! l) \<le> snd (take m M ! a)" using nt al lo by simp
qed

lemma btfullok_butlast: "btfullok M \<Longrightarrow> btfullok (butlast M)"
  using btfullok_take[of M "length M - 1"] by (simp add: butlast_conv_take)

lemma btfullok3_butlast: "btfullok3 M \<Longrightarrow> btfullok3 (butlast M)"
  using btfullok3_take[of M "length M - 1"] by (simp add: butlast_conv_take)


lemma btfullok_oper_bad:
  assumes BF: "btfullok M" and BF3: "btfullok3 M"
    and B: "blockok 0 M" and ST: "M \<in> ST_PS" and n1: "1 \<le> n"
    and j1d: "j1 = Lng M - 1" and j1nz: "j1 \<noteq> 0"
    and Fz: "\<not> (entry M 0 j1 = 0 \<and> entry M 1 j1 = 0)"
    and i1d: "i1 = idx1 M j1" and hp: "hasParent M i1 j1"
    and j0d: "j0 = parent M i1 j1"
    and d0d: "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
    and opeq: "X = take j0 M @ concat (map (\<lambda>k.
           map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j)) [j0..<j1]) [0..<n])"
  shows "btfullok X"
proof -
  have nR: "nextR M i1 j0 j1" unfolding j0d by (rule parent_nextR[OF hp])
  have j0j1: "j0 < j1" using nR by (rule nextR_less)
  have lenM: "length M = Suc j1" using j1d j1nz by (cases M) auto
  have j1len: "j1 < length M" using lenM by simp
  define L where "L = j1 - j0"
  have L0: "0 < L" unfolding L_def using j0j1 by simp
  have lenX: "length X = j0 + n * L"
    unfolding L_def by (rule oper_bad_len[OF opeq j0j1 j1len])
  have npre: "\<And>i. i < j0 \<Longrightarrow> X ! i = M ! i"
    using oper_bad_nth_pre[OF opeq _ j1len j0j1] by blast
  have ncopy: "\<And>k q. k < n \<Longrightarrow> q < L \<Longrightarrow>
        X ! (j0 + (k * L + q)) = (entry M 0 (j0 + q) + k * d0, entry M 1 (j0 + q))"
    unfolding L_def using oper_bad_nth_copy[OF opeq j0j1 j1len] by blast
  have hm0: "\<forall>k. j0 < k \<and> k \<le> j1 \<longrightarrow> entry M 0 j0 < entry M 0 k"
    by (rule block_head_min[OF hp j0d])
  have pairM: "\<And>j. (entry M 0 j, entry M 1 j) = M ! j"
    unfolding entry_def by simp
  have j0Lj1: "j0 + L = j1" unfolding L_def using j0j1 by simp
  have Xv0: "\<And>i. i < j0 + L \<Longrightarrow> X ! i = M ! i"
  proof -
    fix i assume iL: "i < j0 + L"
    show "X ! i = M ! i"
    proof (cases "i < j0")
      case True thus ?thesis by (rule npre)
    next
      case False
      have qL: "i - j0 < L" using iL False by simp
      have c0: "X ! (j0 + (0 * L + (i - j0)))
          = (entry M 0 (j0 + (i - j0)) + 0 * d0, entry M 1 (j0 + (i - j0)))"
        by (rule ncopy) (use n1 qL in simp_all)
      have ii: "j0 + (i - j0) = i" using False by simp
      have "X ! i = (entry M 0 i, entry M 1 i)" using c0 ii by simp
      thus ?thesis using pairM by simp
    qed
  qed
  have idxE: "\<And>i. j0 \<le> i \<Longrightarrow> i < length X \<Longrightarrow>
       \<exists>k q. k < n \<and> q < L \<and> i = j0 + (k * L + q)
           \<and> X ! i = (entry M 0 (j0 + q) + k * d0, entry M 1 (j0 + q))"
  proof -
    fix i assume ji: "j0 \<le> i" and iX: "i < length X"
    define k where "k = (i - j0) div L"
    define q where "q = (i - j0) mod L"
    have kq: "i - j0 = k * L + q" unfolding k_def q_def by simp
    have qL: "q < L" unfolding q_def using L0 by simp
    have kn: "k < n"
    proof -
      have "i - j0 < n * L" using iX lenX ji by simp
      thus ?thesis unfolding k_def
        by (metis less_mult_imp_div_less mult.commute)
    qed
    have ii: "i = j0 + (k * L + q)" using kq ji by simp
    have "X ! (j0 + (k * L + q)) = (entry M 0 (j0 + q) + k * d0, entry M 1 (j0 + q))"
      by (rule ncopy[OF kn qL])
    thus "\<exists>k q. k < n \<and> q < L \<and> i = j0 + (k * L + q)
           \<and> X ! i = (entry M 0 (j0 + q) + k * d0, entry M 1 (j0 + q))"
      using kn qL ii by blast
  qed
  show ?thesis
    unfolding btfullok_def
  proof (intro allI impI)
    fix a om l
    assume bl: "om < length X"
      and dom: "\<forall>k. a < k \<and> k < om \<longrightarrow> fst (X ! a) < fst (X ! k)"
      and st: "fst (X ! om) \<le> fst (X ! a)"
      and al: "a < l" and lo: "l < om"
    have ao: "a < om" using al lo by simp
    show "snd (X ! l) \<le> Suc (snd (X ! a))"
    proof (cases "om < j0 + L")
      case A: True
      have XM: "\<And>i. i \<le> om \<Longrightarrow> X ! i = M ! i"
      proof -
        fix i assume "i \<le> om"
        hence "i < j0 + L" using A by simp
        thus "X ! i = M ! i" by (rule Xv0)
      qed
      have omM: "om < length M" using A j0Lj1 j1len by simp
      have dom': "\<forall>k. a < k \<and> k < om \<longrightarrow> fst (M ! a) < fst (M ! k)"
      proof (intro allI impI)
        fix k assume kk: "a < k \<and> k < om"
        have "fst (X ! a) < fst (X ! k)" using dom kk by blast
        thus "fst (M ! a) < fst (M ! k)" using XM kk ao by simp
      qed
      have st': "fst (M ! om) \<le> fst (M ! a)" using st XM ao by simp
      have "snd (M ! l) \<le> Suc (snd (M ! a))"
        using BF[unfolded btfullok_def, rule_format, of om a l]
          omM dom' st' al lo by blast
      thus ?thesis using XM al lo ao by simp
    next
      case B: False
      hence Bge: "j0 + L \<le> om" by simp
      show ?thesis
      proof (cases "a < j0")
        case apre: True
        have j0in: "a < j0 \<and> j0 < om" using apre Bge L0 by simp
        have "fst (X ! a) < fst (X ! j0)" using dom j0in by blast
        moreover have "X ! j0 = M ! j0" using Xv0 L0 by simp
        ultimately have aj0lev: "fst (X ! a) < entry M 0 j0"
          unfolding entry_def by simp
        have omj0: "j0 \<le> om" using Bge L0 by simp
        obtain ko qo where ko: "ko < n" "qo < L" "om = j0 + (ko * L + qo)"
            and Xo: "X ! om = (entry M 0 (j0 + qo) + ko * d0, entry M 1 (j0 + qo))"
          using idxE[OF omj0 bl] by blast
        have e0qo: "entry M 0 j0 \<le> entry M 0 (j0 + qo)"
        proof (cases qo)
          case 0 thus ?thesis by simp
        next
          case (Suc q')
          have "j0 < j0 + qo \<and> j0 + qo \<le> j1" using Suc ko(2) j0Lj1 by simp
          thus ?thesis using hm0 by fastforce
        qed
        have "entry M 0 j0 \<le> fst (X ! om)" using Xo e0qo by simp
        thus ?thesis using st aj0lev by simp
      next
        case False
        hence aj0: "j0 \<le> a" by simp
        obtain ka qa where ka: "ka < n" "qa < L" "a = j0 + (ka * L + qa)"
            and Xa: "X ! a = (entry M 0 (j0 + qa) + ka * d0, entry M 1 (j0 + qa))"
          using idxE[OF aj0] bl ao by (meson dual_order.strict_trans)
        have omj0: "j0 \<le> om" using aj0 ao by simp
        obtain ko qo where ko: "ko < n" "qo < L" "om = j0 + (ko * L + qo)"
            and Xo: "X ! om = (entry M 0 (j0 + qo) + ko * d0, entry M 1 (j0 + qo))"
          using idxE[OF omj0 bl] by blast
        define h where "h = j0 + ((ka + 1) * L + 0)"
        have hN: "h = j0 + (L + ka * L)" unfolding h_def by simp
        have ah: "a < h" unfolding hN using ka(3) ka(2) by simp
        show ?thesis
        proof (cases "om < h")
          case sameC: True
          have koka: "ko = ka"
          proof -
            have le1: "ko * L + qo < L + ka * L" using ko(3) sameC unfolding hN by simp
            have le2: "ka * L + qa < ko * L + qo" using ka(3) ko(3) ao by simp
            have "ko \<le> ka"
            proof (rule ccontr)
              assume "\<not> ko \<le> ka"
              hence "Suc ka \<le> ko" by simp
              hence "Suc ka * L \<le> ko * L" by (rule mult_le_mono1)
              hence "L + ka * L \<le> ko * L" by simp
              thus False using le1 by arith
            qed
            moreover have "ka \<le> ko"
            proof (rule ccontr)
              assume "\<not> ka \<le> ko"
              hence "Suc ko \<le> ka" by simp
              hence "Suc ko * L \<le> ka * L" by (rule mult_le_mono1)
              hence "L + ko * L \<le> ka * L" by simp
              thus False using le2 ko(2) by arith
            qed
            ultimately show ?thesis by simp
          qed
          have qaqo: "qa < qo" using ka(3) ko(3) koka ao by arith
          have lj0: "j0 \<le> l" using aj0 al by simp
          have lX: "l < length X" using bl lo by simp
          obtain kl ql where kl: "kl < n" "ql < L" "l = j0 + (kl * L + ql)"
              and Xl: "X ! l = (entry M 0 (j0 + ql) + kl * d0, entry M 1 (j0 + ql))"
            using idxE[OF lj0 lX] by blast
          have klka: "kl = ka"
          proof -
            have lo1: "kl * L + ql < ko * L + qo" using kl(3) ko(3) lo by arith
            have lo2: "ka * L + qa < kl * L + ql" using ka(3) kl(3) al by arith
            have "kl \<le> ko"
            proof (rule ccontr)
              assume "\<not> kl \<le> ko"
              hence "Suc ko \<le> kl" by simp
              hence "L + ko * L \<le> kl * L" using mult_le_mono1[of "Suc ko" kl L] by simp
              thus False using lo1 ko(2) by arith
            qed
            moreover have "ka \<le> kl"
            proof (rule ccontr)
              assume "\<not> ka \<le> kl"
              hence "Suc kl \<le> ka" by simp
              hence "L + kl * L \<le> ka * L" using mult_le_mono1[of "Suc kl" ka L] by simp
              thus False using lo2 kl(2) by arith
            qed
            ultimately show ?thesis using koka by simp
          qed
          have qlrange: "qa < ql \<and> ql < qo"
            using ka(3) kl(3) ko(3) klka koka al lo by arith
          have omM: "j0 + qo < length M" using ko(2) j0Lj1 j1len by arith
          have dom': "\<forall>k. j0 + qa < k \<and> k < j0 + qo \<longrightarrow>
              fst (M ! (j0 + qa)) < fst (M ! k)"
          proof (intro allI impI)
            fix k assume kk: "j0 + qa < k \<and> k < j0 + qo"
            define qq where "qq = k - j0"
            have ke: "k = j0 + qq" unfolding qq_def using kk by arith
            have qr: "qa < qq \<and> qq < qo" unfolding qq_def using kk by arith
            have qqL: "qq < L" using qr ko(2) by arith
            have idx: "a + (qq - qa) = j0 + (ka * L + qq)" using ka(3) qr by arith
            have win: "a < a + (qq - qa) \<and> a + (qq - qa) < om"
              using qr ka(3) ko(3) koka by arith
            have "fst (X ! a) < fst (X ! (a + (qq - qa)))" using dom win by blast
            moreover have "X ! (a + (qq - qa))
                = (entry M 0 (j0 + qq) + ka * d0, entry M 1 (j0 + qq))"
              unfolding idx by (rule ncopy[OF ka(1) qqL])
            ultimately have "entry M 0 (j0 + qa) < entry M 0 (j0 + qq)" using Xa by simp
            thus "fst (M ! (j0 + qa)) < fst (M ! k)" unfolding ke entry_def by simp
          qed
          have st': "fst (M ! (j0 + qo)) \<le> fst (M ! (j0 + qa))"
            using st Xa Xo koka unfolding entry_def by simp
          have "snd (M ! (j0 + ql)) \<le> Suc (snd (M ! (j0 + qa)))"
            using BF[unfolded btfullok_def, rule_format, of "j0 + qo" "j0 + qa" "j0 + ql"]
              omM dom' st' qlrange by simp
          thus ?thesis using Xa Xl klka unfolding entry_def by simp
        next
          case notlt: False
          show ?thesis
          proof (cases "om = h")
            case omh: True
            have ka1n: "ka + 1 < n"
            proof -
              have "h < length X" using omh bl by simp
              hence "(ka + 1) * L < n * L" unfolding h_def lenX by simp
              thus ?thesis using L0
                by (metis gr_implies_not0 less_mult_imp_div_less nonzero_mult_div_cancel_right)
            qed
            have Xh: "X ! h = (entry M 0 j0 + (ka + 1) * d0, entry M 1 j0)"
              unfolding h_def using ncopy[OF ka1n L0] by simp
            have stp: "entry M 0 j0 + (ka + 1) * d0 \<le> entry M 0 (j0 + qa) + ka * d0"
              using st Xa Xh omh by simp
            have dag: "entry M 0 j0 + d0 \<le> entry M 0 (j0 + qa)" using stp by simp
            have lj0: "j0 \<le> l" using aj0 al by simp
            have lX: "l < length X" using bl lo by simp
            obtain kl ql where kl: "kl < n" "ql < L" "l = j0 + (kl * L + ql)"
                and Xl: "X ! l = (entry M 0 (j0 + ql) + kl * d0, entry M 1 (j0 + ql))"
              using idxE[OF lj0 lX] by blast
            have klka: "kl = ka \<and> qa < ql"
            proof -
              have lo1: "kl * L + ql < L + ka * L" using kl(3) omh lo unfolding hN by arith
              have lo2: "ka * L + qa < kl * L + ql" using ka(3) kl(3) al by arith
              have "kl \<le> ka"
              proof (rule ccontr)
                assume "\<not> kl \<le> ka"
                hence "Suc ka \<le> kl" by simp
                hence "L + ka * L \<le> kl * L" using mult_le_mono1[of "Suc ka" kl L] by simp
                thus False using lo1 by arith
              qed
              moreover have "ka \<le> kl"
              proof (rule ccontr)
                assume "\<not> ka \<le> kl"
                hence "Suc kl \<le> ka" by simp
                hence "L + kl * L \<le> ka * L" using mult_le_mono1[of "Suc kl" ka L] by simp
                thus False using lo2 kl(2) by arith
              qed
              ultimately show ?thesis using lo2 by simp
            qed
            have domtail: "\<forall>q. qa < q \<and> q < L \<longrightarrow>
                entry M 0 (j0 + qa) < entry M 0 (j0 + q)"
            proof (intro allI impI)
              fix q assume qq: "qa < q \<and> q < L"
              have idx: "a + (q - qa) = j0 + (ka * L + q)" using ka(3) qq by arith
              have win: "a < a + (q - qa) \<and> a + (q - qa) < om"
                using qq ka(3) omh unfolding hN by arith
              have "fst (X ! a) < fst (X ! (a + (q - qa)))" using dom win by blast
              moreover have "X ! (a + (q - qa))
                  = (entry M 0 (j0 + q) + ka * d0, entry M 1 (j0 + q))"
                unfolding idx by (rule ncopy[OF ka(1)]) (use qq in simp)
              ultimately show "entry M 0 (j0 + qa) < entry M 0 (j0 + q)" using Xa by simp
            qed
            show ?thesis
            proof (cases "d0 = 0")
              case d00: True
              have stpu: "entry M 0 j0 \<le> entry M 0 (j0 + qa)" using dag d00 by simp
              have "entry M 1 (j0 + ql) \<le> Suc (entry M 1 (j0 + qa))"
                by (rule ginv_BTWRAPU[OF ST j1d j1nz Fz i1d hp j0d d0d d00 _ stpu
                      domtail[unfolded L_def]])
                   (use ka(2) klka kl(2) L_def in simp_all)
              thus ?thesis using Xa Xl klka by simp
            next
              case d0pos': False
              have d0pos: "0 < d0" using d0pos' by simp
              have i1one: "i1 = 1"
                using idx1_le[of M j1] d0d d0pos i1d by (cases i1) auto
              have e0j: "entry M 0 j0 < entry M 0 j1" using hm0 j0j1 by simp
              have d0ex: "entry M 0 j0 + d0 = entry M 0 j1"
                unfolding d0d using i1one e0j by simp
              have omM: "j1 < length M" by (rule j1len)
              have dom': "\<forall>k. j0 + qa < k \<and> k < j1 \<longrightarrow>
                  fst (M ! (j0 + qa)) < fst (M ! k)"
              proof (intro allI impI)
                fix k assume kk: "j0 + qa < k \<and> k < j1"
                define qq where "qq = k - j0"
                have ke: "k = j0 + qq" unfolding qq_def using kk by arith
                have qr: "qa < qq \<and> qq < L" unfolding qq_def L_def using kk by arith
                have "entry M 0 (j0 + qa) < entry M 0 (j0 + qq)" using domtail qr by blast
                thus "fst (M ! (j0 + qa)) < fst (M ! k)" unfolding ke entry_def by simp
              qed
              have st': "fst (M ! j1) \<le> fst (M ! (j0 + qa))"
                using dag d0ex unfolding entry_def by simp
              have lrange: "j0 + qa < j0 + ql \<and> j0 + ql < j1"
                using klka kl(2) j0Lj1 by arith
              have "snd (M ! (j0 + ql)) \<le> Suc (snd (M ! (j0 + qa)))"
                using BF[unfolded btfullok_def, rule_format, of j1 "j0 + qa" "j0 + ql"]
                  omM dom' st' lrange by blast
              thus ?thesis using Xa Xl klka unfolding entry_def by simp
            qed
          next
            case omgt': False
            have omgt: "h < om" using notlt omgt' by simp
            have hwin: "a < h \<and> h < om" using ah omgt by simp
            have ka1n: "ka + 1 < n"
            proof -
              have "h < length X" using omgt bl by simp
              hence "(ka + 1) * L < n * L" unfolding h_def lenX by simp
              thus ?thesis using L0
                by (metis gr_implies_not0 less_mult_imp_div_less nonzero_mult_div_cancel_right)
            qed
            have Xh: "X ! h = (entry M 0 j0 + (ka + 1) * d0, entry M 1 j0)"
              unfolding h_def using ncopy[OF ka1n L0] by simp
            have hdom: "fst (X ! a) < fst (X ! h)" using dom hwin by blast
            have star: "entry M 0 (j0 + qa) + ka * d0 < entry M 0 j0 + (ka + 1) * d0"
              using hdom Xa Xh by simp
            have starn: "entry M 0 (j0 + qa) + ka * d0 < entry M 0 j0 + d0 + ka * d0"
              using star by (simp add: algebra_simps)
            have kogt: "ka + 1 \<le> ko"
            proof -
              have "L + ka * L \<le> ko * L + qo" using ko(3) omgt unfolding hN by arith
              show ?thesis
              proof (rule ccontr)
                assume "\<not> ka + 1 \<le> ko"
                hence "ko \<le> ka" by simp
                hence "ko * L + qo < L + ka * L"
                  using ko(2) mult_le_mono1[of ko ka L] by arith
                thus False using \<open>L + ka * L \<le> ko * L + qo\<close> by arith
              qed
            qed
            have False
            proof (cases qo)
              case 0
              have "ka + 2 \<le> ko"
              proof (rule ccontr)
                assume "\<not> ka + 2 \<le> ko"
                hence "ko = ka + 1" using kogt by simp
                hence "om = h" using ko(3) 0 unfolding hN by simp
                thus False using omgt by simp
              qed
              hence "(ka + 2) * d0 \<le> ko * d0" by (rule mult_le_mono1)
              hence m2n: "d0 + d0 + ka * d0 \<le> ko * d0" by (simp add: algebra_simps)
              have "entry M 0 j0 + ko * d0 \<le> entry M 0 (j0 + qa) + ka * d0"
                using st Xa Xo 0 by simp
              thus False using m2n starn by arith
            next
              case (Suc q')
              have "j0 < j0 + qo \<and> j0 + qo \<le> j1" using Suc ko(2) j0Lj1 by arith
              hence e0qo: "entry M 0 j0 < entry M 0 (j0 + qo)" using hm0 by blast
              have "(ka + 1) * d0 \<le> ko * d0" using kogt by (rule mult_le_mono1)
              hence m1n: "d0 + ka * d0 \<le> ko * d0" by (simp add: algebra_simps)
              have "entry M 0 (j0 + qo) + ko * d0 \<le> entry M 0 (j0 + qa) + ka * d0"
                using st Xa Xo by simp
              thus False using m1n starn e0qo by arith
            qed
            thus ?thesis ..
          qed
        qed
      qed
    qed
  qed
qed

lemma btfullok3_oper_bad:
  assumes BF: "btfullok M" and BF3: "btfullok3 M"
    and B: "blockok 0 M" and ST: "M \<in> ST_PS" and n1: "1 \<le> n"
    and j1d: "j1 = Lng M - 1" and j1nz: "j1 \<noteq> 0"
    and Fz: "\<not> (entry M 0 j1 = 0 \<and> entry M 1 j1 = 0)"
    and i1d: "i1 = idx1 M j1" and hp: "hasParent M i1 j1"
    and j0d: "j0 = parent M i1 j1"
    and d0d: "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
    and opeq: "X = take j0 M @ concat (map (\<lambda>k.
           map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j)) [j0..<j1]) [0..<n])"
  shows "btfullok3 X"
proof -
  have nR: "nextR M i1 j0 j1" unfolding j0d by (rule parent_nextR[OF hp])
  have j0j1: "j0 < j1" using nR by (rule nextR_less)
  have lenM: "length M = Suc j1" using j1d j1nz by (cases M) auto
  have j1len: "j1 < length M" using lenM by simp
  define L where "L = j1 - j0"
  have L0: "0 < L" unfolding L_def using j0j1 by simp
  have lenX: "length X = j0 + n * L"
    unfolding L_def by (rule oper_bad_len[OF opeq j0j1 j1len])
  have npre: "\<And>i. i < j0 \<Longrightarrow> X ! i = M ! i"
    using oper_bad_nth_pre[OF opeq _ j1len j0j1] by blast
  have ncopy: "\<And>k q. k < n \<Longrightarrow> q < L \<Longrightarrow>
        X ! (j0 + (k * L + q)) = (entry M 0 (j0 + q) + k * d0, entry M 1 (j0 + q))"
    unfolding L_def using oper_bad_nth_copy[OF opeq j0j1 j1len] by blast
  have hm0: "\<forall>k. j0 < k \<and> k \<le> j1 \<longrightarrow> entry M 0 j0 < entry M 0 k"
    by (rule block_head_min[OF hp j0d])
  have pairM: "\<And>j. (entry M 0 j, entry M 1 j) = M ! j"
    unfolding entry_def by simp
  have j0Lj1: "j0 + L = j1" unfolding L_def using j0j1 by simp
  have Xv0: "\<And>i. i < j0 + L \<Longrightarrow> X ! i = M ! i"
  proof -
    fix i assume iL: "i < j0 + L"
    show "X ! i = M ! i"
    proof (cases "i < j0")
      case True thus ?thesis by (rule npre)
    next
      case False
      have qL: "i - j0 < L" using iL False by simp
      have c0: "X ! (j0 + (0 * L + (i - j0)))
          = (entry M 0 (j0 + (i - j0)) + 0 * d0, entry M 1 (j0 + (i - j0)))"
        by (rule ncopy) (use n1 qL in simp_all)
      have ii: "j0 + (i - j0) = i" using False by simp
      have "X ! i = (entry M 0 i, entry M 1 i)" using c0 ii by simp
      thus ?thesis using pairM by simp
    qed
  qed
  have idxE: "\<And>i. j0 \<le> i \<Longrightarrow> i < length X \<Longrightarrow>
       \<exists>k q. k < n \<and> q < L \<and> i = j0 + (k * L + q)
           \<and> X ! i = (entry M 0 (j0 + q) + k * d0, entry M 1 (j0 + q))"
  proof -
    fix i assume ji: "j0 \<le> i" and iX: "i < length X"
    define k where "k = (i - j0) div L"
    define q where "q = (i - j0) mod L"
    have kq: "i - j0 = k * L + q" unfolding k_def q_def by simp
    have qL: "q < L" unfolding q_def using L0 by simp
    have kn: "k < n"
    proof -
      have "i - j0 < n * L" using iX lenX ji by simp
      thus ?thesis unfolding k_def
        by (metis less_mult_imp_div_less mult.commute)
    qed
    have ii: "i = j0 + (k * L + q)" using kq ji by simp
    have "X ! (j0 + (k * L + q)) = (entry M 0 (j0 + q) + k * d0, entry M 1 (j0 + q))"
      by (rule ncopy[OF kn qL])
    thus "\<exists>k q. k < n \<and> q < L \<and> i = j0 + (k * L + q)
           \<and> X ! i = (entry M 0 (j0 + q) + k * d0, entry M 1 (j0 + q))"
      using kn qL ii by blast
  qed
  show ?thesis
    unfolding btfullok3_def
  proof (intro allI impI)
    fix a om l
    assume bl: "om < length X"
      and dom: "\<forall>k. a < k \<and> k < om \<longrightarrow> fst (X ! a) < fst (X ! k)"
      and st: "fst (X ! om) \<le> fst (X ! a)"
      and ht: "snd (X ! Suc a) = snd (X ! a)"
      and al: "a < l" and lo: "l < om"
    have ao: "a < om" using al lo by simp
    show "snd (X ! l) \<le> snd (X ! a)"
    proof (cases "om < j0 + L")
      case A: True
      have XM: "\<And>i. i \<le> om \<Longrightarrow> X ! i = M ! i"
      proof -
        fix i assume "i \<le> om"
        hence "i < j0 + L" using A by simp
        thus "X ! i = M ! i" by (rule Xv0)
      qed
      have omM: "om < length M" using A j0Lj1 j1len by simp
      have dom': "\<forall>k. a < k \<and> k < om \<longrightarrow> fst (M ! a) < fst (M ! k)"
      proof (intro allI impI)
        fix k assume kk: "a < k \<and> k < om"
        have "fst (X ! a) < fst (X ! k)" using dom kk by blast
        thus "fst (M ! a) < fst (M ! k)" using XM kk ao by simp
      qed
      have st': "fst (M ! om) \<le> fst (M ! a)" using st XM ao by simp
      have ht': "snd (M ! Suc a) = snd (M ! a)"
        using ht XM[of "Suc a"] XM[of a] al lo by simp
      have "snd (M ! l) \<le> snd (M ! a)"
        using BF3[unfolded btfullok3_def, rule_format, of om a l]
          omM dom' st' ht' al lo by blast
      thus ?thesis using XM al lo ao by simp
    next
      case B: False
      hence Bge: "j0 + L \<le> om" by simp
      show ?thesis
      proof (cases "a < j0")
        case apre: True
        have j0in: "a < j0 \<and> j0 < om" using apre Bge L0 by simp
        have "fst (X ! a) < fst (X ! j0)" using dom j0in by blast
        moreover have "X ! j0 = M ! j0" using Xv0 L0 by simp
        ultimately have aj0lev: "fst (X ! a) < entry M 0 j0"
          unfolding entry_def by simp
        have omj0: "j0 \<le> om" using Bge L0 by simp
        obtain ko qo where ko: "ko < n" "qo < L" "om = j0 + (ko * L + qo)"
            and Xo: "X ! om = (entry M 0 (j0 + qo) + ko * d0, entry M 1 (j0 + qo))"
          using idxE[OF omj0 bl] by blast
        have e0qo: "entry M 0 j0 \<le> entry M 0 (j0 + qo)"
        proof (cases qo)
          case 0 thus ?thesis by simp
        next
          case (Suc q')
          have "j0 < j0 + qo \<and> j0 + qo \<le> j1" using Suc ko(2) j0Lj1 by simp
          thus ?thesis using hm0 by fastforce
        qed
        have "entry M 0 j0 \<le> fst (X ! om)" using Xo e0qo by simp
        thus ?thesis using st aj0lev by simp
      next
        case False
        hence aj0: "j0 \<le> a" by simp
        obtain ka qa where ka: "ka < n" "qa < L" "a = j0 + (ka * L + qa)"
            and Xa: "X ! a = (entry M 0 (j0 + qa) + ka * d0, entry M 1 (j0 + qa))"
          using idxE[OF aj0] bl ao by (meson dual_order.strict_trans)
        have omj0: "j0 \<le> om" using aj0 ao by simp
        obtain ko qo where ko: "ko < n" "qo < L" "om = j0 + (ko * L + qo)"
            and Xo: "X ! om = (entry M 0 (j0 + qo) + ko * d0, entry M 1 (j0 + qo))"
          using idxE[OF omj0 bl] by blast
        define h where "h = j0 + ((ka + 1) * L + 0)"
        have hN: "h = j0 + (L + ka * L)" unfolding h_def by simp
        have ah: "a < h" unfolding hN using ka(3) ka(2) by simp
        show ?thesis
        proof (cases "om < h")
          case sameC: True
          have koka: "ko = ka"
          proof -
            have le1: "ko * L + qo < L + ka * L" using ko(3) sameC unfolding hN by simp
            have le2: "ka * L + qa < ko * L + qo" using ka(3) ko(3) ao by simp
            have "ko \<le> ka"
            proof (rule ccontr)
              assume "\<not> ko \<le> ka"
              hence "Suc ka \<le> ko" by simp
              hence "Suc ka * L \<le> ko * L" by (rule mult_le_mono1)
              hence "L + ka * L \<le> ko * L" by simp
              thus False using le1 by arith
            qed
            moreover have "ka \<le> ko"
            proof (rule ccontr)
              assume "\<not> ka \<le> ko"
              hence "Suc ko \<le> ka" by simp
              hence "Suc ko * L \<le> ka * L" by (rule mult_le_mono1)
              hence "L + ko * L \<le> ka * L" by simp
              thus False using le2 ko(2) by arith
            qed
            ultimately show ?thesis by simp
          qed
          have qaqo: "qa < qo" using ka(3) ko(3) koka ao by arith
          have lj0: "j0 \<le> l" using aj0 al by simp
          have lX: "l < length X" using bl lo by simp
          obtain kl ql where kl: "kl < n" "ql < L" "l = j0 + (kl * L + ql)"
              and Xl: "X ! l = (entry M 0 (j0 + ql) + kl * d0, entry M 1 (j0 + ql))"
            using idxE[OF lj0 lX] by blast
          have klka: "kl = ka"
          proof -
            have lo1: "kl * L + ql < ko * L + qo" using kl(3) ko(3) lo by arith
            have lo2: "ka * L + qa < kl * L + ql" using ka(3) kl(3) al by arith
            have "kl \<le> ko"
            proof (rule ccontr)
              assume "\<not> kl \<le> ko"
              hence "Suc ko \<le> kl" by simp
              hence "L + ko * L \<le> kl * L" using mult_le_mono1[of "Suc ko" kl L] by simp
              thus False using lo1 ko(2) by arith
            qed
            moreover have "ka \<le> kl"
            proof (rule ccontr)
              assume "\<not> ka \<le> kl"
              hence "Suc kl \<le> ka" by simp
              hence "L + kl * L \<le> ka * L" using mult_le_mono1[of "Suc kl" ka L] by simp
              thus False using lo2 kl(2) by arith
            qed
            ultimately show ?thesis using koka by simp
          qed
          have qlrange: "qa < ql \<and> ql < qo"
            using ka(3) kl(3) ko(3) klka koka al lo by arith
          have omM: "j0 + qo < length M" using ko(2) j0Lj1 j1len by arith
          have dom': "\<forall>k. j0 + qa < k \<and> k < j0 + qo \<longrightarrow>
              fst (M ! (j0 + qa)) < fst (M ! k)"
          proof (intro allI impI)
            fix k assume kk: "j0 + qa < k \<and> k < j0 + qo"
            define qq where "qq = k - j0"
            have ke: "k = j0 + qq" unfolding qq_def using kk by arith
            have qr: "qa < qq \<and> qq < qo" unfolding qq_def using kk by arith
            have qqL: "qq < L" using qr ko(2) by arith
            have idx: "a + (qq - qa) = j0 + (ka * L + qq)" using ka(3) qr by arith
            have win: "a < a + (qq - qa) \<and> a + (qq - qa) < om"
              using qr ka(3) ko(3) koka by arith
            have "fst (X ! a) < fst (X ! (a + (qq - qa)))" using dom win by blast
            moreover have "X ! (a + (qq - qa))
                = (entry M 0 (j0 + qq) + ka * d0, entry M 1 (j0 + qq))"
              unfolding idx by (rule ncopy[OF ka(1) qqL])
            ultimately have "entry M 0 (j0 + qa) < entry M 0 (j0 + qq)" using Xa by simp
            thus "fst (M ! (j0 + qa)) < fst (M ! k)" unfolding ke entry_def by simp
          qed
          have st': "fst (M ! (j0 + qo)) \<le> fst (M ! (j0 + qa))"
            using st Xa Xo koka unfolding entry_def by simp
          have sqaL: "Suc qa < L" using qlrange kl(2) klka by arith
          have idxsa: "Suc a = j0 + (ka * L + Suc qa)" using ka(3) by simp
          have Xsa: "X ! Suc a = (entry M 0 (j0 + Suc qa) + ka * d0, entry M 1 (j0 + Suc qa))"
            unfolding idxsa by (rule ncopy[OF ka(1) sqaL])
          have ht': "snd (M ! Suc (j0 + qa)) = snd (M ! (j0 + qa))"
          proof -
            have "entry M 1 (j0 + Suc qa) = entry M 1 (j0 + qa)" using ht Xsa Xa by simp
            thus ?thesis unfolding entry_def by simp
          qed
          have "snd (M ! (j0 + ql)) \<le> snd (M ! (j0 + qa))"
            using BF3[unfolded btfullok3_def, rule_format, of "j0 + qo" "j0 + qa" "j0 + ql"]
              omM dom' st' ht' qlrange by simp
          thus ?thesis using Xa Xl klka unfolding entry_def by simp
        next
          case notlt: False
          show ?thesis
          proof (cases "om = h")
            case omh: True
            have ka1n: "ka + 1 < n"
            proof -
              have "h < length X" using omh bl by simp
              hence "(ka + 1) * L < n * L" unfolding h_def lenX by simp
              thus ?thesis using L0
                by (metis gr_implies_not0 less_mult_imp_div_less nonzero_mult_div_cancel_right)
            qed
            have Xh: "X ! h = (entry M 0 j0 + (ka + 1) * d0, entry M 1 j0)"
              unfolding h_def using ncopy[OF ka1n L0] by simp
            have stp: "entry M 0 j0 + (ka + 1) * d0 \<le> entry M 0 (j0 + qa) + ka * d0"
              using st Xa Xh omh by simp
            have dag: "entry M 0 j0 + d0 \<le> entry M 0 (j0 + qa)" using stp by simp
            have lj0: "j0 \<le> l" using aj0 al by simp
            have lX: "l < length X" using bl lo by simp
            obtain kl ql where kl: "kl < n" "ql < L" "l = j0 + (kl * L + ql)"
                and Xl: "X ! l = (entry M 0 (j0 + ql) + kl * d0, entry M 1 (j0 + ql))"
              using idxE[OF lj0 lX] by blast
            have klka: "kl = ka \<and> qa < ql"
            proof -
              have lo1: "kl * L + ql < L + ka * L" using kl(3) omh lo unfolding hN by arith
              have lo2: "ka * L + qa < kl * L + ql" using ka(3) kl(3) al by arith
              have "kl \<le> ka"
              proof (rule ccontr)
                assume "\<not> kl \<le> ka"
                hence "Suc ka \<le> kl" by simp
                hence "L + ka * L \<le> kl * L" using mult_le_mono1[of "Suc ka" kl L] by simp
                thus False using lo1 by arith
              qed
              moreover have "ka \<le> kl"
              proof (rule ccontr)
                assume "\<not> ka \<le> kl"
                hence "Suc kl \<le> ka" by simp
                hence "L + kl * L \<le> ka * L" using mult_le_mono1[of "Suc kl" ka L] by simp
                thus False using lo2 kl(2) by arith
              qed
              ultimately show ?thesis using lo2 by simp
            qed
            have domtail: "\<forall>q. qa < q \<and> q < L \<longrightarrow>
                entry M 0 (j0 + qa) < entry M 0 (j0 + q)"
            proof (intro allI impI)
              fix q assume qq: "qa < q \<and> q < L"
              have idx: "a + (q - qa) = j0 + (ka * L + q)" using ka(3) qq by arith
              have win: "a < a + (q - qa) \<and> a + (q - qa) < om"
                using qq ka(3) omh unfolding hN by arith
              have "fst (X ! a) < fst (X ! (a + (q - qa)))" using dom win by blast
              moreover have "X ! (a + (q - qa))
                  = (entry M 0 (j0 + q) + ka * d0, entry M 1 (j0 + q))"
                unfolding idx by (rule ncopy[OF ka(1)]) (use qq in simp)
              ultimately show "entry M 0 (j0 + qa) < entry M 0 (j0 + q)" using Xa by simp
            qed
            show ?thesis
            proof (cases "d0 = 0")
              case d00: True
              have stpu: "entry M 0 j0 \<le> entry M 0 (j0 + qa)" using dag d00 by simp
              have sqaL: "Suc qa < L" using klka kl(2) by arith
              have idxsa: "Suc a = j0 + (ka * L + Suc qa)" using ka(3) by simp
              have Xsa: "X ! Suc a = (entry M 0 (j0 + Suc qa) + ka * d0, entry M 1 (j0 + Suc qa))"
                unfolding idxsa by (rule ncopy[OF ka(1) sqaL])
              have htq: "entry M 1 (j0 + Suc qa) = entry M 1 (j0 + qa)"
                using ht Xsa Xa by simp
              have "entry M 1 (j0 + ql) \<le> entry M 1 (j0 + qa)"
                by (rule ginv_BTWRAPU3[OF ST j1d j1nz Fz i1d hp j0d d0d d00 _ stpu
                      domtail[unfolded L_def] htq])
                   (use ka(2) klka kl(2) L_def in simp_all)
              thus ?thesis using Xa Xl klka by simp
            next
              case d0pos': False
              have d0pos: "0 < d0" using d0pos' by simp
              have i1one: "i1 = 1"
                using idx1_le[of M j1] d0d d0pos i1d by (cases i1) auto
              have e0j: "entry M 0 j0 < entry M 0 j1" using hm0 j0j1 by simp
              have d0ex: "entry M 0 j0 + d0 = entry M 0 j1"
                unfolding d0d using i1one e0j by simp
              have omM: "j1 < length M" by (rule j1len)
              have dom': "\<forall>k. j0 + qa < k \<and> k < j1 \<longrightarrow>
                  fst (M ! (j0 + qa)) < fst (M ! k)"
              proof (intro allI impI)
                fix k assume kk: "j0 + qa < k \<and> k < j1"
                define qq where "qq = k - j0"
                have ke: "k = j0 + qq" unfolding qq_def using kk by arith
                have qr: "qa < qq \<and> qq < L" unfolding qq_def L_def using kk by arith
                have "entry M 0 (j0 + qa) < entry M 0 (j0 + qq)" using domtail qr by blast
                thus "fst (M ! (j0 + qa)) < fst (M ! k)" unfolding ke entry_def by simp
              qed
              have st': "fst (M ! j1) \<le> fst (M ! (j0 + qa))"
                using dag d0ex unfolding entry_def by simp
              have lrange: "j0 + qa < j0 + ql \<and> j0 + ql < j1"
                using klka kl(2) j0Lj1 by arith
              have sqaL: "Suc qa < L" using klka kl(2) by arith
              have idxsa: "Suc a = j0 + (ka * L + Suc qa)" using ka(3) by simp
              have Xsa: "X ! Suc a = (entry M 0 (j0 + Suc qa) + ka * d0, entry M 1 (j0 + Suc qa))"
                unfolding idxsa by (rule ncopy[OF ka(1) sqaL])
              have ht': "snd (M ! Suc (j0 + qa)) = snd (M ! (j0 + qa))"
              proof -
                have "entry M 1 (j0 + Suc qa) = entry M 1 (j0 + qa)" using ht Xsa Xa by simp
                thus ?thesis unfolding entry_def by simp
              qed
              have "snd (M ! (j0 + ql)) \<le> snd (M ! (j0 + qa))"
                using BF3[unfolded btfullok3_def, rule_format, of j1 "j0 + qa" "j0 + ql"]
                  omM dom' st' ht' lrange by blast
              thus ?thesis using Xa Xl klka unfolding entry_def by simp
            qed
          next
            case omgt': False
            have omgt: "h < om" using notlt omgt' by simp
            have hwin: "a < h \<and> h < om" using ah omgt by simp
            have ka1n: "ka + 1 < n"
            proof -
              have "h < length X" using omgt bl by simp
              hence "(ka + 1) * L < n * L" unfolding h_def lenX by simp
              thus ?thesis using L0
                by (metis gr_implies_not0 less_mult_imp_div_less nonzero_mult_div_cancel_right)
            qed
            have Xh: "X ! h = (entry M 0 j0 + (ka + 1) * d0, entry M 1 j0)"
              unfolding h_def using ncopy[OF ka1n L0] by simp
            have hdom: "fst (X ! a) < fst (X ! h)" using dom hwin by blast
            have star: "entry M 0 (j0 + qa) + ka * d0 < entry M 0 j0 + (ka + 1) * d0"
              using hdom Xa Xh by simp
            have starn: "entry M 0 (j0 + qa) + ka * d0 < entry M 0 j0 + d0 + ka * d0"
              using star by (simp add: algebra_simps)
            have kogt: "ka + 1 \<le> ko"
            proof -
              have "L + ka * L \<le> ko * L + qo" using ko(3) omgt unfolding hN by arith
              show ?thesis
              proof (rule ccontr)
                assume "\<not> ka + 1 \<le> ko"
                hence "ko \<le> ka" by simp
                hence "ko * L + qo < L + ka * L"
                  using ko(2) mult_le_mono1[of ko ka L] by arith
                thus False using \<open>L + ka * L \<le> ko * L + qo\<close> by arith
              qed
            qed
            have False
            proof (cases qo)
              case 0
              have "ka + 2 \<le> ko"
              proof (rule ccontr)
                assume "\<not> ka + 2 \<le> ko"
                hence "ko = ka + 1" using kogt by simp
                hence "om = h" using ko(3) 0 unfolding hN by simp
                thus False using omgt by simp
              qed
              hence "(ka + 2) * d0 \<le> ko * d0" by (rule mult_le_mono1)
              hence m2n: "d0 + d0 + ka * d0 \<le> ko * d0" by (simp add: algebra_simps)
              have "entry M 0 j0 + ko * d0 \<le> entry M 0 (j0 + qa) + ka * d0"
                using st Xa Xo 0 by simp
              thus False using m2n starn by arith
            next
              case (Suc q')
              have "j0 < j0 + qo \<and> j0 + qo \<le> j1" using Suc ko(2) j0Lj1 by arith
              hence e0qo: "entry M 0 j0 < entry M 0 (j0 + qo)" using hm0 by blast
              have "(ka + 1) * d0 \<le> ko * d0" using kogt by (rule mult_le_mono1)
              hence m1n: "d0 + ka * d0 \<le> ko * d0" by (simp add: algebra_simps)
              have "entry M 0 (j0 + qo) + ko * d0 \<le> entry M 0 (j0 + qa) + ka * d0"
                using st Xa Xo by simp
              thus False using m1n starn e0qo by arith
            qed
            thus ?thesis ..
          qed
        qed
      qed
    qed
  qed
qed



lemma btfullok_oper:
  assumes BF: "btfullok M" and BF3: "btfullok3 M"
    and ST: "M \<in> ST_PS" and n1: "1 \<le> n"
  shows "btfullok (oper M n) \<and> btfullok3 (oper M n)"
proof -
  define j1 where "j1 = Lng M - 1"
  have b: "blockok 0 M" by (rule blockok_ST_PS[OF ST])
  show ?thesis
  proof (cases "j1 = 0")
    case True thus ?thesis using BF BF3 unfolding oper_def Let_def j1_def by simp
  next
    case False
    show ?thesis
    proof (cases "entry M 0 j1 = 0 \<and> entry M 1 j1 = 0")
      case True
      have "oper M n = Pred M"
        unfolding oper_def Let_def j1_def[symmetric] using False True by auto
      thus ?thesis
        unfolding Pred_def using BF BF3 btfullok_butlast btfullok3_butlast by simp
    next
      case Fz: False
      define i1 where "i1 = idx1 M j1"
      show ?thesis
      proof (cases "hasParent M i1 j1")
        case False2: False
        have "oper M n = Pred M"
          unfolding oper_def Let_def j1_def[symmetric] i1_def[symmetric]
          using False Fz False2 by auto
        thus ?thesis
          unfolding Pred_def using BF BF3 btfullok_butlast btfullok3_butlast by simp
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
          using btfullok_oper_bad[OF BF BF3 b ST n1 j1_def False Fz i1_def hp j0_def d0_def opeq]
            btfullok3_oper_bad[OF BF BF3 b ST n1 j1_def False Fz i1_def hp j0_def d0_def opeq]
          by blast
      qed
    qed
  qed
qed

theorem btfullok_ST_PS: "M \<in> ST_PS \<Longrightarrow> btfullok M \<and> btfullok3 M"
proof (induction M rule: ST_PS.induct)
  case (diag v) show ?case using btfullok_diagSeq btfullok3_diagSeq by blast
next
  case (oper M n)
  show ?case
    by (rule btfullok_oper[OF _ _ oper.hyps(1) oper.hyps(2)]) (use oper.IH in blast)+
qed

text \<open>(BT-FULL) The host-wide tie-free window bound on a bad-branch host
  (memo 続46): ANY dominated window closed by a level drop at a column
  \<open>\<le> j1\<close> is bounded one above its anchor (closure+2: 63999, zero
  violations).  \<open>ginv_BTWIN\<close> is the in-block corollary.\<close>

lemma ginv_BTFULL:
  assumes "M \<in> ST_PS"
    and "j1 = Lng M - 1" and "j1 \<noteq> 0"
    and "\<not> (entry M 0 j1 = 0 \<and> entry M 1 j1 = 0)"
    and "i1 = idx1 M j1" and "hasParent M i1 j1"
    and "j0 = parent M i1 j1"
    and "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
    and "a < om" and "om \<le> j1"
    and "\<forall>k. a < k \<and> k < om \<longrightarrow> fst (M ! a) < fst (M ! k)"
    and "fst (M ! om) \<le> fst (M ! a)"
    and "a < l" and "l < om"
  shows "snd (M ! l) \<le> Suc (snd (M ! a))"
proof -
  have lenM: "length M = Suc j1" using assms(2,3) by (cases M) auto
  have omM: "om < length M" using assms(10) lenM by simp
  show ?thesis
    using btfullok_ST_PS[OF assms(1)]
      conjunct1[of "btfullok M" "btfullok3 M"]
    unfolding btfullok_def
    using omM assms(11) assms(12) assms(13) assms(14) by blast
qed

lemma ginv_BTFULL_T3:
  assumes "M \<in> ST_PS"
    and "j1 = Lng M - 1" and "j1 \<noteq> 0"
    and "\<not> (entry M 0 j1 = 0 \<and> entry M 1 j1 = 0)"
    and "i1 = idx1 M j1" and "hasParent M i1 j1"
    and "j0 = parent M i1 j1"
    and "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
    and "a < om" and "om \<le> j1"
    and "\<forall>k. a < k \<and> k < om \<longrightarrow> fst (M ! a) < fst (M ! k)"
    and "fst (M ! om) \<le> fst (M ! a)"
    and "snd (M ! Suc a) = snd (M ! a)"
    and "a < l" and "l < om"
  shows "snd (M ! l) \<le> snd (M ! a)"
proof -
  have lenM: "length M = Suc j1" using assms(2,3) by (cases M) auto
  have omM: "om < length M" using assms(10) lenM by simp
  show ?thesis
    using btfullok_ST_PS[OF assms(1)]
    unfolding btfullok3_def
    using omM assms(11) assms(12) assms(13) assms(14) assms(15) by blast
qed

lemma ginv_BTWIN:
  assumes "M \<in> ST_PS"
    and "j1 = Lng M - 1" and "j1 \<noteq> 0"
    and "\<not> (entry M 0 j1 = 0 \<and> entry M 1 j1 = 0)"
    and "i1 = idx1 M j1" and "hasParent M i1 j1"
    and "j0 = parent M i1 j1"
    and "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
    and "al < om" and "om \<le> j1 - j0"
    and "\<forall>q. al < q \<and> q < om \<longrightarrow> entry M 0 (j0 + al) < entry M 0 (j0 + q)"
    and "entry M 0 (j0 + om) \<le> entry M 0 (j0 + al)"
    and "al < q" and "q < om"
  shows "entry M 1 (j0 + q) \<le> Suc (entry M 1 (j0 + al))"
proof -
  have nR: "nextR M i1 j0 j1" unfolding assms(7) by (rule parent_nextR[OF assms(6)])
  have j0j1: "j0 < j1" using nR by (rule nextR_less)
  have a1: "j0 + al < j0 + om" using assms(9) by simp
  have a2: "j0 + om \<le> j1" using assms(10) j0j1 by arith
  have a3: "\<forall>k. j0 + al < k \<and> k < j0 + om \<longrightarrow> fst (M ! (j0 + al)) < fst (M ! k)"
  proof (intro allI impI)
    fix k assume kk: "j0 + al < k \<and> k < j0 + om"
    define qq where "qq = k - j0"
    have ke: "k = j0 + qq" unfolding qq_def using kk by arith
    have "al < qq \<and> qq < om" unfolding qq_def using kk by arith
    hence "entry M 0 (j0 + al) < entry M 0 (j0 + qq)" using assms(11) by blast
    thus "fst (M ! (j0 + al)) < fst (M ! k)" unfolding ke entry_def by simp
  qed
  have a4: "fst (M ! (j0 + om)) \<le> fst (M ! (j0 + al))"
    using assms(12) unfolding entry_def by simp
  have a5: "j0 + al < j0 + q" using assms(13) by simp
  have a6: "j0 + q < j0 + om" using assms(14) by simp
  have "snd (M ! (j0 + q)) \<le> Suc (snd (M ! (j0 + al)))"
    by (rule ginv_BTFULL[OF assms(1-8) a1 a2 a3 a4 a5 a6])
  thus ?thesis unfolding entry_def by simp
qed

lemma ginv_BTWIN_T3:
  assumes "M \<in> ST_PS"
    and "j1 = Lng M - 1" and "j1 \<noteq> 0"
    and "\<not> (entry M 0 j1 = 0 \<and> entry M 1 j1 = 0)"
    and "i1 = idx1 M j1" and "hasParent M i1 j1"
    and "j0 = parent M i1 j1"
    and "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
    and "al < om" and "om \<le> j1 - j0"
    and "\<forall>q. al < q \<and> q < om \<longrightarrow> entry M 0 (j0 + al) < entry M 0 (j0 + q)"
    and "entry M 0 (j0 + om) \<le> entry M 0 (j0 + al)"
    and "entry M 1 (j0 + Suc al) = entry M 1 (j0 + al)"
    and "al < q" and "q < om"
  shows "entry M 1 (j0 + q) \<le> entry M 1 (j0 + al)"
proof -
  have nR: "nextR M i1 j0 j1" unfolding assms(7) by (rule parent_nextR[OF assms(6)])
  have j0j1: "j0 < j1" using nR by (rule nextR_less)
  have a1: "j0 + al < j0 + om" using assms(9) by simp
  have a2: "j0 + om \<le> j1" using assms(10) j0j1 by arith
  have a3: "\<forall>k. j0 + al < k \<and> k < j0 + om \<longrightarrow> fst (M ! (j0 + al)) < fst (M ! k)"
  proof (intro allI impI)
    fix k assume kk: "j0 + al < k \<and> k < j0 + om"
    define qq where "qq = k - j0"
    have ke: "k = j0 + qq" unfolding qq_def using kk by arith
    have "al < qq \<and> qq < om" unfolding qq_def using kk by arith
    hence "entry M 0 (j0 + al) < entry M 0 (j0 + qq)" using assms(11) by blast
    thus "fst (M ! (j0 + al)) < fst (M ! k)" unfolding ke entry_def by simp
  qed
  have a4: "fst (M ! (j0 + om)) \<le> fst (M ! (j0 + al))"
    using assms(12) unfolding entry_def by simp
  have ht: "snd (M ! Suc (j0 + al)) = snd (M ! (j0 + al))"
  proof -
    have "j0 + Suc al = Suc (j0 + al)" by simp
    thus ?thesis using assms(13) unfolding entry_def by simp
  qed
  have a5: "j0 + al < j0 + q" using assms(14) by simp
  have a6: "j0 + q < j0 + om" using assms(15) by simp
  have "snd (M ! (j0 + q)) \<le> snd (M ! (j0 + al))"
    by (rule ginv_BTFULL_T3[OF assms(1-8) a1 a2 a3 a4 ht a5 a6])
  thus ?thesis unfolding entry_def by simp
qed

text \<open>(BT-WRAP-GEN) The \<open>\<tau>\<close>-generalised exact-copy wrap bound (memo 続46補2):
  with \<open>d0 = 0\<close> the tie partner may be ANY earlier block column (closure+2:
  49609 / T3 10179, zero violations; \<open>d0 > 0\<close> is false for both).\<close>

lemma ginv_BTWRAPG:
  assumes "M \<in> ST_PS"
    and "j1 = Lng M - 1" and "j1 \<noteq> 0"
    and "\<not> (entry M 0 j1 = 0 \<and> entry M 1 j1 = 0)"
    and "i1 = idx1 M j1" and "hasParent M i1 j1"
    and "j0 = parent M i1 j1"
    and "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
    and "d0 = 0"
    and "ta \<le> qa" and "qa < j1 - j0"
    and "entry M 1 (j0 + qa) = entry M 1 (j0 + ta)"
    and "\<forall>q. qa < q \<and> q < j1 - j0 \<longrightarrow> entry M 0 (j0 + qa) < entry M 0 (j0 + q)"
    and "qa < q" and "q < j1 - j0"
  shows "entry M 1 (j0 + q) \<le> Suc (entry M 1 (j0 + qa))"
proof -
  have nR: "nextR M i1 j0 j1" unfolding assms(7) by (rule parent_nextR[OF assms(6)])
  have j0j1: "j0 < j1" using nR by (rule nextR_less)
  have hm0: "\<forall>k. j0 < k \<and> k \<le> j1 \<longrightarrow> entry M 0 j0 < entry M 0 k"
    by (rule block_head_min[OF assms(6) assms(7)])
  have e0c: "entry M 0 j0 \<le> entry M 0 (j0 + qa)"
  proof (cases qa)
    case 0 thus ?thesis by simp
  next
    case (Suc q')
    have "j0 < j0 + qa \<and> j0 + qa \<le> j1" using Suc assms(11) j0j1 by arith
    thus ?thesis using hm0 by fastforce
  qed
  show ?thesis
    by (rule ginv_BTWRAPU[OF assms(1-8) assms(9) assms(11) e0c assms(13)
          assms(14) assms(15)])
qed

lemma ginv_BTWRAPG_T3:
  assumes "M \<in> ST_PS"
    and "j1 = Lng M - 1" and "j1 \<noteq> 0"
    and "\<not> (entry M 0 j1 = 0 \<and> entry M 1 j1 = 0)"
    and "i1 = idx1 M j1" and "hasParent M i1 j1"
    and "j0 = parent M i1 j1"
    and "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
    and "d0 = 0"
    and "ta \<le> qa" and "qa < j1 - j0"
    and "entry M 1 (j0 + qa) = entry M 1 (j0 + ta)"
    and "\<forall>q. qa < q \<and> q < j1 - j0 \<longrightarrow> entry M 0 (j0 + qa) < entry M 0 (j0 + q)"
    and "entry M 1 (j0 + Suc qa) = entry M 1 (j0 + qa)"
    and "qa < q" and "q < j1 - j0"
  shows "entry M 1 (j0 + q) \<le> entry M 1 (j0 + qa)"
proof -
  have nR: "nextR M i1 j0 j1" unfolding assms(7) by (rule parent_nextR[OF assms(6)])
  have j0j1: "j0 < j1" using nR by (rule nextR_less)
  have hm0: "\<forall>k. j0 < k \<and> k \<le> j1 \<longrightarrow> entry M 0 j0 < entry M 0 k"
    by (rule block_head_min[OF assms(6) assms(7)])
  have e0c: "entry M 0 j0 \<le> entry M 0 (j0 + qa)"
  proof (cases qa)
    case 0 thus ?thesis by simp
  next
    case (Suc q')
    have "j0 < j0 + qa \<and> j0 + qa \<le> j1" using Suc assms(11) j0j1 by arith
    thus ?thesis using hm0 by fastforce
  qed
  show ?thesis
    by (rule ginv_BTWRAPU3[OF assms(1-8) assms(9) assms(11) e0c assms(13)
          assms(14) assms(15) assms(16)])
qed

lemma ginv_BTWRAP:
  assumes "M \<in> ST_PS"
    and "j1 = Lng M - 1" and "j1 \<noteq> 0"
    and "\<not> (entry M 0 j1 = 0 \<and> entry M 1 j1 = 0)"
    and "i1 = idx1 M j1" and "hasParent M i1 j1"
    and "j0 = parent M i1 j1"
    and "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
    and "d0 = 0"
    and "qa < j1 - j0"
    and "entry M 1 (j0 + qa) = entry M 1 j0"
    and "\<forall>q. qa < q \<and> q < j1 - j0 \<longrightarrow> entry M 0 (j0 + qa) < entry M 0 (j0 + q)"
    and "qa < q" and "q < j1 - j0"
  shows "entry M 1 (j0 + q) \<le> Suc (entry M 1 (j0 + qa))"
proof -
  have t0: "(0::nat) \<le> qa" by simp
  have tie0: "entry M 1 (j0 + qa) = entry M 1 (j0 + 0)" using assms(11) by simp
  show ?thesis
    by (rule ginv_BTWRAPG[OF assms(1-8) assms(9) t0 assms(10) tie0 assms(12)
          assms(13) assms(14)])
qed

text \<open>(BT-WRAP-T3, residual) The ascending-branch (\<open>0 < i1\<close>) instances of the
  \<open>\<tau> = 0\<close> head-tie wrap (closure+2: 6 instances, zero violations; the
  \<open>i1 = 0\<close> bulk — 20699 instances — is the \<open>BTWRAPU3\<close> route below).\<close>

lemma ginv_BTWRAP_T3_pos:
  assumes "M \<in> ST_PS"
    and "j1 = Lng M - 1" and "j1 \<noteq> 0"
    and "\<not> (entry M 0 j1 = 0 \<and> entry M 1 j1 = 0)"
    and "i1 = idx1 M j1" and "hasParent M i1 j1"
    and "j0 = parent M i1 j1"
    and "0 < i1"
    and "qa < j1 - j0"
    and "entry M 1 (j0 + qa) = entry M 1 j0"
    and "\<forall>q. qa < q \<and> q < j1 - j0 \<longrightarrow> entry M 0 (j0 + qa) < entry M 0 (j0 + q)"
    and "entry M 1 (j0 + Suc qa) = entry M 1 (j0 + qa)"
    and "qa < q" and "q < j1 - j0"
  shows "entry M 1 (j0 + q) \<le> entry M 1 (j0 + qa)"
  sorry

lemma ginv_BTWRAP_T3:
  assumes ST: "M \<in> ST_PS"
    and j1d: "j1 = Lng M - 1" and j1nz: "j1 \<noteq> 0"
    and Fz: "\<not> (entry M 0 j1 = 0 \<and> entry M 1 j1 = 0)"
    and i1d: "i1 = idx1 M j1" and hp: "hasParent M i1 j1"
    and j0d: "j0 = parent M i1 j1"
    and d0d: "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
    and qaL: "qa < j1 - j0"
    and tau: "entry M 1 (j0 + qa) = entry M 1 j0"
    and dom: "\<forall>q. qa < q \<and> q < j1 - j0 \<longrightarrow> entry M 0 (j0 + qa) < entry M 0 (j0 + q)"
    and tie: "entry M 1 (j0 + Suc qa) = entry M 1 (j0 + qa)"
    and ql: "qa < q" and qh: "q < j1 - j0"
  shows "entry M 1 (j0 + q) \<le> entry M 1 (j0 + qa)"
proof (cases "i1 = 0")
  case False
  hence "0 < i1" by simp
  thus ?thesis
    by (rule ginv_BTWRAP_T3_pos[OF ST j1d j1nz Fz i1d hp j0d _ qaL tau dom tie ql qh])
next
  case True
  have d00: "d0 = 0" using d0d True by simp
  have n0: "nextrel0 M j0 j1"
    using parent_nextR[OF hp] j0d unfolding nextR_def True by simp
  have jlt: "j0 < j1" and e0lt: "entry M 0 j0 < entry M 0 j1"
    using n0 unfolding nextrel0_def by blast+
  have gapc: "\<And>j. j0 < j \<Longrightarrow> j < j1 \<Longrightarrow> entry M 0 j1 \<le> entry M 0 j"
    using n0 unfolding nextrel0_def by blast
  have e0c: "entry M 0 j0 \<le> entry M 0 (j0 + qa)"
  proof (cases qa)
    case 0 thus ?thesis by simp
  next
    case (Suc m)
    have b1: "j0 < j0 + qa" unfolding Suc by simp
    have b2: "j0 + qa < j1" using qaL jlt by simp
    have "entry M 0 j1 \<le> entry M 0 (j0 + qa)" using gapc[OF b1 b2] .
    thus ?thesis using e0lt by simp
  qed
  show ?thesis
    by (rule ginv_BTWRAPU3[OF ST j1d j1nz Fz i1d hp j0d d0d d00 qaL e0c dom tie ql qh])
qed

text \<open>(BT1) The block-tail row-1 bound at a copy-boundary tie: with the tie,
  stop and dominance conditions of a cross-copy tie pair, the dominated block
  tail is bounded one above the anchor (closure+1: 6370 instances, zero
  violations; the head-tie variant drops the successor).\<close>

lemma ginv_BT1:
  assumes "M \<in> ST_PS"
    and "j1 = Lng M - 1" and "j1 \<noteq> 0"
    and "\<not> (entry M 0 j1 = 0 \<and> entry M 1 j1 = 0)"
    and "i1 = idx1 M j1" and "hasParent M i1 j1"
    and "j0 = parent M i1 j1"
    and "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
    and "qa < j1 - j0"
    and "entry M 1 (j0 + qa) = entry M 1 j0"
    and "entry M 0 j0 + d0 \<le> entry M 0 (j0 + qa)"
    and "\<forall>q. qa < q \<and> q < j1 - j0 \<longrightarrow> entry M 0 (j0 + qa) < entry M 0 (j0 + q)"
    and "qa < q" and "q < j1 - j0"
  shows "entry M 1 (j0 + q) \<le> Suc (entry M 1 (j0 + qa))"
proof (cases "d0 = 0")
  case True
  show ?thesis
    by (rule ginv_BTWRAP[OF assms(1-8) True assms(9) assms(10) assms(12)
          assms(13) assms(14)])
next
  case False
  have d0pos: "0 < d0" using False by simp
  have i1one: "i1 = 1"
    using idx1_le[of M j1] assms(8) d0pos assms(5) by (cases i1) auto
  have nR: "nextR M i1 j0 j1" unfolding assms(7) by (rule parent_nextR[OF assms(6)])
  have j0j1: "j0 < j1" using nR by (rule nextR_less)
  have hm0: "\<forall>k. j0 < k \<and> k \<le> j1 \<longrightarrow> entry M 0 j0 < entry M 0 k"
    by (rule block_head_min[OF assms(6) assms(7)])
  have e0j: "entry M 0 j0 < entry M 0 j1" using hm0 j0j1 by simp
  have d0ex: "entry M 0 j0 + d0 = entry M 0 j1"
    unfolding assms(8) using i1one e0j by simp
  have omj: "j0 + (j1 - j0) = j1" using j0j1 by simp
  have stop: "entry M 0 (j0 + (j1 - j0)) \<le> entry M 0 (j0 + qa)"
    unfolding omj using assms(11) d0ex by simp
  show ?thesis
    by (rule ginv_BTWIN[OF assms(1-8) assms(9) _ assms(12) stop assms(13) assms(14)])
       simp
qed

lemma t1ok_oper_bad:
  assumes T: "t1ok M" and T3: "t3ok M" and B: "blockok 0 M" and ST: "M \<in> ST_PS"
    and n1: "1 \<le> n"
    and j1d: "j1 = Lng M - 1" and j1nz: "j1 \<noteq> 0"
    and Fz: "\<not> (entry M 0 j1 = 0 \<and> entry M 1 j1 = 0)"
    and i1d: "i1 = idx1 M j1" and hp: "hasParent M i1 j1"
    and j0d: "j0 = parent M i1 j1"
    and d0d: "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
    and opeq: "X = take j0 M @ concat (map (\<lambda>k.
           map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j)) [j0..<j1]) [0..<n])"
  shows "t1ok X"
proof -
  have nR: "nextR M i1 j0 j1" unfolding j0d by (rule parent_nextR[OF hp])
  have j0j1: "j0 < j1" using nR by (rule nextR_less)
  have lenM: "length M = Suc j1" using j1d j1nz by (cases M) auto
  have j1len: "j1 < length M" using lenM by simp
  define L where "L = j1 - j0"
  have L0: "0 < L" unfolding L_def using j0j1 by simp
  have lenX: "length X = j0 + n * L"
    unfolding L_def by (rule oper_bad_len[OF opeq j0j1 j1len])
  have npre: "\<And>i. i < j0 \<Longrightarrow> X ! i = M ! i"
    using oper_bad_nth_pre[OF opeq _ j1len j0j1] by blast
  have ncopy: "\<And>k q. k < n \<Longrightarrow> q < L \<Longrightarrow>
        X ! (j0 + (k * L + q)) = (entry M 0 (j0 + q) + k * d0, entry M 1 (j0 + q))"
    unfolding L_def using oper_bad_nth_copy[OF opeq j0j1 j1len] by blast
  have hm0: "\<forall>k. j0 < k \<and> k \<le> j1 \<longrightarrow> entry M 0 j0 < entry M 0 k"
    by (rule block_head_min[OF hp j0d])
  have pairM: "\<And>j. (entry M 0 j, entry M 1 j) = M ! j"
    unfolding entry_def by simp
  have j0Lj1: "j0 + L = j1" unfolding L_def using j0j1 by simp
  have Xv0: "\<And>i. i < j0 + L \<Longrightarrow> X ! i = M ! i"
  proof -
    fix i assume iL: "i < j0 + L"
    show "X ! i = M ! i"
    proof (cases "i < j0")
      case True thus ?thesis by (rule npre)
    next
      case False
      have qL: "i - j0 < L" using iL False by simp
      have c0: "X ! (j0 + (0 * L + (i - j0)))
          = (entry M 0 (j0 + (i - j0)) + 0 * d0, entry M 1 (j0 + (i - j0)))"
        by (rule ncopy) (use n1 qL in simp_all)
      have ii: "j0 + (i - j0) = i" using False by simp
      have "X ! i = (entry M 0 i, entry M 1 i)" using c0 ii by simp
      thus ?thesis using pairM by simp
    qed
  qed
  have idxE: "\<And>i. j0 \<le> i \<Longrightarrow> i < length X \<Longrightarrow>
       \<exists>k q. k < n \<and> q < L \<and> i = j0 + (k * L + q)
           \<and> X ! i = (entry M 0 (j0 + q) + k * d0, entry M 1 (j0 + q))"
  proof -
    fix i assume ji: "j0 \<le> i" and iX: "i < length X"
    define k where "k = (i - j0) div L"
    define q where "q = (i - j0) mod L"
    have kq: "i - j0 = k * L + q" unfolding k_def q_def by simp
    have qL: "q < L" unfolding q_def using L0 by simp
    have kn: "k < n"
    proof -
      have "i - j0 < n * L" using iX lenX ji by simp
      thus ?thesis unfolding k_def
        by (metis less_mult_imp_div_less mult.commute)
    qed
    have ii: "i = j0 + (k * L + q)" using kq ji by simp
    have "X ! (j0 + (k * L + q)) = (entry M 0 (j0 + q) + k * d0, entry M 1 (j0 + q))"
      by (rule ncopy[OF kn qL])
    thus "\<exists>k q. k < n \<and> q < L \<and> i = j0 + (k * L + q)
           \<and> X ! i = (entry M 0 (j0 + q) + k * d0, entry M 1 (j0 + q))"
      using kn qL ii by blast
  qed
  show ?thesis
    unfolding t1ok_def
  proof (intro allI impI)
    fix a b
    assume aX: "a < length X" and pos: "0 < fst (X ! a)"
      and bdef: "b = Suc a + length (mrun X a)" and bX: "b < length X"
      and sb: "snd (X ! b) = snd (X ! a)"
    have ab: "a < b" using bdef by linarith
    define K where "K = mrun X a"
    have lenK: "length K = b - Suc a" unfolding K_def using bdef by simp
    have Kel: "\<And>t. t < b - Suc a \<Longrightarrow> K ! t = X ! (Suc a + t) \<and> fst (X ! a) < fst (K ! t)"
    proof -
      fix t assume tb: "t < b - Suc a"
      have tK: "t < length (mrun X a)" using tb bdef by simp
      have tw: "K ! t = drop (Suc a) X ! t"
        using tK unfolding K_def mrun_def by (rule takeWhile_nth)
      have "drop (Suc a) X ! t = X ! (Suc a + t)"
        using aX by (intro nth_drop) simp
      hence e: "K ! t = X ! (Suc a + t)" using tw by simp
      have "K ! t \<in> set K" using tb lenK by simp
      hence "fst (X ! a) < fst (K ! t)"
        unfolding K_def mrun_def using set_takeWhileD by metis
      thus "K ! t = X ! (Suc a + t) \<and> fst (X ! a) < fst (K ! t)"
        using e by simp
    qed
    have stopb: "\<not> fst (X ! a) < fst (X ! b)"
    proof -
      have ld: "length (takeWhile (\<lambda>r. fst (X ! a) < fst r) (drop (Suc a) X))
          < length (drop (Suc a) X)"
        using bdef bX unfolding mrun_def by simp
      have n0: "\<not> fst (X ! a)
          < fst (drop (Suc a) X ! length (takeWhile (\<lambda>r. fst (X ! a) < fst r) (drop (Suc a) X)))"
        using nth_length_takeWhile[OF ld] by simp
      have "drop (Suc a) X ! (b - Suc a) = X ! (Suc a + (b - Suc a))"
        using aX by (intro nth_drop) simp
      hence "drop (Suc a) X ! (b - Suc a) = X ! b" using ab by simp
      thus ?thesis using n0 bdef unfolding mrun_def by simp
    qed
    show "\<forall>x \<in> set (mrun X a). snd x \<le> Suc (snd (X ! a))"
    proof (cases "a < j0")
      case apre: True
      have bj0: "b \<le> j0"
      proof (rule ccontr)
        assume "\<not> b \<le> j0"
        hence j0b: "j0 < b" by simp
        have t: "j0 - Suc a < b - Suc a" using j0b apre by arith
        have e: "Suc a + (j0 - Suc a) = j0" using apre by arith
        have kel: "K ! (j0 - Suc a) = X ! (Suc a + (j0 - Suc a))
            \<and> fst (X ! a) < fst (K ! (j0 - Suc a))"
          by (rule Kel[OF t])
        hence j0run: "fst (X ! a) < fst (X ! j0)" unfolding e by metis
        have Xj0: "X ! j0 = M ! j0" using Xv0 L0 by simp
        have bj0': "j0 \<le> b" using j0b by simp
        obtain kb qb where kb: "kb < n" "qb < L" "b = j0 + (kb * L + qb)"
            and Xb: "X ! b = (entry M 0 (j0 + qb) + kb * d0, entry M 1 (j0 + qb))"
          using idxE[OF bj0' bX] by blast
        have e0qb: "entry M 0 j0 \<le> entry M 0 (j0 + qb)"
        proof (cases qb)
          case 0 thus ?thesis by simp
        next
          case (Suc q')
          have "j0 < j0 + qb \<and> j0 + qb \<le> j1" using Suc kb(2) j0Lj1 by simp
          thus ?thesis using hm0 by fastforce
        qed
        have "entry M 0 j0 \<le> fst (X ! b)" using Xb e0qb by simp
        moreover have "fst (X ! b) \<le> fst (X ! a)" using stopb by simp
        moreover have "fst (X ! a) < entry M 0 j0"
          using j0run Xj0 unfolding entry_def by simp
        ultimately show False by simp
      qed
      have XMall: "\<And>i. i \<le> b \<Longrightarrow> X ! i = M ! i"
      proof -
        fix i assume "i \<le> b"
        hence "i < j0 + L" using bj0 L0 by simp
        thus "X ! i = M ! i" by (rule Xv0)
      qed
      have bM: "b < length M" using bj0 j0j1 j1len by simp
      have aM: "a < length M" using apre j0j1 j1len by simp
      have Xa: "X ! a = M ! a" using XMall[of a] ab by simp
      have Xb': "X ! b = M ! b" using XMall[of b] by simp
      have KelM: "\<And>t. t < b - Suc a \<Longrightarrow> K ! t = M ! (Suc a + t) \<and> fst (M ! a) < fst (K ! t)"
      proof -
        fix t assume tb: "t < b - Suc a"
        have "K ! t = X ! (Suc a + t)" "fst (X ! a) < fst (K ! t)" using Kel[OF tb] by auto
        moreover have "X ! (Suc a + t) = M ! (Suc a + t)"
          using XMall[of "Suc a + t"] tb by (simp add: less_diff_conv add.commute)
        ultimately show "K ! t = M ! (Suc a + t) \<and> fst (M ! a) < fst (K ! t)"
          using Xa by simp
      qed
      have mrMa: "mrun M a = K"
      proof -
        have Keq: "K = take (b - Suc a) (drop (Suc a) M)"
        proof (rule nth_equalityI)
          show "length K = length (take (b - Suc a) (drop (Suc a) M))"
            using lenK bM by simp
        next
          fix t assume "t < length K"
          hence tb: "t < b - Suc a" using lenK by simp
          show "K ! t = take (b - Suc a) (drop (Suc a) M) ! t"
            using KelM[OF tb] tb bM by simp
        qed
        have dsplit: "drop (Suc a) M = K @ M ! b # drop (Suc b) M"
        proof -
          have "drop (Suc a) M = take (b - Suc a) (drop (Suc a) M)
              @ drop (b - Suc a) (drop (Suc a) M)"
            by (rule append_take_drop_id[symmetric])
          moreover have "drop (b - Suc a) (drop (Suc a) M) = drop b M"
            using ab by (simp add: drop_drop)
          moreover have "drop b M = M ! b # drop (Suc b) M"
            using bM by (rule Cons_nth_drop_Suc[symmetric])
          ultimately show ?thesis using Keq by metis
        qed
        have allK: "\<forall>x \<in> set K. fst (M ! a) < fst x"
        proof
          fix x assume "x \<in> set K"
          then obtain t where tt: "t < length K" "x = K ! t" by (metis in_set_conv_nth)
          have tb2: "t < b - Suc a" using tt(1) lenK by simp
          have "fst (M ! a) < fst (K ! t)" using KelM[OF tb2] by blast
          thus "fst (M ! a) < fst x" using tt(2) by simp
        qed
        have "takeWhile (\<lambda>r. fst (M ! a) < fst r) (drop (Suc a) M)
            = K @ takeWhile (\<lambda>r. fst (M ! a) < fst r) (M ! b # drop (Suc b) M)"
          unfolding dsplit by (rule takeWhile_append2) (use allK in blast)
        moreover have "takeWhile (\<lambda>r. fst (M ! a) < fst r) (M ! b # drop (Suc b) M) = []"
        proof -
          have "\<not> fst (M ! a) < fst (M ! b)" using stopb Xa Xb' by simp
          thus ?thesis by simp
        qed
        ultimately show ?thesis unfolding mrun_def by simp
      qed
      have bdefM: "b = Suc a + length (mrun M a)" using bdef mrMa K_def by simp
      have posM: "0 < fst (M ! a)" using pos Xa by simp
      have sbM: "snd (M ! b) = snd (M ! a)" using sb Xa Xb' by simp
      have "\<forall>x \<in> set (mrun M a). snd x \<le> Suc (snd (M ! a))"
        using T[unfolded t1ok_def, rule_format, of a b] aM posM bdefM bM sbM by blast
      thus ?thesis unfolding mrMa K_def[symmetric] using Xa by simp
    next
      case False
      hence aj0: "j0 \<le> a" by simp
      obtain ka qa where ka: "ka < n" "qa < L" "a = j0 + (ka * L + qa)"
          and Xa: "X ! a = (entry M 0 (j0 + qa) + ka * d0, entry M 1 (j0 + qa))"
        using idxE[OF aj0 aX] by blast
      have bj0: "j0 \<le> b" using aj0 ab by simp
      obtain kb qb where kb: "kb < n" "qb < L" "b = j0 + (kb * L + qb)"
          and Xb: "X ! b = (entry M 0 (j0 + qb) + kb * d0, entry M 1 (j0 + qb))"
        using idxE[OF bj0 bX] by blast
      have kakb: "ka \<le> kb"
      proof (rule ccontr)
        assume "\<not> ka \<le> kb"
        hence "Suc kb \<le> ka" by simp
        hence "Suc kb * L \<le> ka * L" by (rule mult_le_mono1)
        hence "L + kb * L \<le> ka * L" by simp
        hence "kb * L + qb < ka * L + qa" using kb(2) by arith
        thus False using ka(3) kb(3) ab by arith
      qed
      show ?thesis
      proof (cases "kb = ka")
        case kbka: True
        have qaqb: "qa < qb" using ka(3) kb(3) kbka ab by arith
        define am where "am = j0 + qa"
        define bm where "bm = j0 + qb"
        have amM: "am < length M" unfolding am_def using ka(2) j0Lj1 j1len by arith
        have bmM: "bm < length M" unfolding bm_def using kb(2) j0Lj1 j1len by arith
        have lrun: "b - Suc a = qb - Suc qa" using ka(3) kb(3) kbka by arith
        have e0stop: "entry M 0 bm \<le> entry M 0 am"
        proof -
          have "fst (X ! b) \<le> fst (X ! a)" using stopb by simp
          thus ?thesis using Xa Xb kbka unfolding am_def bm_def by simp
        qed
        have qa1: "0 < qa"
        proof (rule ccontr)
          assume "\<not> 0 < qa"
          hence qa0: "qa = 0" by simp
          have "j0 < j0 + qb \<and> j0 + qb \<le> j1" using qaqb qa0 kb(2) j0Lj1 by arith
          hence "entry M 0 j0 < entry M 0 (j0 + qb)" using hm0 by blast
          thus False using e0stop qa0 unfolding am_def bm_def by simp
        qed
        have Kel2: "\<And>t. t < b - Suc a \<Longrightarrow>
            K ! t = (entry M 0 (am + Suc t) + ka * d0, entry M 1 (am + Suc t))"
        proof -
          fix t assume tb: "t < b - Suc a"
          have idx: "Suc a + t = j0 + (ka * L + (qa + Suc t))" using ka(3) by simp
          have qlt: "qa + Suc t < L"
          proof -
            have "qa + Suc t \<le> qb" using tb lrun by arith
            thus ?thesis using kb(2) by arith
          qed
          have "X ! (Suc a + t) = (entry M 0 (j0 + (qa + Suc t)) + ka * d0,
                entry M 1 (j0 + (qa + Suc t)))"
            unfolding idx by (rule ncopy[OF ka(1) qlt])
          thus "K ! t = (entry M 0 (am + Suc t) + ka * d0, entry M 1 (am + Suc t))"
            using Kel[OF tb] unfolding am_def by (simp add: add.assoc)
        qed
        have KelM: "\<And>t. t < bm - Suc am \<Longrightarrow> entry M 0 am < entry M 0 (am + Suc t)"
        proof -
          fix t assume tb: "t < bm - Suc am"
          have tb': "t < b - Suc a" using tb lrun unfolding am_def bm_def by arith
          have "fst (X ! a) < fst (K ! t)" using Kel[OF tb'] by blast
          thus "entry M 0 am < entry M 0 (am + Suc t)"
            using Xa Kel2[OF tb'] unfolding am_def by simp
        qed
        define KM where "KM = take (bm - Suc am) (drop (Suc am) M)"
        have lenKM: "length KM = bm - Suc am" unfolding KM_def using bmM by simp
        have KMel: "\<And>t. t < bm - Suc am \<Longrightarrow> KM ! t = M ! (Suc am + t)"
          unfolding KM_def using bmM by simp
        have mrM: "mrun M am = KM"
        proof -
          have allpre: "\<forall>x \<in> set KM. fst (M ! am) < fst x"
          proof
            fix x assume "x \<in> set KM"
            then obtain t where tt: "t < length KM" "x = KM ! t"
              by (metis in_set_conv_nth)
            have t1: "t < bm - Suc am" using tt(1) lenKM by simp
            have "x = M ! (Suc am + t)" using tt(2) KMel[OF t1] by simp
            thus "fst (M ! am) < fst x"
              using KelM[OF t1] unfolding entry_def by simp
          qed
          have dsplit: "drop (Suc am) M = KM @ M ! bm # drop (Suc bm) M"
          proof -
            have "drop (Suc am) M = KM @ drop (bm - Suc am) (drop (Suc am) M)"
              unfolding KM_def by (rule append_take_drop_id[symmetric])
            moreover have "drop (bm - Suc am) (drop (Suc am) M) = drop bm M"
              using qaqb unfolding am_def bm_def by (simp add: drop_drop add.commute)
            moreover have "drop bm M = M ! bm # drop (Suc bm) M"
              using bmM by (rule Cons_nth_drop_Suc[symmetric])
            ultimately show ?thesis by metis
          qed
          have "takeWhile (\<lambda>r. fst (M ! am) < fst r) (drop (Suc am) M)
              = KM @ takeWhile (\<lambda>r. fst (M ! am) < fst r) (M ! bm # drop (Suc bm) M)"
            unfolding dsplit by (rule takeWhile_append2) (use allpre in blast)
          moreover have "takeWhile (\<lambda>r. fst (M ! am) < fst r) (M ! bm # drop (Suc bm) M) = []"
            using e0stop unfolding entry_def by simp
          ultimately show ?thesis unfolding mrun_def by simp
        qed
        have lmr: "length (mrun M am) = bm - Suc am"
          unfolding mrM by (rule lenKM)
        have posM: "0 < fst (M ! am)"
        proof -
          have "j0 < j0 + qa \<and> j0 + qa \<le> j1" using qa1 ka(2) j0Lj1 by arith
          hence "entry M 0 j0 < entry M 0 am" unfolding am_def using hm0 by blast
          thus ?thesis unfolding entry_def by simp
        qed
        have sbM: "snd (M ! bm) = snd (M ! am)"
        proof -
          have "entry M 1 (j0 + qb) = entry M 1 (j0 + qa)" using sb Xa Xb by simp
          thus ?thesis unfolding am_def bm_def entry_def by simp
        qed
        have bdefM: "bm = Suc am + length (mrun M am)"
          using lmr qaqb unfolding am_def bm_def by arith
        have bnd: "\<forall>x \<in> set (mrun M am). snd x \<le> Suc (snd (M ! am))"
          using T[unfolded t1ok_def, rule_format, of am bm] amM posM bdefM bmM sbM by blast
        show ?thesis
        proof
          fix x assume "x \<in> set (mrun X a)"
          then obtain t where tt: "t < length K" "x = K ! t"
            unfolding K_def by (metis in_set_conv_nth)
          have tb: "t < b - Suc a" using tt(1) lenK by simp
          have sx: "snd x = entry M 1 (am + Suc t)" using Kel2[OF tb] tt(2) by simp
          have tbm: "t < bm - Suc am" using tb lrun unfolding am_def bm_def by arith
          have "M ! (Suc am + t) \<in> set (mrun M am)"
            unfolding mrM using KMel[OF tbm] tbm lenKM by (metis nth_mem)
          hence "snd (M ! (Suc am + t)) \<le> Suc (snd (M ! am))" using bnd by blast
          thus "snd x \<le> Suc (snd (X ! a))"
            using sx Xa unfolding am_def entry_def by simp
        qed
      next
        case kbka: False
        hence kgt: "ka < kb" using kakb by simp
        define h where "h = j0 + ((ka + 1) * L + 0)"
        have hb: "h \<le> b"
        proof -
          have "(ka + 1) * L \<le> kb * L" using kgt by (intro mult_le_mono1) simp
          thus ?thesis unfolding h_def using ka(3) kb(3) by simp
        qed
        have ka1n: "ka + 1 < n" using kgt kb(1) by simp
        have Xh: "X ! h = (entry M 0 j0 + (ka + 1) * d0, entry M 1 j0)"
          unfolding h_def using ncopy[OF ka1n L0] by simp
        have beq: "b = h"
        proof (rule ccontr)
          assume "b \<noteq> h"
          hence hltb: "h < b" using hb by simp
          have ah: "a < h" unfolding h_def using ka(3) ka(2) by simp
          have t: "h - Suc a < b - Suc a" using hltb ah by arith
          have e: "Suc a + (h - Suc a) = h" using ah by arith
          have kel: "K ! (h - Suc a) = X ! (Suc a + (h - Suc a))
              \<and> fst (X ! a) < fst (K ! (h - Suc a))"
            by (rule Kel[OF t])
          hence hrun: "fst (X ! a) < fst (X ! h)" unfolding e by metis
          have star: "entry M 0 (j0 + qa) + ka * d0 < entry M 0 j0 + (ka + 1) * d0"
            using hrun Xa Xh by simp
          have dstar: "fst (X ! b) \<le> fst (X ! a)" using stopb by simp
          show False
          proof (cases qb)
            case 0
            have "entry M 0 j0 + kb * d0 \<le> entry M 0 (j0 + qa) + ka * d0"
              using dstar Xa Xb 0 by simp
            moreover have "(ka + 1) * d0 \<le> kb * d0" using kgt by (intro mult_le_mono1) simp
            ultimately show False using star by arith
          next
            case (Suc q')
            have "j0 < j0 + qb \<and> j0 + qb \<le> j1" using Suc kb(2) j0Lj1 by arith
            hence e0qb: "entry M 0 j0 < entry M 0 (j0 + qb)" using hm0 by blast
            have "entry M 0 (j0 + qb) + kb * d0 \<le> entry M 0 (j0 + qa) + ka * d0"
              using dstar Xa Xb by simp
            moreover have "(ka + 1) * d0 \<le> kb * d0" using kgt by (intro mult_le_mono1) simp
            ultimately show False using star e0qb by arith
          qed
        qed
        have tiep: "entry M 1 (j0 + qa) = entry M 1 j0"
          using sb Xa Xb[unfolded beq[symmetric]] beq Xh by simp
        have stopc: "entry M 0 j0 + d0 \<le> entry M 0 (j0 + qa)"
        proof -
          have "entry M 0 j0 + (ka + 1) * d0 \<le> entry M 0 (j0 + qa) + ka * d0"
            using stopb Xa Xh beq by simp
          thus ?thesis by simp
        qed
        have domc: "\<forall>q. qa < q \<and> q < j1 - j0 \<longrightarrow> entry M 0 (j0 + qa) < entry M 0 (j0 + q)"
        proof (intro allI impI)
          fix q assume qq: "qa < q \<and> q < j1 - j0"
          have qL: "q < L" using qq unfolding L_def by simp
          define t where "t = q - Suc qa"
          have bsa: "b - Suc a = L - Suc qa"
            unfolding beq h_def using ka(3) by simp
          have tb: "t < b - Suc a"
            unfolding t_def bsa using qq qL by arith
          have idx: "Suc a + t = j0 + (ka * L + q)"
            unfolding t_def using ka(3) qq by simp
          have "X ! (Suc a + t) = (entry M 0 (j0 + q) + ka * d0, entry M 1 (j0 + q))"
            unfolding idx by (rule ncopy[OF ka(1) qL])
          moreover have "fst (X ! a) < fst (X ! (Suc a + t))"
            using Kel[OF tb] by metis
          ultimately show "entry M 0 (j0 + qa) < entry M 0 (j0 + q)" using Xa by simp
        qed
        show ?thesis
        proof
          fix x assume "x \<in> set (mrun X a)"
          then obtain t where tt: "t < length K" "x = K ! t"
            unfolding K_def by (metis in_set_conv_nth)
          have tb: "t < b - Suc a" using tt(1) lenK by simp
          define q where "q = qa + Suc t"
          have bsa2: "b - Suc a = L - Suc qa"
            unfolding beq h_def using ka(3) by simp
          have qL: "q < L"
            unfolding q_def using tb bsa2 by arith
          have idx: "Suc a + t = j0 + (ka * L + q)" unfolding q_def using ka(3) by simp
          have "X ! (Suc a + t) = (entry M 0 (j0 + q) + ka * d0, entry M 1 (j0 + q))"
            unfolding idx by (rule ncopy[OF ka(1) qL])
          hence sx: "snd x = entry M 1 (j0 + q)" using Kel[OF tb] tt(2) by simp
          have "entry M 1 (j0 + q) \<le> Suc (entry M 1 (j0 + qa))"
            by (rule ginv_BT1[OF ST j1d j1nz Fz i1d hp j0d d0d _ tiep stopc domc])
               (use ka(2) qL q_def L_def in simp_all)
          thus "snd x \<le> Suc (snd (X ! a))" using sx Xa by simp
        qed
      qed
    qed
  qed
qed

lemma ginv_BT1_T3:
  assumes "M \<in> ST_PS"
    and "j1 = Lng M - 1" and "j1 \<noteq> 0"
    and "\<not> (entry M 0 j1 = 0 \<and> entry M 1 j1 = 0)"
    and "i1 = idx1 M j1" and "hasParent M i1 j1"
    and "j0 = parent M i1 j1"
    and "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
    and "qa < j1 - j0"
    and "entry M 1 (j0 + qa) = entry M 1 j0"
    and "entry M 0 j0 + d0 \<le> entry M 0 (j0 + qa)"
    and "\<forall>q. qa < q \<and> q < j1 - j0 \<longrightarrow> entry M 0 (j0 + qa) < entry M 0 (j0 + q)"
    and "entry M 1 (j0 + Suc qa) = entry M 1 (j0 + qa)"
    and "qa < q" and "q < j1 - j0"
  shows "entry M 1 (j0 + q) \<le> entry M 1 (j0 + qa)"
  by (rule ginv_BTWRAP_T3[OF assms(1-8) assms(9) assms(10) assms(12)
        assms(13) assms(14) assms(15)])

lemma t3ok_oper_bad:
  assumes T: "t1ok M" and T3: "t3ok M" and B: "blockok 0 M" and ST: "M \<in> ST_PS"
    and n1: "1 \<le> n"
    and j1d: "j1 = Lng M - 1" and j1nz: "j1 \<noteq> 0"
    and Fz: "\<not> (entry M 0 j1 = 0 \<and> entry M 1 j1 = 0)"
    and i1d: "i1 = idx1 M j1" and hp: "hasParent M i1 j1"
    and j0d: "j0 = parent M i1 j1"
    and d0d: "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
    and opeq: "X = take j0 M @ concat (map (\<lambda>k.
           map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j)) [j0..<j1]) [0..<n])"
  shows "t3ok X"
proof -
  have nR: "nextR M i1 j0 j1" unfolding j0d by (rule parent_nextR[OF hp])
  have j0j1: "j0 < j1" using nR by (rule nextR_less)
  have lenM: "length M = Suc j1" using j1d j1nz by (cases M) auto
  have j1len: "j1 < length M" using lenM by simp
  define L where "L = j1 - j0"
  have L0: "0 < L" unfolding L_def using j0j1 by simp
  have lenX: "length X = j0 + n * L"
    unfolding L_def by (rule oper_bad_len[OF opeq j0j1 j1len])
  have npre: "\<And>i. i < j0 \<Longrightarrow> X ! i = M ! i"
    using oper_bad_nth_pre[OF opeq _ j1len j0j1] by blast
  have ncopy: "\<And>k q. k < n \<Longrightarrow> q < L \<Longrightarrow>
        X ! (j0 + (k * L + q)) = (entry M 0 (j0 + q) + k * d0, entry M 1 (j0 + q))"
    unfolding L_def using oper_bad_nth_copy[OF opeq j0j1 j1len] by blast
  have hm0: "\<forall>k. j0 < k \<and> k \<le> j1 \<longrightarrow> entry M 0 j0 < entry M 0 k"
    by (rule block_head_min[OF hp j0d])
  have pairM: "\<And>j. (entry M 0 j, entry M 1 j) = M ! j"
    unfolding entry_def by simp
  have j0Lj1: "j0 + L = j1" unfolding L_def using j0j1 by simp
  have Xv0: "\<And>i. i < j0 + L \<Longrightarrow> X ! i = M ! i"
  proof -
    fix i assume iL: "i < j0 + L"
    show "X ! i = M ! i"
    proof (cases "i < j0")
      case True thus ?thesis by (rule npre)
    next
      case False
      have qL: "i - j0 < L" using iL False by simp
      have c0: "X ! (j0 + (0 * L + (i - j0)))
          = (entry M 0 (j0 + (i - j0)) + 0 * d0, entry M 1 (j0 + (i - j0)))"
        by (rule ncopy) (use n1 qL in simp_all)
      have ii: "j0 + (i - j0) = i" using False by simp
      have "X ! i = (entry M 0 i, entry M 1 i)" using c0 ii by simp
      thus ?thesis using pairM by simp
    qed
  qed
  have idxE: "\<And>i. j0 \<le> i \<Longrightarrow> i < length X \<Longrightarrow>
       \<exists>k q. k < n \<and> q < L \<and> i = j0 + (k * L + q)
           \<and> X ! i = (entry M 0 (j0 + q) + k * d0, entry M 1 (j0 + q))"
  proof -
    fix i assume ji: "j0 \<le> i" and iX: "i < length X"
    define k where "k = (i - j0) div L"
    define q where "q = (i - j0) mod L"
    have kq: "i - j0 = k * L + q" unfolding k_def q_def by simp
    have qL: "q < L" unfolding q_def using L0 by simp
    have kn: "k < n"
    proof -
      have "i - j0 < n * L" using iX lenX ji by simp
      thus ?thesis unfolding k_def
        by (metis less_mult_imp_div_less mult.commute)
    qed
    have ii: "i = j0 + (k * L + q)" using kq ji by simp
    have "X ! (j0 + (k * L + q)) = (entry M 0 (j0 + q) + k * d0, entry M 1 (j0 + q))"
      by (rule ncopy[OF kn qL])
    thus "\<exists>k q. k < n \<and> q < L \<and> i = j0 + (k * L + q)
           \<and> X ! i = (entry M 0 (j0 + q) + k * d0, entry M 1 (j0 + q))"
      using kn qL ii by blast
  qed
  show ?thesis
    unfolding t3ok_def
  proof (intro allI impI)
    fix a b
    assume aX: "a < length X" and pos: "0 < fst (X ! a)"
      and bdef: "b = Suc a + length (mrun X a)" and bX: "b < length X"
      and sb: "snd (X ! b) = snd (X ! a)"
      and ne: "mrun X a \<noteq> []"
      and hd1: "snd (hd (mrun X a)) = snd (X ! a)"
    have ab: "a < b" using bdef by linarith
    define K where "K = mrun X a"
    have lenK: "length K = b - Suc a" unfolding K_def using bdef by simp
    have Kel: "\<And>t. t < b - Suc a \<Longrightarrow> K ! t = X ! (Suc a + t) \<and> fst (X ! a) < fst (K ! t)"
    proof -
      fix t assume tb: "t < b - Suc a"
      have tK: "t < length (mrun X a)" using tb bdef by simp
      have tw: "K ! t = drop (Suc a) X ! t"
        using tK unfolding K_def mrun_def by (rule takeWhile_nth)
      have "drop (Suc a) X ! t = X ! (Suc a + t)"
        using aX by (intro nth_drop) simp
      hence e: "K ! t = X ! (Suc a + t)" using tw by simp
      have "K ! t \<in> set K" using tb lenK by simp
      hence "fst (X ! a) < fst (K ! t)"
        unfolding K_def mrun_def using set_takeWhileD by metis
      thus "K ! t = X ! (Suc a + t) \<and> fst (X ! a) < fst (K ! t)"
        using e by simp
    qed
    have stopb: "\<not> fst (X ! a) < fst (X ! b)"
    proof -
      have ld: "length (takeWhile (\<lambda>r. fst (X ! a) < fst r) (drop (Suc a) X))
          < length (drop (Suc a) X)"
        using bdef bX unfolding mrun_def by simp
      have n0: "\<not> fst (X ! a)
          < fst (drop (Suc a) X ! length (takeWhile (\<lambda>r. fst (X ! a) < fst r) (drop (Suc a) X)))"
        using nth_length_takeWhile[OF ld] by simp
      have "drop (Suc a) X ! (b - Suc a) = X ! (Suc a + (b - Suc a))"
        using aX by (intro nth_drop) simp
      hence "drop (Suc a) X ! (b - Suc a) = X ! b" using ab by simp
      thus ?thesis using n0 bdef unfolding mrun_def by simp
    qed
    have Kne: "K \<noteq> []" unfolding K_def by (rule ne)
    have hdK0: "hd K = K ! 0" using Kne by (simp add: hd_conv_nth)
    have K0pos: "0 < b - Suc a" using lenK Kne by (cases "b - Suc a") auto
    show "\<forall>x \<in> set (mrun X a). snd x \<le> snd (X ! a)"
    proof (cases "a < j0")
      case apre: True
      have bj0: "b \<le> j0"
      proof (rule ccontr)
        assume "\<not> b \<le> j0"
        hence j0b: "j0 < b" by simp
        have t: "j0 - Suc a < b - Suc a" using j0b apre by arith
        have e: "Suc a + (j0 - Suc a) = j0" using apre by arith
        have kel: "K ! (j0 - Suc a) = X ! (Suc a + (j0 - Suc a))
            \<and> fst (X ! a) < fst (K ! (j0 - Suc a))"
          by (rule Kel[OF t])
        hence j0run: "fst (X ! a) < fst (X ! j0)" unfolding e by metis
        have Xj0: "X ! j0 = M ! j0" using Xv0 L0 by simp
        have bj0': "j0 \<le> b" using j0b by simp
        obtain kb qb where kb: "kb < n" "qb < L" "b = j0 + (kb * L + qb)"
            and Xb: "X ! b = (entry M 0 (j0 + qb) + kb * d0, entry M 1 (j0 + qb))"
          using idxE[OF bj0' bX] by blast
        have e0qb: "entry M 0 j0 \<le> entry M 0 (j0 + qb)"
        proof (cases qb)
          case 0 thus ?thesis by simp
        next
          case (Suc q')
          have "j0 < j0 + qb \<and> j0 + qb \<le> j1" using Suc kb(2) j0Lj1 by simp
          thus ?thesis using hm0 by fastforce
        qed
        have "entry M 0 j0 \<le> fst (X ! b)" using Xb e0qb by simp
        moreover have "fst (X ! b) \<le> fst (X ! a)" using stopb by simp
        moreover have "fst (X ! a) < entry M 0 j0"
          using j0run Xj0 unfolding entry_def by simp
        ultimately show False by simp
      qed
      have XMall: "\<And>i. i \<le> b \<Longrightarrow> X ! i = M ! i"
      proof -
        fix i assume "i \<le> b"
        hence "i < j0 + L" using bj0 L0 by simp
        thus "X ! i = M ! i" by (rule Xv0)
      qed
      have bM: "b < length M" using bj0 j0j1 j1len by simp
      have aM: "a < length M" using apre j0j1 j1len by simp
      have Xa: "X ! a = M ! a" using XMall[of a] ab by simp
      have Xb': "X ! b = M ! b" using XMall[of b] by simp
      have KelM: "\<And>t. t < b - Suc a \<Longrightarrow> K ! t = M ! (Suc a + t) \<and> fst (M ! a) < fst (K ! t)"
      proof -
        fix t assume tb: "t < b - Suc a"
        have "K ! t = X ! (Suc a + t)" "fst (X ! a) < fst (K ! t)" using Kel[OF tb] by auto
        moreover have "X ! (Suc a + t) = M ! (Suc a + t)"
          using XMall[of "Suc a + t"] tb by (simp add: less_diff_conv add.commute)
        ultimately show "K ! t = M ! (Suc a + t) \<and> fst (M ! a) < fst (K ! t)"
          using Xa by simp
      qed
      have mrMa: "mrun M a = K"
      proof -
        have Keq: "K = take (b - Suc a) (drop (Suc a) M)"
        proof (rule nth_equalityI)
          show "length K = length (take (b - Suc a) (drop (Suc a) M))"
            using lenK bM by simp
        next
          fix t assume "t < length K"
          hence tb: "t < b - Suc a" using lenK by simp
          show "K ! t = take (b - Suc a) (drop (Suc a) M) ! t"
            using KelM[OF tb] tb bM by simp
        qed
        have dsplit: "drop (Suc a) M = K @ M ! b # drop (Suc b) M"
        proof -
          have "drop (Suc a) M = take (b - Suc a) (drop (Suc a) M)
              @ drop (b - Suc a) (drop (Suc a) M)"
            by (rule append_take_drop_id[symmetric])
          moreover have "drop (b - Suc a) (drop (Suc a) M) = drop b M"
            using ab by (simp add: drop_drop)
          moreover have "drop b M = M ! b # drop (Suc b) M"
            using bM by (rule Cons_nth_drop_Suc[symmetric])
          ultimately show ?thesis using Keq by metis
        qed
        have allK: "\<forall>x \<in> set K. fst (M ! a) < fst x"
        proof
          fix x assume "x \<in> set K"
          then obtain t where tt: "t < length K" "x = K ! t" by (metis in_set_conv_nth)
          have tb2: "t < b - Suc a" using tt(1) lenK by simp
          have "fst (M ! a) < fst (K ! t)" using KelM[OF tb2] by blast
          thus "fst (M ! a) < fst x" using tt(2) by simp
        qed
        have "takeWhile (\<lambda>r. fst (M ! a) < fst r) (drop (Suc a) M)
            = K @ takeWhile (\<lambda>r. fst (M ! a) < fst r) (M ! b # drop (Suc b) M)"
          unfolding dsplit by (rule takeWhile_append2) (use allK in blast)
        moreover have "takeWhile (\<lambda>r. fst (M ! a) < fst r) (M ! b # drop (Suc b) M) = []"
        proof -
          have "\<not> fst (M ! a) < fst (M ! b)" using stopb Xa Xb' by simp
          thus ?thesis by simp
        qed
        ultimately show ?thesis unfolding mrun_def by simp
      qed
      have bdefM: "b = Suc a + length (mrun M a)" using bdef mrMa K_def by simp
      have posM: "0 < fst (M ! a)" using pos Xa by simp
      have sbM: "snd (M ! b) = snd (M ! a)" using sb Xa Xb' by simp
      have neM: "mrun M a \<noteq> []" using Kne mrMa by simp
      have hdM: "snd (hd (mrun M a)) = snd (M ! a)"
        using hd1 Xa unfolding mrMa K_def by simp
      have "\<forall>x \<in> set (mrun M a). snd x \<le> snd (M ! a)"
        using T3[unfolded t3ok_def, rule_format, of a b]
          aM posM bdefM bM sbM neM hdM by blast
      thus ?thesis unfolding mrMa K_def[symmetric] using Xa by simp
    next
      case False
      hence aj0: "j0 \<le> a" by simp
      obtain ka qa where ka: "ka < n" "qa < L" "a = j0 + (ka * L + qa)"
          and Xa: "X ! a = (entry M 0 (j0 + qa) + ka * d0, entry M 1 (j0 + qa))"
        using idxE[OF aj0 aX] by blast
      have bj0: "j0 \<le> b" using aj0 ab by simp
      obtain kb qb where kb: "kb < n" "qb < L" "b = j0 + (kb * L + qb)"
          and Xb: "X ! b = (entry M 0 (j0 + qb) + kb * d0, entry M 1 (j0 + qb))"
        using idxE[OF bj0 bX] by blast
      have kakb: "ka \<le> kb"
      proof (rule ccontr)
        assume "\<not> ka \<le> kb"
        hence "Suc kb \<le> ka" by simp
        hence "Suc kb * L \<le> ka * L" by (rule mult_le_mono1)
        hence "L + kb * L \<le> ka * L" by simp
        hence "kb * L + qb < ka * L + qa" using kb(2) by arith
        thus False using ka(3) kb(3) ab by arith
      qed
      show ?thesis
      proof (cases "kb = ka")
        case kbka: True
        have qaqb: "qa < qb" using ka(3) kb(3) kbka ab by arith
        define am where "am = j0 + qa"
        define bm where "bm = j0 + qb"
        have amM: "am < length M" unfolding am_def using ka(2) j0Lj1 j1len by arith
        have bmM: "bm < length M" unfolding bm_def using kb(2) j0Lj1 j1len by arith
        have lrun: "b - Suc a = qb - Suc qa" using ka(3) kb(3) kbka by arith
        have e0stop: "entry M 0 bm \<le> entry M 0 am"
        proof -
          have "fst (X ! b) \<le> fst (X ! a)" using stopb by simp
          thus ?thesis using Xa Xb kbka unfolding am_def bm_def by simp
        qed
        have qa1: "0 < qa"
        proof (rule ccontr)
          assume "\<not> 0 < qa"
          hence qa0: "qa = 0" by simp
          have "j0 < j0 + qb \<and> j0 + qb \<le> j1" using qaqb qa0 kb(2) j0Lj1 by arith
          hence "entry M 0 j0 < entry M 0 (j0 + qb)" using hm0 by blast
          thus False using e0stop qa0 unfolding am_def bm_def by simp
        qed
        have Kel2: "\<And>t. t < b - Suc a \<Longrightarrow>
            K ! t = (entry M 0 (am + Suc t) + ka * d0, entry M 1 (am + Suc t))"
        proof -
          fix t assume tb: "t < b - Suc a"
          have idx: "Suc a + t = j0 + (ka * L + (qa + Suc t))" using ka(3) by simp
          have qlt: "qa + Suc t < L"
          proof -
            have "qa + Suc t \<le> qb" using tb lrun by arith
            thus ?thesis using kb(2) by arith
          qed
          have "X ! (Suc a + t) = (entry M 0 (j0 + (qa + Suc t)) + ka * d0,
                entry M 1 (j0 + (qa + Suc t)))"
            unfolding idx by (rule ncopy[OF ka(1) qlt])
          thus "K ! t = (entry M 0 (am + Suc t) + ka * d0, entry M 1 (am + Suc t))"
            using Kel[OF tb] unfolding am_def by (simp add: add.assoc)
        qed
        have KelM: "\<And>t. t < bm - Suc am \<Longrightarrow> entry M 0 am < entry M 0 (am + Suc t)"
        proof -
          fix t assume tb: "t < bm - Suc am"
          have tb': "t < b - Suc a" using tb lrun unfolding am_def bm_def by arith
          have "fst (X ! a) < fst (K ! t)" using Kel[OF tb'] by blast
          thus "entry M 0 am < entry M 0 (am + Suc t)"
            using Xa Kel2[OF tb'] unfolding am_def by simp
        qed
        define KM where "KM = take (bm - Suc am) (drop (Suc am) M)"
        have lenKM: "length KM = bm - Suc am" unfolding KM_def using bmM by simp
        have KMel: "\<And>t. t < bm - Suc am \<Longrightarrow> KM ! t = M ! (Suc am + t)"
          unfolding KM_def using bmM by simp
        have mrM: "mrun M am = KM"
        proof -
          have allpre: "\<forall>x \<in> set KM. fst (M ! am) < fst x"
          proof
            fix x assume "x \<in> set KM"
            then obtain t where tt: "t < length KM" "x = KM ! t"
              by (metis in_set_conv_nth)
            have t1: "t < bm - Suc am" using tt(1) lenKM by simp
            have "x = M ! (Suc am + t)" using tt(2) KMel[OF t1] by simp
            thus "fst (M ! am) < fst x"
              using KelM[OF t1] unfolding entry_def by simp
          qed
          have dsplit: "drop (Suc am) M = KM @ M ! bm # drop (Suc bm) M"
          proof -
            have "drop (Suc am) M = KM @ drop (bm - Suc am) (drop (Suc am) M)"
              unfolding KM_def by (rule append_take_drop_id[symmetric])
            moreover have "drop (bm - Suc am) (drop (Suc am) M) = drop bm M"
              using qaqb unfolding am_def bm_def by (simp add: drop_drop add.commute)
            moreover have "drop bm M = M ! bm # drop (Suc bm) M"
              using bmM by (rule Cons_nth_drop_Suc[symmetric])
            ultimately show ?thesis by metis
          qed
          have "takeWhile (\<lambda>r. fst (M ! am) < fst r) (drop (Suc am) M)
              = KM @ takeWhile (\<lambda>r. fst (M ! am) < fst r) (M ! bm # drop (Suc bm) M)"
            unfolding dsplit by (rule takeWhile_append2) (use allpre in blast)
          moreover have "takeWhile (\<lambda>r. fst (M ! am) < fst r) (M ! bm # drop (Suc bm) M) = []"
            using e0stop unfolding entry_def by simp
          ultimately show ?thesis unfolding mrun_def by simp
        qed
        have lmr: "length (mrun M am) = bm - Suc am"
          unfolding mrM by (rule lenKM)
        have posM: "0 < fst (M ! am)"
        proof -
          have "j0 < j0 + qa \<and> j0 + qa \<le> j1" using qa1 ka(2) j0Lj1 by arith
          hence "entry M 0 j0 < entry M 0 am" unfolding am_def using hm0 by blast
          thus ?thesis unfolding entry_def by simp
        qed
        have sbM: "snd (M ! bm) = snd (M ! am)"
        proof -
          have "entry M 1 (j0 + qb) = entry M 1 (j0 + qa)" using sb Xa Xb by simp
          thus ?thesis unfolding am_def bm_def entry_def by simp
        qed
        have bdefM: "bm = Suc am + length (mrun M am)"
          using lmr qaqb unfolding am_def bm_def by arith
        have neM2: "mrun M am \<noteq> []" using lmr lrun Kne lenK
          unfolding am_def bm_def by (cases "qb - Suc qa") auto
        have hdM2: "snd (hd (mrun M am)) = snd (M ! am)"
        proof -
          have bmpos: "0 < bm - Suc am"
            using K0pos lrun unfolding am_def bm_def by arith
          have h0: "hd (mrun M am) = M ! (Suc am)"
          proof -
            have "hd (mrun M am) = mrun M am ! 0" using neM2 by (simp add: hd_conv_nth)
            also have "\<dots> = KM ! 0" unfolding mrM ..
            also have "\<dots> = M ! (Suc am + 0)" using KMel[OF bmpos] by simp
            finally show ?thesis by simp
          qed
          have "snd (K ! 0) = entry M 1 (am + Suc 0)" using Kel2[OF K0pos] by simp
          hence "entry M 1 (Suc am) = snd (X ! a)" using hd1 hdK0 unfolding K_def by simp
          thus ?thesis unfolding h0 using Xa unfolding am_def entry_def by simp
        qed
        have bnd: "\<forall>x \<in> set (mrun M am). snd x \<le> snd (M ! am)"
          using T3[unfolded t3ok_def, rule_format, of am bm]
            amM posM bdefM bmM sbM neM2 hdM2 by blast
        show ?thesis
        proof
          fix x assume "x \<in> set (mrun X a)"
          then obtain t where tt: "t < length K" "x = K ! t"
            unfolding K_def by (metis in_set_conv_nth)
          have tb: "t < b - Suc a" using tt(1) lenK by simp
          have sx: "snd x = entry M 1 (am + Suc t)" using Kel2[OF tb] tt(2) by simp
          have tbm: "t < bm - Suc am" using tb lrun unfolding am_def bm_def by arith
          have "M ! (Suc am + t) \<in> set (mrun M am)"
            unfolding mrM using KMel[OF tbm] tbm lenKM by (metis nth_mem)
          hence "snd (M ! (Suc am + t)) \<le> snd (M ! am)" using bnd by blast
          thus "snd x \<le> snd (X ! a)"
            using sx Xa unfolding am_def entry_def by simp
        qed
      next
        case kbka: False
        hence kgt: "ka < kb" using kakb by simp
        define h where "h = j0 + ((ka + 1) * L + 0)"
        have hb: "h \<le> b"
        proof -
          have "(ka + 1) * L \<le> kb * L" using kgt by (intro mult_le_mono1) simp
          thus ?thesis unfolding h_def using ka(3) kb(3) by simp
        qed
        have ka1n: "ka + 1 < n" using kgt kb(1) by simp
        have Xh: "X ! h = (entry M 0 j0 + (ka + 1) * d0, entry M 1 j0)"
          unfolding h_def using ncopy[OF ka1n L0] by simp
        have beq: "b = h"
        proof (rule ccontr)
          assume "b \<noteq> h"
          hence hltb: "h < b" using hb by simp
          have ah: "a < h" unfolding h_def using ka(3) ka(2) by simp
          have t: "h - Suc a < b - Suc a" using hltb ah by arith
          have e: "Suc a + (h - Suc a) = h" using ah by arith
          have kel: "K ! (h - Suc a) = X ! (Suc a + (h - Suc a))
              \<and> fst (X ! a) < fst (K ! (h - Suc a))"
            by (rule Kel[OF t])
          hence hrun: "fst (X ! a) < fst (X ! h)" unfolding e by metis
          have star: "entry M 0 (j0 + qa) + ka * d0 < entry M 0 j0 + (ka + 1) * d0"
            using hrun Xa Xh by simp
          have dstar: "fst (X ! b) \<le> fst (X ! a)" using stopb by simp
          show False
          proof (cases qb)
            case 0
            have "entry M 0 j0 + kb * d0 \<le> entry M 0 (j0 + qa) + ka * d0"
              using dstar Xa Xb 0 by simp
            moreover have "(ka + 1) * d0 \<le> kb * d0" using kgt by (intro mult_le_mono1) simp
            ultimately show False using star by arith
          next
            case (Suc q')
            have "j0 < j0 + qb \<and> j0 + qb \<le> j1" using Suc kb(2) j0Lj1 by arith
            hence e0qb: "entry M 0 j0 < entry M 0 (j0 + qb)" using hm0 by blast
            have "entry M 0 (j0 + qb) + kb * d0 \<le> entry M 0 (j0 + qa) + ka * d0"
              using dstar Xa Xb by simp
            moreover have "(ka + 1) * d0 \<le> kb * d0" using kgt by (intro mult_le_mono1) simp
            ultimately show False using star e0qb by arith
          qed
        qed
        have tiep: "entry M 1 (j0 + qa) = entry M 1 j0"
          using sb Xa Xb[unfolded beq[symmetric]] beq Xh by simp
        have stopc: "entry M 0 j0 + d0 \<le> entry M 0 (j0 + qa)"
        proof -
          have "entry M 0 j0 + (ka + 1) * d0 \<le> entry M 0 (j0 + qa) + ka * d0"
            using stopb Xa Xh beq by simp
          thus ?thesis by simp
        qed
        have domc: "\<forall>q. qa < q \<and> q < j1 - j0 \<longrightarrow> entry M 0 (j0 + qa) < entry M 0 (j0 + q)"
        proof (intro allI impI)
          fix q assume qq: "qa < q \<and> q < j1 - j0"
          have qL: "q < L" using qq unfolding L_def by simp
          define t where "t = q - Suc qa"
          have bsa: "b - Suc a = L - Suc qa"
            unfolding beq h_def using ka(3) by simp
          have tb: "t < b - Suc a"
            unfolding t_def bsa using qq qL by arith
          have idx: "Suc a + t = j0 + (ka * L + q)"
            unfolding t_def using ka(3) qq by simp
          have "X ! (Suc a + t) = (entry M 0 (j0 + q) + ka * d0, entry M 1 (j0 + q))"
            unfolding idx by (rule ncopy[OF ka(1) qL])
          moreover have "fst (X ! a) < fst (X ! (Suc a + t))"
            using Kel[OF tb] by metis
          ultimately show "entry M 0 (j0 + qa) < entry M 0 (j0 + q)" using Xa by simp
        qed
        have headtie: "entry M 1 (j0 + Suc qa) = entry M 1 (j0 + qa)"
        proof -
          have sqaL: "Suc qa < L"
          proof -
            have "b - Suc a = L - Suc qa" unfolding beq h_def using ka(3) by simp
            thus ?thesis using K0pos by arith
          qed
          have idx0: "Suc a + 0 = j0 + (ka * L + Suc qa)" using ka(3) by simp
          have "X ! (Suc a + 0) = (entry M 0 (j0 + Suc qa) + ka * d0, entry M 1 (j0 + Suc qa))"
            unfolding idx0 by (rule ncopy[OF ka(1) sqaL])
          hence "snd (K ! 0) = entry M 1 (j0 + Suc qa)" using Kel[OF K0pos] by simp
          thus ?thesis using hd1 hdK0 Xa unfolding K_def by simp
        qed
        show ?thesis
        proof
          fix x assume "x \<in> set (mrun X a)"
          then obtain t where tt: "t < length K" "x = K ! t"
            unfolding K_def by (metis in_set_conv_nth)
          have tb: "t < b - Suc a" using tt(1) lenK by simp
          define q where "q = qa + Suc t"
          have bsa2: "b - Suc a = L - Suc qa"
            unfolding beq h_def using ka(3) by simp
          have qL: "q < L"
            unfolding q_def using tb bsa2 by arith
          have idx: "Suc a + t = j0 + (ka * L + q)" unfolding q_def using ka(3) by simp
          have "X ! (Suc a + t) = (entry M 0 (j0 + q) + ka * d0, entry M 1 (j0 + q))"
            unfolding idx by (rule ncopy[OF ka(1) qL])
          hence sx: "snd x = entry M 1 (j0 + q)" using Kel[OF tb] tt(2) by simp
          have "entry M 1 (j0 + q) \<le> entry M 1 (j0 + qa)"
            by (rule ginv_BT1_T3[OF ST j1d j1nz Fz i1d hp j0d d0d _ tiep stopc domc headtie])
               (use ka(2) qL q_def L_def in simp_all)
          thus "snd x \<le> snd (X ! a)" using sx Xa by simp
        qed
      qed
    qed
  qed
qed


lemma t13ok_oper:
  assumes T: "t1ok M" and T3: "t3ok M" and T14: "t14ok M"
    and ST: "M \<in> ST_PS" and n1: "1 \<le> n"
  shows "t1ok (oper M n) \<and> t3ok (oper M n) \<and> t14ok (oper M n)"
proof -
  define j1 where "j1 = Lng M - 1"
  have b: "blockok 0 M" by (rule blockok_ST_PS[OF ST])
  show ?thesis
  proof (cases "j1 = 0")
    case True thus ?thesis using T T3 T14 unfolding oper_def Let_def j1_def by simp
  next
    case False
    show ?thesis
    proof (cases "entry M 0 j1 = 0 \<and> entry M 1 j1 = 0")
      case True
      have "oper M n = Pred M"
        unfolding oper_def Let_def j1_def[symmetric] using False True by auto
      thus ?thesis
        unfolding Pred_def using T T3 T14 t1ok_butlast t3ok_butlast t14ok_butlast by simp
    next
      case Fz: False
      define i1 where "i1 = idx1 M j1"
      show ?thesis
      proof (cases "hasParent M i1 j1")
        case False2: False
        have "oper M n = Pred M"
          unfolding oper_def Let_def j1_def[symmetric] i1_def[symmetric]
          using False Fz False2 by auto
        thus ?thesis
          unfolding Pred_def using T T3 T14 t1ok_butlast t3ok_butlast t14ok_butlast by simp
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
          using t1ok_oper_bad[OF T T3 b ST n1 j1_def False Fz i1_def hp j0_def d0_def opeq]
            t3ok_oper_bad[OF T T3 b ST n1 j1_def False Fz i1_def hp j0_def d0_def opeq]
            t14ok_oper_bad[OF T T3 T14 b ST n1 j1_def False Fz i1_def hp j0_def d0_def opeq]
          by blast
      qed
    qed
  qed
qed

theorem t13ok_ST_PS: "M \<in> ST_PS \<Longrightarrow> t1ok M \<and> t3ok M \<and> t14ok M"
proof (induction M rule: ST_PS.induct)
  case (diag v) show ?case using t1ok_diagSeq t3ok_diagSeq t14ok_diagSeq by blast
next
  case (oper M n)
  show ?case
    by (rule t13ok_oper[OF _ _ _ oper.hyps(1) oper.hyps(2)]) (use oper.IH in blast)+
qed

lemma sibrel_trunc:
  assumes R: "sibrel K K1"
  shows "sibrel K (take s K1)"
proof (cases "length K1 \<le> s")
  case True
  thus ?thesis using R by simp
next
  case False
  hence sl: "s < length K1" by simp
  have dec: "K1 = take s K1 @ drop s K1" by simp
  have dne: "drop s K1 \<noteq> []" using sl by simp
  from R consider
      (eq) "K1 = K"
    | (pre) "\<exists>D. D \<noteq> [] \<and> K = K1 @ D"
    | (fd) p x x1 r r1 where "K = p @ x # r" "K1 = p @ x1 # r1"
        "fst x1 < fst x \<or> (fst x1 = fst x \<and> snd x1 < snd x)"
    unfolding sibrel_def by blast
  then show ?thesis
  proof cases
    case eq
    have "K = take s K1 @ drop s K1" using eq dec by simp
    thus ?thesis unfolding sibrel_def using dne by blast
  next
    case pre
    then obtain D where D: "D \<noteq> []" "K = K1 @ D" by blast
    have "K = take s K1 @ (drop s K1 @ D)" using D(2) dec by (metis append.assoc)
    moreover have "drop s K1 @ D \<noteq> []" using dne by simp
    ultimately show ?thesis unfolding sibrel_def by blast
  next
    case fd
    show ?thesis
    proof (cases "s \<le> length p")
      case True
      have tp: "take s K1 = take s p" unfolding fd(2) using True by simp
      have tpK: "take s K1 = take s K" unfolding tp fd(1) using True by simp
      have KK: "K = take s K1 @ drop s K" using tpK by (metis append_take_drop_id)
      have "drop s K \<noteq> []" unfolding fd(1) using True by simp
      thus ?thesis unfolding sibrel_def using KK by blast
    next
      case False
      hence sp: "length p < s" by simp
      have t1: "take s K1 = p @ x1 # take (s - length p - 1) r1"
      proof -
        have "take s K1 = take s p @ take (s - length p) (x1 # r1)"
          unfolding fd(2) by (simp add: take_append)
        moreover have "take s p = p" using sp by simp
        moreover have "take (s - length p) (x1 # r1)
                       = x1 # take (s - length p - 1) r1"
          using sp by (cases "s - length p") auto
        ultimately show ?thesis by simp
      qed
      show ?thesis unfolding sibrel_def using fd(1) t1 fd(3) by blast
    qed
  qed
qed

lemma sibm2_take:
  assumes S: "sibm2 M"
  shows "sibm2 (take m M)"
  unfolding sibm2_def
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
  from S[unfolded sibm2_def, rule_format, OF aM ap' bp' bM fb' sb']
  have core: "sibrel (mrun M a) (mrun M b)" .
  have mtb: "mrun (take m M) b = take (m - Suc b) (mrun M b)"
    by (rule mrun_take[OF bm])
  show "sibrel (mrun (take m M) a) (mrun (take m M) b)"
    unfolding full mtb by (rule sibrel_trunc[OF core])
qed


lemma sibm2_butlast: "sibm2 M \<Longrightarrow> sibm2 (butlast M)"
  using sibm2_take[of M "length M - 1"] by (simp add: butlast_conv_take)

text \<open>The pure clash algebra of \<open>sibrel\<close>: the relation never tolerates a
  proper extension of the first run, nor a first-difference ascent.  These
  two principles let facts \<open>sibrel K K2\<close> obtained from different hosts
  (the base sequence and the copy stack) be played against each other.\<close>

lemma sibrel_nopref:
  assumes R: "sibrel K K2" and E: "K2 = K @ E" and ne: "E \<noteq> []"
  shows False
proof -
  from R consider (eq) "K2 = K"
    | (pre) D where "D \<noteq> []" "K = K2 @ D"
    | (fd) p x x1 r r1 where "K = p @ x # r" "K2 = p @ x1 # r1"
        "fst x1 < fst x \<or> (fst x1 = fst x \<and> snd x1 < snd x)"
    unfolding sibrel_def by blast
  thus False
  proof cases
    case eq thus False using E ne by simp
  next
    case pre
    have "length K = length K2 + length D" using pre(2) by simp
    moreover have "length K2 = length K + length E" using E by simp
    ultimately show False using ne by simp
  next
    case fd
    have pK: "length p < length K" unfolding fd(1) by simp
    have "K ! length p = x" unfolding fd(1) by simp
    moreover have "K2 ! length p = x1" unfolding fd(2) by simp
    moreover have "K2 ! length p = K ! length p"
      unfolding E using pK by (simp add: nth_append)
    ultimately have "x1 = x" by simp
    thus False using fd(3) by auto
  qed
qed

lemma sibrel_ascent:
  assumes R: "sibrel K K2"
    and dK: "K = p @ x # r" and dK2: "K2 = p @ x1 # r1"
    and ne: "x1 \<noteq> x"
    and asc: "\<not> (fst x1 < fst x \<or> (fst x1 = fst x \<and> snd x1 < snd x))"
  shows False
proof -
  have nthK: "K ! length p = x" unfolding dK by simp
  have nthK2: "K2 ! length p = x1" unfolding dK2 by simp
  have pK: "length p < length K" unfolding dK by simp
  have pK2: "length p < length K2" unfolding dK2 by simp
  from R consider (eq) "K2 = K"
    | (pre) D where "D \<noteq> []" "K = K2 @ D"
    | (fd) p' x' x1' r' r1' where "K = p' @ x' # r'" "K2 = p' @ x1' # r1'"
        "fst x1' < fst x' \<or> (fst x1' = fst x' \<and> snd x1' < snd x')"
    unfolding sibrel_def by blast
  thus False
  proof cases
    case eq
    thus False using nthK nthK2 ne by simp
  next
    case pre
    have "K ! length p = K2 ! length p"
      unfolding pre(2) using pK2 by (simp add: nth_append)
    thus False using nthK nthK2 ne by simp
  next
    case fd
    have nthK': "K ! length p' = x'" unfolding fd(1) by simp
    have nthK2': "K2 ! length p' = x1'" unfolding fd(2) by simp
    have x1x': "x1' \<noteq> x'" using fd(3) by auto
    consider (less) "length p' < length p" | (same) "length p' = length p"
      | (more) "length p < length p'" by linarith
    thus False
    proof cases
      case same
      have "x' = x" using nthK nthK' same by simp
      moreover have "x1' = x1" using nthK2 nthK2' same by simp
      ultimately show False using fd(3) asc by simp
    next
      case less
      have "K ! length p' = p ! length p'"
        unfolding dK using less by (simp add: nth_append)
      moreover have "K2 ! length p' = p ! length p'"
        unfolding dK2 using less by (simp add: nth_append)
      ultimately have "x' = x1'" using nthK' nthK2' by simp
      thus False using x1x' by simp
    next
      case more
      have "K ! length p = p' ! length p"
        unfolding fd(1) using more by (simp add: nth_append)
      moreover have "K2 ! length p = p' ! length p"
        unfolding fd(2) using more by (simp add: nth_append)
      ultimately have "x = x1" using nthK nthK2 by simp
      thus False using ne by simp
    qed
  qed
qed

lemma sibrel_diverge:
  assumes R: "sibrel K K2"
    and dK: "K = p @ x # r" and dK2: "K2 = p @ x1 # r1"
    and ne: "x1 \<noteq> x"
  shows "fst x1 < fst x \<or> (fst x1 = fst x \<and> snd x1 < snd x)"
  using sibrel_ascent[OF R dK dK2 ne] by blast

text \<open>Pure seam ingredients: the block head is the strict row-0 minimum of
  the block (via the row-0 ancestor chain), and runs are unchanged by an
  append unless they were open.\<close>

lemma mrun_append:
  assumes aY: "a < length Y"
  shows "mrun (Y @ C) a =
    (if \<forall>x \<in> set (drop (Suc a) Y). fst (Y ! a) < fst x
     then drop (Suc a) Y @ takeWhile (\<lambda>r. fst (Y ! a) < fst r) C
     else mrun Y a)"
proof -
  have n: "(Y @ C) ! a = Y ! a" using aY by (simp add: nth_append)
  have d: "drop (Suc a) (Y @ C) = drop (Suc a) Y @ C" using aY by simp
  show ?thesis
  proof (cases "\<forall>x \<in> set (drop (Suc a) Y). fst (Y ! a) < fst x")
    case True
    have "takeWhile (\<lambda>r. fst (Y ! a) < fst r) (drop (Suc a) Y @ C)
          = drop (Suc a) Y @ takeWhile (\<lambda>r. fst (Y ! a) < fst r) C"
      using True by (simp add: takeWhile_append2)
    thus ?thesis unfolding mrun_def n d using True by simp
  next
    case False
    then obtain w where "w \<in> set (drop (Suc a) Y)" "\<not> fst (Y ! a) < fst w" by blast
    hence "takeWhile (\<lambda>r. fst (Y ! a) < fst r) (drop (Suc a) Y @ C)
          = takeWhile (\<lambda>r. fst (Y ! a) < fst r) (drop (Suc a) Y)"
      by (rule takeWhile_append1)
    thus ?thesis unfolding mrun_def n d if_not_P[OF False] .
  qed
qed

text \<open>Uniform row-0 shifts preserve the whole sibling-run structure: runs,
  ties, head-maximality and \<open>sibrel\<close> only ever compare row-0 values against
  each other and leave row 1 untouched.\<close>

definition shf :: "nat \<Rightarrow> pairseq \<Rightarrow> pairseq" where
  "shf s B = map (\<lambda>p. (fst p + s, snd p)) B"

lemma shf_len [simp]: "length (shf s B) = length B"
  unfolding shf_def by simp

lemma shf_nth: "q < length B \<Longrightarrow> shf s B ! q = (fst (B ! q) + s, snd (B ! q))"
  unfolding shf_def by simp

lemma shf_drop: "drop k (shf s B) = shf s (drop k B)"
  unfolding shf_def by (simp add: drop_map)

lemma shf_takeWhile:
  "takeWhile (\<lambda>r. c + s < fst r) (shf s B) = shf s (takeWhile (\<lambda>r. c < fst r) B)"
  unfolding shf_def by (subst takeWhile_map) (simp add: comp_def)

lemma shf_mrun:
  assumes q: "q < length B"
  shows "mrun (shf s B) q = shf s (mrun B q)"
proof -
  have f: "fst (shf s B ! q) = fst (B ! q) + s" using shf_nth[OF q] by simp
  show ?thesis
    unfolding mrun_def f shf_drop shf_takeWhile ..
qed

lemma shf_maxr1: "maxr1 (shf s B) = maxr1 B"
proof -
  have "snd ` set (shf s B) = snd ` set B"
    unfolding shf_def by force
  thus ?thesis unfolding maxr1_def by simp
qed

lemma shf_hd: "B \<noteq> [] \<Longrightarrow> hd (shf s B) = (fst (hd B) + s, snd (hd B))"
  unfolding shf_def by (simp add: hd_map)

lemma shf_sibrel:
  assumes R: "sibrel K K1"
  shows "sibrel (shf s K) (shf s K1)"
proof -
  from R consider (E) "K1 = K"
    | (P) D where "D \<noteq> []" "K = K1 @ D"
    | (FD) p x x1 r r1 where "K = p @ x # r" "K1 = p @ x1 # r1"
        "fst x1 < fst x \<or> (fst x1 = fst x \<and> snd x1 < snd x)"
    unfolding sibrel_def by blast
  thus ?thesis
  proof cases
    case E
    thus ?thesis unfolding sibrel_def by simp
  next
    case P
    have "shf s D \<noteq> []" using P(1) unfolding shf_def by simp
    moreover have "shf s K = shf s K1 @ shf s D"
      unfolding P(2) shf_def by simp
    ultimately show ?thesis unfolding sibrel_def by blast
  next
    case FD
    have d1: "shf s K = shf s p @ (fst x + s, snd x) # shf s r"
      unfolding FD(1) shf_def by simp
    have d2: "shf s K1 = shf s p @ (fst x1 + s, snd x1) # shf s r1"
      unfolding FD(2) shf_def by simp
    have lxs: "fst (fst x1 + s, snd x1) < fst (fst x + s, snd x)
               \<or> (fst (fst x1 + s, snd x1) = fst (fst x + s, snd x)
                  \<and> snd (fst x1 + s, snd x1) < snd (fst x + s, snd x))"
      using FD(3) by auto
    show ?thesis unfolding sibrel_def using d1 d2 lxs by blast
  qed
qed

lemma shf_0 [simp]: "shf 0 B = B"
  unfolding shf_def by simp

lemma mrun_suffix:
  assumes la: "length Y \<le> a" and aL: "a < length (Y @ C)"
  shows "mrun (Y @ C) a = mrun C (a - length Y)"
proof -
  have n: "(Y @ C) ! a = C ! (a - length Y)"
    using la by (simp add: nth_append)
  have d: "drop (Suc a) (Y @ C) = drop (Suc (a - length Y)) C"
    using la by (simp add: Suc_diff_le)
  show ?thesis unfolding mrun_def n d ..
qed

text \<open>(seam, open-run core) Extending an open tie-sibling run across the
  copy seam stays inside \<open>sibrel\<close>.  This is the alignment/periodicity core
  of the bad-branch preservation (memo 続29補4 I-open).\<close>

text \<open>(seam, E-refutation) An open tie-sibling run below the next copy's
  head level can never EQUAL its closing run when the tie head sits in the
  prefix: the run of \<open>b\<close> in the base sequence \<open>M\<close> ends with the last column
  \<open>M!j1\<close>, whose level/row-1 profile clashes with the copy continuation \<dash>
  \<open>sibrel_nopref\<close>/\<open>sibrel_ascent\<close> against the \<open>sibm2 M\<close> instance.\<close>

lemma seam_E_refute:
  assumes R: "sibm2 M" and B: "blockok 0 M" and ST: "M \<in> ST_PS"
    and j1d: "j1 = Lng M - 1" and j1nz: "j1 \<noteq> 0"
    and i1d: "i1 = idx1 M j1" and hp: "hasParent M i1 j1"
    and j0d: "j0 = parent M i1 j1"
    and d0d: "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
    and Yd: "Y = take j0 M @ concat (map (\<lambda>k.
           map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j)) [j0..<j1]) [0..<m])"
    and aY: "a < length Y" and pos: "0 < fst (Y ! a)"
    and bdef: "b = Suc a + length (mrun Y a)" and bY: "b < length Y"
    and fb: "fst (Y ! b) = fst (Y ! a)" and sb: "snd (Y ! b) = snd (Y ! a)"
    and ob: "\<forall>x \<in> set (drop (Suc b) Y). fst (Y ! b) < fst x"
    and high: "fst (Y ! b) < entry M 0 j0 + m * d0"
    and bj0: "b < j0"
  shows "mrun Y a \<noteq> drop (Suc b) Y"
proof
  assume EQ: "mrun Y a = drop (Suc b) Y"
  define cp where "cp = (\<lambda>k. map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j)) [j0..<j1])"
  have Yd': "Y = take j0 M @ concat (map cp [0..<m])"
    unfolding cp_def by (rule Yd)
  have nR: "nextR M i1 j0 j1" unfolding j0d by (rule parent_nextR[OF hp])
  have j0j1: "j0 < j1" using nR by (rule nextR_less)
  have lenM: "length M = Suc j1" using j1d j1nz by (cases M) auto
  have j1len: "j1 < length M" using lenM by simp
  define L where "L = j1 - j0"
  have L0: "0 < L" unfolding L_def using j0j1 by simp
  have lenY: "length Y = j0 + m * L"
    unfolding L_def by (rule oper_bad_len[OF Yd j0j1 j1len])
  have npre: "\<And>i. i < j0 \<Longrightarrow> Y ! i = M ! i"
    using oper_bad_nth_pre[OF Yd _ j1len j0j1] by blast
  have hm0: "\<forall>k. j0 < k \<and> k \<le> j1 \<longrightarrow> entry M 0 j0 < entry M 0 k"
    by (rule block_head_min[OF hp j0d])
  have pairM: "\<And>j. (entry M 0 j, entry M 1 j) = M ! j"
    unfolding entry_def by simp
  have ab: "a < b" using bdef by linarith
  have aj0: "a < j0" using ab bj0 by simp
  have Yb: "Y ! b = M ! b" by (rule npre[OF bj0])
  have Ya: "Y ! a = M ! a" by (rule npre[OF aj0])
  define blk where "blk = drop j0 (take j1 M)"
  have lenblk: "length blk = L" unfolding blk_def L_def using j1len by simp
  have blkne: "blk \<noteq> []" using lenblk L0 by auto
  have cpnth: "\<And>k q. q < L \<Longrightarrow> cp k ! q = (entry M 0 (j0+q) + k * d0, entry M 1 (j0+q))"
    unfolding cp_def L_def by simp
  have cp0: "cp 0 = blk"
  proof (rule nth_equalityI)
    show "length (cp 0) = length blk" unfolding cp_def lenblk L_def by simp
  next
    fix q assume "q < length (cp 0)"
    hence qL: "q < L" unfolding cp_def L_def by simp
    have "blk ! q = M ! (j0 + q)"
      unfolding blk_def L_def using qL j1len unfolding L_def by simp
    thus "cp 0 ! q = blk ! q" using cpnth[OF qL] pairM by simp
  qed
  have levlow: "fst (Y ! b) < entry M 0 j0"
  proof (cases m)
    case 0 thus ?thesis using high by simp
  next
    case (Suc km)
    have j0Y: "j0 < length Y" unfolding lenY Suc using L0 by simp
    have Yj0: "Y ! j0 = (entry M 0 j0, entry M 1 j0)"
      using oper_bad_nth_copy[OF Yd j0j1 j1len, of 0 0] L0 Suc
      unfolding L_def by simp
    have "drop (Suc b) Y ! (j0 - Suc b) \<in> set (drop (Suc b) Y)"
      using bj0 j0Y by (intro nth_mem) simp
    moreover have "drop (Suc b) Y ! (j0 - Suc b) = Y ! j0"
    proof -
      have "drop (Suc b) Y ! (j0 - Suc b) = Y ! (Suc b + (j0 - Suc b))"
        using bY by (intro nth_drop) simp
      thus ?thesis using bj0 by simp
    qed
    ultimately have "fst (Y ! b) < fst (Y ! j0)" using ob by auto
    thus ?thesis using Yj0 by simp
  qed
  have dropbM: "drop (Suc b) M = drop (Suc b) (take j0 M) @ blk @ [M ! j1]"
  proof -
    have "drop (Suc b) M = drop (Suc b) (take j0 M @ drop j0 M)" by simp
    also have "\<dots> = drop (Suc b) (take j0 M)
        @ drop (Suc b - length (take j0 M)) (drop j0 M)"
      by (rule drop_append)
    also have "\<dots> = drop (Suc b) (take j0 M) @ drop j0 M"
      using bj0 j1len j0j1 by simp
    also have "drop j0 M = blk @ [M ! j1]"
    proof -
      have Mdec: "M = take j1 M @ [M ! j1]"
      proof -
        have "drop j1 M = M ! j1 # drop (Suc j1) M"
          using j1len by (rule Cons_nth_drop_Suc[symmetric])
        moreover have "drop (Suc j1) M = []" using lenM by simp
        ultimately have "drop j1 M = [M ! j1]" by simp
        thus ?thesis by (metis append_take_drop_id)
      qed
      have "drop j0 M = drop j0 (take j1 M)
          @ drop (j0 - length (take j1 M)) [M ! j1]"
        by (subst Mdec) (rule drop_append)
      thus ?thesis unfolding blk_def using j0j1 j1len by simp
    qed
    finally show ?thesis .
  qed
  define P0 where "P0 = drop (Suc b) (take j0 M)"
  have dropbY: "drop (Suc b) Y = P0 @ concat (map cp [0..<m])"
    unfolding Yd' P0_def
    by (subst drop_append) (use bj0 j1len j0j1 in simp)
  have obM: "\<forall>x \<in> set (drop (Suc b) M). fst (M ! b) < fst x"
  proof
    fix x assume "x \<in> set (drop (Suc b) M)"
    then obtain t where t: "t < length M - Suc b" "x = drop (Suc b) M ! t"
      by (metis in_set_conv_nth length_drop)
    have xi: "x = M ! (Suc b + t)"
    proof -
      have "drop (Suc b) M ! t = M ! (Suc b + t)"
        by (intro nth_drop) (use bj0 j0j1 j1len in simp)
      thus ?thesis using t(2) by simp
    qed
    show "fst (M ! b) < fst x"
    proof (cases "Suc b + t < j0")
      case True
      have "M ! (Suc b + t) = Y ! (Suc b + t)" using npre[OF True] by simp
      moreover have "Y ! (Suc b + t) \<in> set (drop (Suc b) Y)"
      proof -
        have "Suc b + t < length Y" using True lenY by simp
        hence "drop (Suc b) Y ! t = Y ! (Suc b + t)"
          by (intro nth_drop) (use bY in simp_all)
        moreover have "t < length (drop (Suc b) Y)"
          using True lenY by simp
        ultimately show ?thesis by (metis nth_mem)
      qed
      ultimately show ?thesis using ob Yb xi by auto
    next
      case False
      hence ge: "j0 \<le> Suc b + t" by simp
      have le1: "Suc b + t \<le> j1" using t(1) lenM by simp
      show ?thesis
      proof (cases "Suc b + t = j0")
        case True
        thus ?thesis using xi levlow Yb pairM
          by (metis fst_conv)
      next
        case False
        hence "j0 < Suc b + t" using ge by simp
        hence "entry M 0 j0 < entry M 0 (Suc b + t)" using hm0 le1 by simp
        thus ?thesis using xi levlow Yb unfolding entry_def by simp
      qed
    qed
  qed
  have mrMb: "mrun M b = P0 @ blk @ [M ! j1]"
  proof -
    have "mrun M b = drop (Suc b) M"
      unfolding mrun_def using obM by (simp add: takeWhile_eq_all_conv)
    thus ?thesis unfolding dropbM P0_def .
  qed
  define K where "K = mrun Y a"
  have lenK: "length K = b - Suc a" unfolding K_def using bdef by simp
  have Kel: "\<And>t. t < b - Suc a \<Longrightarrow> K ! t = M ! (Suc a + t) \<and> fst (M ! a) < fst (K ! t)"
  proof -
    fix t assume tb: "t < b - Suc a"
    have tK: "t < length (mrun Y a)" using tb bdef by simp
    have tw: "K ! t = drop (Suc a) Y ! t"
      using tK unfolding K_def mrun_def by (rule takeWhile_nth)
    have "drop (Suc a) Y ! t = Y ! (Suc a + t)"
      using aY by (intro nth_drop) simp
    moreover have "Suc a + t < j0" using tb bj0 by simp
    ultimately have e: "K ! t = M ! (Suc a + t)" using tw npre by simp
    have "K ! t \<in> set K" using tb lenK by simp
    hence "fst (Y ! a) < fst (K ! t)"
      unfolding K_def mrun_def using set_takeWhileD by metis
    thus "K ! t = M ! (Suc a + t) \<and> fst (M ! a) < fst (K ! t)"
      using e Ya by simp
  qed
  have mrMa: "mrun M a = K"
  proof -
    have bM: "b < length M" using bj0 j0j1 j1len by simp
    have Keq: "K = take (b - Suc a) (drop (Suc a) M)"
    proof (rule nth_equalityI)
      show "length K = length (take (b - Suc a) (drop (Suc a) M))"
        using lenK bM by simp
    next
      fix t assume "t < length K"
      hence tb: "t < b - Suc a" using lenK by simp
      show "K ! t = take (b - Suc a) (drop (Suc a) M) ! t"
        using Kel[OF tb] tb bM by simp
    qed
    have dsplit: "drop (Suc a) M = K @ M ! b # drop (Suc b) M"
    proof -
      have "drop (Suc a) M = take (b - Suc a) (drop (Suc a) M)
          @ drop (b - Suc a) (drop (Suc a) M)"
        by (rule append_take_drop_id[symmetric])
      moreover have "drop (b - Suc a) (drop (Suc a) M) = drop b M"
        using ab by (simp add: drop_drop)
      moreover have "drop b M = M ! b # drop (Suc b) M"
        using bM by (rule Cons_nth_drop_Suc[symmetric])
      ultimately show ?thesis using Keq by metis
    qed
    have allK: "\<forall>x \<in> set K. fst (M ! a) < fst x"
    proof
      fix x assume "x \<in> set K"
      then obtain t where tt: "t < length K" "x = K ! t" by (metis in_set_conv_nth)
      have tb2: "t < b - Suc a" using tt(1) lenK by simp
      have "fst (M ! a) < fst (K ! t)" using Kel[OF tb2] by blast
      thus "fst (M ! a) < fst x" using tt(2) by simp
    qed
    have "takeWhile (\<lambda>r. fst (M ! a) < fst r) (drop (Suc a) M)
        = K @ takeWhile (\<lambda>r. fst (M ! a) < fst r) (M ! b # drop (Suc b) M)"
      unfolding dsplit by (rule takeWhile_append2) (use allK in blast)
    moreover have "takeWhile (\<lambda>r. fst (M ! a) < fst r) (M ! b # drop (Suc b) M) = []"
      using fb Ya Yb by simp
    ultimately show ?thesis unfolding mrun_def by simp
  qed
  have coreM: "sibrel K (mrun M b)"
  proof -
    have aM: "a < length M" using aj0 j0j1 j1len by simp
    have bM: "b < length M" using bj0 j0j1 j1len by simp
    have posM: "0 < fst (M ! a)" using pos Ya by simp
    have bdefM: "b = Suc a + length (mrun M a)" using bdef mrMa K_def by simp
    have fbM: "fst (M ! b) = fst (M ! a)" using fb Ya Yb by simp
    have sbM: "snd (M ! b) = snd (M ! a)" using sb Ya Yb by simp
    show ?thesis
      using R[unfolded sibm2_def, rule_format, OF aM posM bdefM bM fbM sbM]
      unfolding mrMa .
  qed
  have coreM': "sibrel K (P0 @ blk @ [M ! j1])"
    using coreM unfolding mrMb .
  show False
  proof (cases m)
    case 0
    have "K = P0" using EQ dropbY unfolding K_def 0 by simp
    hence "P0 @ blk @ [M ! j1] = K @ (blk @ [M ! j1])" by simp
    thus False using sibrel_nopref[OF coreM'] blkne by blast
  next
    case (Suc km)
    have cdec: "concat (map cp [0..<m]) = blk @ concat (map cp [1..<m])"
    proof -
      have "[0..<m] = 0 # [1..<m]"
        unfolding Suc by (simp add: upt_conv_Cons)
      thus ?thesis using cp0 by simp
    qed
    show False
    proof (cases "m = 1")
      case True
      have "K = P0 @ blk" using EQ dropbY cdec unfolding K_def True by simp
      hence "P0 @ blk @ [M ! j1] = K @ [M ! j1]" by simp
      thus False using sibrel_nopref[OF coreM'] by blast
    next
      case False
      hence m2: "2 \<le> m" using Suc by simp
      have cdec2: "concat (map cp [1..<m]) = cp 1 @ concat (map cp [Suc 1..<m])"
      proof -
        have "[1..<m] = 1 # [Suc 1..<m]" using m2 by (simp add: upt_conv_Cons)
        thus ?thesis by simp
      qed
      define x where "x = (entry M 0 j0 + d0, entry M 1 j0)"
      have cp1: "cp 1 = x # tl (cp 1)"
      proof -
        have "cp 1 ! 0 = x" using cpnth[OF L0] unfolding x_def by simp
        moreover have "cp 1 \<noteq> []" unfolding cp_def using j0j1 by simp
        ultimately show ?thesis by (metis hd_conv_nth list.exhaust_sel)
      qed
      have Kdec: "K = (P0 @ blk) @ x # (tl (cp 1) @ concat (map cp [Suc 1..<m]))"
        using EQ dropbY cdec cdec2 cp1 unfolding K_def by simp
      have K1Mdec: "P0 @ blk @ [M ! j1] = (P0 @ blk) @ M ! j1 # []"
        by simp
      have e0j: "entry M 0 j0 < entry M 0 j1" using hm0 j0j1 by simp
      have Mj1: "M ! j1 = (entry M 0 j1, entry M 1 j1)" using pairM by simp
      have neasc: "M ! j1 \<noteq> x \<and>
          \<not> (fst (M ! j1) < fst x
             \<or> (fst (M ! j1) = fst x \<and> snd (M ! j1) < snd x))"
      proof (cases "0 < i1")
        case False
        hence "d0 = 0" using d0d by simp
        hence "fst x = entry M 0 j0" unfolding x_def by simp
        thus ?thesis using e0j Mj1 unfolding x_def by simp
      next
        case True
        hence i1one: "i1 = 1" using idx1_le[of M j1] i1d by simp
        have dx: "fst x = entry M 0 j1"
          unfolding x_def using d0d True e0j by simp
        have "nextrel1 M j0 j1" using nR unfolding i1one nextR_def by simp
        hence "entry M 1 j0 < entry M 1 j1" unfolding nextrel1_def by blast
        thus ?thesis using dx Mj1 unfolding x_def by simp
      qed
      show False
        using sibrel_ascent[OF coreM' Kdec K1Mdec] neasc by blast
    qed
  qed
qed

text \<open>(seam, m = 1 prefix-family residual) The only genuinely new content of
  the prefix-family extension: with exactly one copy laid down, the run
  continuation \<open>D\<close> is compared against the second copy.  (Mining: 28+20
  instances; d0 = 0 needs \<open>entry M 1 j0 = 0\<close> there, d0 > 0 cases are
  empirically empty for \<open>b < j0\<close>.)\<close>

lemma seam_open_m1:
  assumes "sibm2 M" and "blockok 0 M" and "M \<in> ST_PS"
    and "j1 = Lng M - 1" and "j1 \<noteq> 0"
    and "i1 = idx1 M j1" and "hasParent M i1 j1"
    and "j0 = parent M i1 j1"
    and "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
    and "Y = take j0 M @ concat (map (\<lambda>k.
           map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j)) [j0..<j1]) [0..<m])"
    and "sibm2 Y"
    and "a < length Y" and "0 < fst (Y ! a)"
    and "b = Suc a + length (mrun Y a)" and "b < length Y"
    and "fst (Y ! b) = fst (Y ! a)" and "snd (Y ! b) = snd (Y ! a)"
    and "\<forall>x \<in> set (drop (Suc b) Y). fst (Y ! b) < fst x"
    and "fst (Y ! b) < entry M 0 j0 + m * d0"
    and "b < j0" and "m = 1"
    and "mrun Y a = drop (Suc b) Y @ D" and "D \<noteq> []"
  shows "sibrel (mrun Y a) (drop (Suc b) Y
           @ map (\<lambda>j. (entry M 0 j + m * d0, entry M 1 j)) [j0..<j1])"
  sorry

text \<open>(seam, copy-head residuals) Tight remainders of the cross-copy
  analysis at the copy head, re-audited under \<open>sibrel6\<close> at closure+3:
  the variant family \<open>E2var\<close> is empty, the prefix family \<open>P\<close> has 261
  realized instances with zero conclusion violations, the open run below
  the head (\<open>seam_open_m1\<close>) has 5447 instances with zero violations, and
  the deep position \<open>b > j0\<close> has 45 instances with zero violations.\<close>

lemma seam_copyhead_m1_E2var:
  assumes "sibm2 M" and "blockok 0 M" and "M \<in> ST_PS"
    and "j1 = Lng M - 1" and "j1 \<noteq> 0"
    and "i1 = idx1 M j1" and "hasParent M i1 j1"
    and "j0 = parent M i1 j1"
    and "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
    and "Y = take j0 M @ concat (map (\<lambda>k.
           map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j)) [j0..<j1]) [0..<m])"
    and "sibm2 Y"
    and "a < length Y" and "0 < fst (Y ! a)"
    and "b = Suc a + length (mrun Y a)" and "b < length Y"
    and "fst (Y ! b) = fst (Y ! a)" and "snd (Y ! b) = snd (Y ! a)"
    and "\<forall>x \<in> set (drop (Suc b) Y). fst (Y ! b) < fst x"
    and "fst (Y ! b) < entry M 0 j0 + m * d0"
    and "b = j0" and "m = 1"
    and "mrun Y a = drop (Suc b) Y @ D" and "D \<noteq> []"
    and "Suc j0 < j1"
    and "D = [M ! j1]"
    and "x \<in> set (drop (Suc j0) (take j1 M))" and "x \<noteq> M ! j1"
  shows "sibrel (mrun Y a) (drop (Suc b) Y
           @ map (\<lambda>j. (entry M 0 j + m * d0, entry M 1 j)) [j0..<j1])"
  sorry

lemma seam_copyhead_m1_P:
  assumes "sibm2 M" and "blockok 0 M" and "M \<in> ST_PS"
    and "j1 = Lng M - 1" and "j1 \<noteq> 0"
    and "i1 = idx1 M j1" and "hasParent M i1 j1"
    and "j0 = parent M i1 j1"
    and "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
    and "Y = take j0 M @ concat (map (\<lambda>k.
           map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j)) [j0..<j1]) [0..<m])"
    and "sibm2 Y"
    and "a < length Y" and "0 < fst (Y ! a)"
    and "b = Suc a + length (mrun Y a)" and "b < length Y"
    and "fst (Y ! b) = fst (Y ! a)" and "snd (Y ! b) = snd (Y ! a)"
    and "\<forall>x \<in> set (drop (Suc b) Y). fst (Y ! b) < fst x"
    and "fst (Y ! b) < entry M 0 j0 + m * d0"
    and "b = j0" and "m = 1"
    and "mrun Y a = drop (Suc b) Y @ D" and "D \<noteq> []"
    and "D = M ! j1 # D'" and "D' \<noteq> []"
  shows "sibrel (mrun Y a) (drop (Suc b) Y
           @ map (\<lambda>j. (entry M 0 j + m * d0, entry M 1 j)) [j0..<j1])"
  sorry

lemma seam_copyhead_m1_L2:
  assumes "sibm2 M" and "blockok 0 M" and "M \<in> ST_PS"
    and "j1 = Lng M - 1" and "j1 \<noteq> 0"
    and "i1 = idx1 M j1" and "hasParent M i1 j1"
    and "j0 = parent M i1 j1"
    and "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
    and "Y = take j0 M @ concat (map (\<lambda>k.
           map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j)) [j0..<j1]) [0..<m])"
    and "sibm2 Y"
    and "a < length Y" and "0 < fst (Y ! a)"
    and "b = Suc a + length (mrun Y a)" and "b < length Y"
    and "fst (Y ! b) = fst (Y ! a)" and "snd (Y ! b) = snd (Y ! a)"
    and "\<forall>x \<in> set (drop (Suc b) Y). fst (Y ! b) < fst x"
    and "fst (Y ! b) < entry M 0 j0 + m * d0"
    and "b = j0" and "m = 1"
    and "mrun Y a = drop (Suc b) Y @ D" and "D \<noteq> []"
    and "Suc j0 < j1"
  shows "sibrel (mrun Y a) (drop (Suc b) Y
           @ map (\<lambda>j. (entry M 0 j + m * d0, entry M 1 j)) [j0..<j1])"
proof -
  note R = assms(1) and B = assms(2) and ST = assms(3) and j1d = assms(4)
    and j1nz = assms(5) and i1d = assms(6) and hp = assms(7) and j0d = assms(8)
    and d0d = assms(9) and Yd = assms(10) and SY = assms(11) and aY = assms(12)
    and pos = assms(13) and bdef = assms(14) and bY = assms(15) and fb = assms(16)
    and sb = assms(17) and ob = assms(18) and high = assms(19) and beq = assms(20)
    and meq = assms(21) and KDef = assms(22) and Dne = assms(23) and L2 = assms(24)
  have nR: "nextR M i1 j0 j1" unfolding j0d by (rule parent_nextR[OF hp])
  have j0j1: "j0 < j1" using nR by (rule nextR_less)
  have lenM: "length M = Suc j1" using j1d j1nz by (cases M) auto
  have j1len: "j1 < length M" using lenM by simp
  define L where "L = j1 - j0"
  have L0: "0 < L" unfolding L_def using j0j1 by simp
  have lenY: "length Y = j0 + m * L"
    unfolding L_def by (rule oper_bad_len[OF Yd j0j1 j1len])
  have lenYj1: "length Y = j1" unfolding lenY L_def meq using j0j1 by simp
  have npre: "\<And>i. i < j0 \<Longrightarrow> Y ! i = M ! i"
    using oper_bad_nth_pre[OF Yd _ j1len j0j1] by blast
  have ncopy: "\<And>k q. k < m \<Longrightarrow> q < L \<Longrightarrow>
        Y ! (j0 + (k * L + q)) = (entry M 0 (j0 + q) + k * d0, entry M 1 (j0 + q))"
    unfolding L_def using oper_bad_nth_copy[OF Yd j0j1 j1len] by blast
  have hm0: "\<forall>k. j0 < k \<and> k \<le> j1 \<longrightarrow> entry M 0 j0 < entry M 0 k"
    by (rule block_head_min[OF hp j0d])
  have pairM: "\<And>j. (entry M 0 j, entry M 1 j) = M ! j"
    unfolding entry_def by simp
  have m1le: "1 \<le> m" unfolding meq by simp
  have ab: "a < b" using bdef by linarith
  have aj0: "a < j0" using ab beq by simp
  have Ya: "Y ! a = M ! a" by (rule npre[OF aj0])
  have Yj0: "Y ! j0 = (entry M 0 j0, entry M 1 j0)"
    using ncopy[of 0 0] m1le L0 by simp
  have levb: "fst (Y ! b) = entry M 0 j0" unfolding beq Yj0 by simp
  have d0pos: "0 < d0"
  proof (rule ccontr)
    assume "\<not> 0 < d0"
    hence "d0 = 0" by simp
    thus False using high levb m1le by simp
  qed
  have i1one: "i1 = 1"
    using idx1_le[of M j1] d0d d0pos i1d by (cases i1) auto
  have e0j: "entry M 0 j0 < entry M 0 j1" using hm0 j0j1 by simp
  have d0ex: "entry M 0 j0 + d0 = entry M 0 j1"
    unfolding d0d using i1one e0j by simp
  have e1j: "entry M 1 j0 < entry M 1 j1"
  proof -
    have "nextrel1 M j0 j1" using nR unfolding i1one nextR_def by simp
    thus ?thesis unfolding nextrel1_def by blast
  qed
  have Yt: "Y = take j1 M"
  proof (rule nth_equalityI)
    show "length Y = length (take j1 M)" using lenYj1 j1len by simp
  next
    fix i assume "i < length Y"
    hence ij1: "i < j1" using lenYj1 by simp
    show "Y ! i = take j1 M ! i"
    proof (cases "i < j0")
      case True thus ?thesis using npre ij1 by simp
    next
      case False
      have qL: "i - j0 < L" unfolding L_def using ij1 False by simp
      have c0: "Y ! (j0 + (0 * L + (i - j0)))
          = (entry M 0 (j0 + (i - j0)) + 0 * d0, entry M 1 (j0 + (i - j0)))"
        by (rule ncopy) (use m1le qL in simp_all)
      have ii: "j0 + (i - j0) = i" using False by simp
      have "Y ! i = (entry M 0 i, entry M 1 i)" using c0 ii by simp
      thus ?thesis using pairM ij1 by simp
    qed
  qed
  define blktail where "blktail = drop (Suc j0) (take j1 M)"
  have btlen: "length blktail = j1 - Suc j0"
    unfolding blktail_def using j1len by simp
  have btne: "blktail \<noteq> []"
  proof -
    have "0 < j1 - Suc j0" using L2 by simp
    thus ?thesis using btlen by auto
  qed
  have btnth: "\<And>t. t < j1 - Suc j0 \<Longrightarrow> blktail ! t = M ! (Suc j0 + t)"
    unfolding blktail_def using j1len j0j1 by simp
  have dropbY: "drop (Suc b) Y = blktail"
    unfolding beq Yt blktail_def ..
  define K where "K = mrun Y a"
  have KD: "K = blktail @ D" using KDef dropbY unfolding K_def by simp
  have Kne: "K \<noteq> []" using KD Dne by simp
  have DneC: "D = hd D # tl D" using Dne by simp
  have lenK: "length K = b - Suc a" unfolding K_def using bdef by simp
  have Kel: "\<And>t. t < b - Suc a \<Longrightarrow> K ! t = M ! (Suc a + t) \<and> fst (M ! a) < fst (K ! t)"
  proof -
    fix t assume tb: "t < b - Suc a"
    have tK: "t < length (mrun Y a)" using tb bdef by simp
    have tw: "K ! t = drop (Suc a) Y ! t"
      using tK unfolding K_def mrun_def by (rule takeWhile_nth)
    have "drop (Suc a) Y ! t = Y ! (Suc a + t)"
      using aY by (intro nth_drop) simp
    moreover have "Suc a + t < j0" using tb beq by simp
    ultimately have e: "K ! t = M ! (Suc a + t)" using tw npre by simp
    have "K ! t \<in> set K" using tb lenK by simp
    hence "fst (Y ! a) < fst (K ! t)"
      unfolding K_def mrun_def using set_takeWhileD by metis
    thus "K ! t = M ! (Suc a + t) \<and> fst (M ! a) < fst (K ! t)"
      using e Ya by simp
  qed
  have Mb: "M ! j0 = Y ! b" unfolding beq Yj0 using pairM by simp
  have mrMa: "mrun M a = K"
  proof -
    have bM: "b < length M" using beq j0j1 j1len by simp
    have Keq: "K = take (b - Suc a) (drop (Suc a) M)"
    proof (rule nth_equalityI)
      show "length K = length (take (b - Suc a) (drop (Suc a) M))"
        using lenK bM by simp
    next
      fix t assume "t < length K"
      hence tb: "t < b - Suc a" using lenK by simp
      show "K ! t = take (b - Suc a) (drop (Suc a) M) ! t"
        using Kel[OF tb] tb bM by simp
    qed
    have dsplit: "drop (Suc a) M = K @ M ! b # drop (Suc b) M"
    proof -
      have "drop (Suc a) M = take (b - Suc a) (drop (Suc a) M)
          @ drop (b - Suc a) (drop (Suc a) M)"
        by (rule append_take_drop_id[symmetric])
      moreover have "drop (b - Suc a) (drop (Suc a) M) = drop b M"
        using ab by (simp add: drop_drop)
      moreover have "drop b M = M ! b # drop (Suc b) M"
        using bM by (rule Cons_nth_drop_Suc[symmetric])
      ultimately show ?thesis using Keq by metis
    qed
    have allK: "\<forall>x \<in> set K. fst (M ! a) < fst x"
    proof
      fix x assume "x \<in> set K"
      then obtain t where tt: "t < length K" "x = K ! t" by (metis in_set_conv_nth)
      have tb2: "t < b - Suc a" using tt(1) lenK by simp
      have "fst (M ! a) < fst (K ! t)" using Kel[OF tb2] by blast
      thus "fst (M ! a) < fst x" using tt(2) by simp
    qed
    have "takeWhile (\<lambda>r. fst (M ! a) < fst r) (drop (Suc a) M)
        = K @ takeWhile (\<lambda>r. fst (M ! a) < fst r) (M ! b # drop (Suc b) M)"
      unfolding dsplit by (rule takeWhile_append2) (use allK in blast)
    moreover have "takeWhile (\<lambda>r. fst (M ! a) < fst r) (M ! b # drop (Suc b) M) = []"
    proof -
      have "fst (M ! b) = fst (M ! a)"
        using fb Ya Mb unfolding beq by simp
      thus ?thesis by simp
    qed
    ultimately show ?thesis unfolding mrun_def by simp
  qed
  have dropj0M: "drop (Suc j0) M = blktail @ [M ! j1]"
  proof -
    have Mdec: "M = take j1 M @ [M ! j1]"
    proof -
      have "drop j1 M = M ! j1 # drop (Suc j1) M"
        using j1len by (rule Cons_nth_drop_Suc[symmetric])
      moreover have "drop (Suc j1) M = []" using lenM by simp
      ultimately have "drop j1 M = [M ! j1]" by simp
      thus ?thesis by (metis append_take_drop_id)
    qed
    have "drop (Suc j0) M = drop (Suc j0) (take j1 M)
        @ drop (Suc j0 - length (take j1 M)) [M ! j1]"
      by (subst Mdec) (rule drop_append)
    thus ?thesis unfolding blktail_def using j0j1 j1len by simp
  qed
  have obMj0: "\<forall>x \<in> set (drop (Suc j0) M). fst (M ! j0) < fst x"
  proof
    fix x assume "x \<in> set (drop (Suc j0) M)"
    then obtain t where t: "t < length M - Suc j0" "x = drop (Suc j0) M ! t"
      by (metis in_set_conv_nth length_drop)
    have xi: "x = M ! (Suc j0 + t)"
    proof -
      have "drop (Suc j0) M ! t = M ! (Suc j0 + t)"
        by (intro nth_drop) (use j0j1 j1len in simp)
      thus ?thesis using t(2) by simp
    qed
    have "entry M 0 j0 < entry M 0 (Suc j0 + t)"
      using hm0 t(1) lenM by simp
    thus "fst (M ! j0) < fst x" using xi unfolding entry_def by simp
  qed
  have mrMb: "mrun M b = blktail @ [M ! j1]"
  proof -
    have "mrun M b = drop (Suc j0) M"
      unfolding mrun_def beq using obMj0 by (simp add: takeWhile_eq_all_conv)
    thus ?thesis unfolding dropj0M .
  qed
  have coreM: "sibrel K (blktail @ [M ! j1])"
  proof -
    have aM: "a < length M" using aj0 j0j1 j1len by simp
    have bM: "b < length M" using beq j0j1 j1len by simp
    have posM: "0 < fst (M ! a)" using pos Ya by simp
    have bdefM: "b = Suc a + length (mrun M a)" using bdef mrMa K_def by simp
    have fbM: "fst (M ! b) = fst (M ! a)" using fb Ya Mb unfolding beq by simp
    have sbM: "snd (M ! b) = snd (M ! a)" using sb Ya Mb unfolding beq by simp
    show ?thesis
      using R[unfolded sibm2_def, rule_format, OF aM posM bdefM bM fbM sbM]
      unfolding mrMa mrMb .
  qed
  define C1 where "C1 = map (\<lambda>j. (entry M 0 j + m * d0, entry M 1 j)) [j0..<j1]"
  have C1ne: "C1 \<noteq> []" unfolding C1_def using j0j1 by simp
  have C1nth0: "C1 ! 0 = (entry M 0 j1, entry M 1 j0)"
  proof -
    have "C1 ! 0 = (entry M 0 j0 + m * d0, entry M 1 j0)"
      unfolding C1_def using j0j1 by simp
    thus ?thesis using d0ex meq by simp
  qed
  have C1hd: "C1 = (entry M 0 j1, entry M 1 j0) # tl C1"
    using C1nth0 C1ne by (metis hd_conv_nth list.exhaust_sel)
  have C1snd: "\<And>x. x \<in> set C1 \<Longrightarrow>
      snd x = entry M 1 j0 \<or> (\<exists>j. Suc j0 \<le> j \<and> j < j1 \<and> snd x = entry M 1 j)"
  proof -
    fix x assume "x \<in> set C1"
    then obtain j where j1c: "j \<in> set [j0..<j1]"
        and j2c: "x = (entry M 0 j + m * d0, entry M 1 j)"
      unfolding C1_def by auto
    have jr: "j0 \<le> j" "j < j1" using j1c by auto
    show "snd x = entry M 1 j0 \<or> (\<exists>j. Suc j0 \<le> j \<and> j < j1 \<and> snd x = entry M 1 j)"
    proof (cases "j = j0")
      case True
      thus ?thesis using j2c by simp
    next
      case False
      have "Suc j0 \<le> j \<and> j < j1 \<and> snd x = entry M 1 j"
        using jr False j2c by simp
      thus ?thesis by blast
    qed
  qed
  have btsnd_le: "\<And>x ub. (\<And>y. y \<in> set blktail \<Longrightarrow> snd y \<le> ub) \<Longrightarrow>
      x \<in> set C1 \<Longrightarrow> entry M 1 j0 \<le> ub \<Longrightarrow> snd x \<le> ub"
  proof -
    fix x ub assume bt: "\<And>y. y \<in> set blktail \<Longrightarrow> snd y \<le> ub"
      and xc: "x \<in> set C1" and j0le: "entry M 1 j0 \<le> ub"
    from C1snd[OF xc] show "snd x \<le> ub"
    proof
      assume "snd x = entry M 1 j0"
      thus ?thesis using j0le by simp
    next
      assume "\<exists>j. Suc j0 \<le> j \<and> j < j1 \<and> snd x = entry M 1 j"
      then obtain j where jj: "Suc j0 \<le> j" "j < j1" "snd x = entry M 1 j" by blast
      have tj: "j - Suc j0 < length blktail" using jj btlen by simp
      have "blktail ! (j - Suc j0) = M ! j"
        using btnth[of "j - Suc j0"] jj btlen by simp
      hence "M ! j \<in> set blktail" using tj by (metis nth_mem)
      hence "snd (M ! j) \<le> ub" by (rule bt)
      thus ?thesis using jj(3) unfolding entry_def by simp
    qed
  qed
  have goalC: "drop (Suc b) Y
      @ map (\<lambda>j. (entry M 0 j + m * d0, entry M 1 j)) [j0..<j1] = blktail @ C1"
    unfolding dropbY C1_def ..
  have main: "sibrel K (blktail @ C1)"
  proof (cases "M ! j1 = hd D")
    case hdeq: True
    show ?thesis
    proof (cases "tl D = []")
      case tlD: True
      have Deq: "D = [M ! j1]"
        using DneC tlD unfolding hdeq by simp
      have Keq: "K = blktail @ [M ! j1]" using KD Deq by simp
      show ?thesis
      proof (cases "\<forall>x \<in> set blktail. x = M ! j1")
        case allc: True
        have hdbt: "hd blktail = M ! j1" using allc btne by (cases blktail) auto
        have hdK: "hd K = M ! j1" using Keq btne hdbt by (simp add: hd_append)
        have hmK: "snd (hd K) = maxr1 K"
        proof -
          have "snd ` set K = {snd (M ! j1)}" using Keq allc Kne by auto
          thus ?thesis unfolding maxr1_def hdK by simp
        qed
        have e1top: "\<And>x. x \<in> set (blktail @ C1) \<Longrightarrow> snd x \<le> snd (M ! j1)"
        proof -
          fix x assume "x \<in> set (blktail @ C1)"
          then consider (bt) "x \<in> set blktail" | (c1) "x \<in> set C1" by auto
          thus "snd x \<le> snd (M ! j1)"
          proof cases
            case bt thus ?thesis using allc by simp
          next
            case c1
            have btb: "\<And>y. y \<in> set blktail \<Longrightarrow> snd y \<le> snd (M ! j1)"
              using allc by simp
            have j0b: "entry M 1 j0 \<le> snd (M ! j1)"
              using e1j unfolding entry_def by simp
            show ?thesis by (rule btsnd_le[OF btb c1 j0b])
          qed
        qed
        have hdBC: "hd (blktail @ C1) = M ! j1" using btne hdbt by (simp add: hd_append)
        have hmK1: "snd (hd (blktail @ C1)) = maxr1 (blktail @ C1)"
        proof -
          have mem: "snd (M ! j1) \<in> snd ` set (blktail @ C1)"
            using btne hdbt by (metis hd_in_set image_eqI set_append UnI1)
          have "Max (snd ` set (blktail @ C1)) = snd (M ! j1)"
            by (rule Max_eqI) (use e1top mem in auto)
          thus ?thesis unfolding maxr1_def hdBC by simp
        qed
        have desc: "fst (entry M 0 j1, entry M 1 j0) = fst (M ! j1) \<and>
                    snd (entry M 0 j1, entry M 1 j0) < snd (M ! j1)"
          using e1j unfolding entry_def by simp
        have decC: "blktail @ C1 = blktail @ (entry M 0 j1, entry M 1 j0) # tl C1"
          using C1hd by metis
        have "snd (hd K) = maxr1 K \<and>
              snd (hd (blktail @ C1)) = maxr1 (blktail @ C1) \<and>
              K = blktail @ M ! j1 # [] \<and>
              blktail @ C1 = blktail @ (entry M 0 j1, entry M 1 j0) # tl C1 \<and>
              ((fst (entry M 0 j1, entry M 1 j0) = fst (M ! j1) \<and>
                snd (entry M 0 j1, entry M 1 j0) < snd (M ! j1))
               \<or> (fst (entry M 0 j1, entry M 1 j0) < fst (M ! j1) \<and>
                  snd (entry M 0 j1, entry M 1 j0) = snd (M ! j1)))"
          using hmK hmK1 Keq decC desc by simp
        thus ?thesis unfolding sibrel_def by blast
      next
        case False
        then obtain x where xb: "x \<in> set blktail" "x \<noteq> M ! j1" by blast
        show ?thesis
          using seam_copyhead_m1_E2var[OF R B ST j1d j1nz i1d hp j0d d0d Yd SY
              aY pos bdef bY fb sb ob high beq meq KDef Dne L2 Deq
              xb(1)[unfolded blktail_def] xb(2)]
          unfolding K_def goalC by simp
      qed
    next
      case tlD: False
      have DP: "D = M ! j1 # tl D" using DneC unfolding hdeq by simp
      show ?thesis
        using seam_copyhead_m1_P[OF R B ST j1d j1nz i1d hp j0d d0d Yd SY
            aY pos bdef bY fb sb ob high beq meq KDef Dne DP tlD]
        unfolding K_def goalC by simp
    qed
  next
    case hdne: False
    have decK: "K = blktail @ hd D # tl D" using KD DneC by metis
    have decM: "blktail @ [M ! j1] = blktail @ M ! j1 # []" by simp
    have div: "fst (M ! j1) < fst (hd D)
             \<or> (fst (M ! j1) = fst (hd D) \<and> snd (M ! j1) < snd (hd D))"
      by (rule sibrel_diverge[OF coreM decK decM hdne])
    have lnk: "entry M 1 j0 < snd (M ! j1)" using e1j unfolding entry_def by simp
    have decC: "blktail @ C1 = blktail @ (entry M 0 j1, entry M 1 j0) # tl C1"
      using C1hd by metis
    have lexC: "fst (entry M 0 j1, entry M 1 j0) < fst (hd D)
              \<or> (fst (entry M 0 j1, entry M 1 j0) = fst (hd D)
                  \<and> snd (entry M 0 j1, entry M 1 j0) < snd (hd D))"
    proof -
      from div show ?thesis
      proof
        assume a: "fst (M ! j1) < fst (hd D)"
        have "fst (entry M 0 j1, entry M 1 j0) = fst (M ! j1)"
          unfolding entry_def by simp
        thus ?thesis using a by simp
      next
        assume a: "fst (M ! j1) = fst (hd D) \<and> snd (M ! j1) < snd (hd D)"
        have f: "fst (entry M 0 j1, entry M 1 j0) = fst (hd D)"
          using a unfolding entry_def by simp
        have "entry M 1 j0 < snd (hd D)" using lnk a by linarith
        thus ?thesis using f by simp
      qed
    qed
    have "K = blktail @ hd D # tl D \<and>
          blktail @ C1 = blktail @ (entry M 0 j1, entry M 1 j0) # tl C1 \<and>
          (fst (entry M 0 j1, entry M 1 j0) < fst (hd D)
           \<or> (fst (entry M 0 j1, entry M 1 j0) = fst (hd D)
               \<and> snd (entry M 0 j1, entry M 1 j0) < snd (hd D)))"
      using decK decC lexC by blast
    thus ?thesis unfolding sibrel_def by blast
  qed
  show ?thesis using main unfolding K_def[symmetric] goalC by simp
qed

lemma seam_copyhead_m1:
  assumes "sibm2 M" and "blockok 0 M" and "M \<in> ST_PS"
    and "j1 = Lng M - 1" and "j1 \<noteq> 0"
    and "i1 = idx1 M j1" and "hasParent M i1 j1"
    and "j0 = parent M i1 j1"
    and "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
    and "Y = take j0 M @ concat (map (\<lambda>k.
           map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j)) [j0..<j1]) [0..<m])"
    and "sibm2 Y"
    and "a < length Y" and "0 < fst (Y ! a)"
    and "b = Suc a + length (mrun Y a)" and "b < length Y"
    and "fst (Y ! b) = fst (Y ! a)" and "snd (Y ! b) = snd (Y ! a)"
    and "\<forall>x \<in> set (drop (Suc b) Y). fst (Y ! b) < fst x"
    and "fst (Y ! b) < entry M 0 j0 + m * d0"
    and "b = j0" and "m = 1"
    and "mrun Y a = drop (Suc b) Y @ D" and "D \<noteq> []"
  shows "sibrel (mrun Y a) (drop (Suc b) Y
           @ map (\<lambda>j. (entry M 0 j + m * d0, entry M 1 j)) [j0..<j1])"
proof -
  note R = assms(1) and B = assms(2) and ST = assms(3) and j1d = assms(4)
    and j1nz = assms(5) and i1d = assms(6) and hp = assms(7) and j0d = assms(8)
    and d0d = assms(9) and Yd = assms(10) and SY = assms(11) and aY = assms(12)
    and pos = assms(13) and bdef = assms(14) and bY = assms(15) and fb = assms(16)
    and sb = assms(17) and ob = assms(18) and high = assms(19) and beq = assms(20)
    and meq = assms(21) and KDef = assms(22) and Dne = assms(23)
  show ?thesis
  proof (cases "Suc j0 < j1")
    case True
    show ?thesis
      by (rule seam_copyhead_m1_L2[OF R B ST j1d j1nz i1d hp j0d d0d Yd SY
            aY pos bdef bY fb sb ob high beq meq KDef Dne True])
  next
    case False
    have nR: "nextR M i1 j0 j1" unfolding j0d by (rule parent_nextR[OF hp])
    have j0j1: "j0 < j1" using nR by (rule nextR_less)
    have Leq: "j1 = Suc j0" using False j0j1 by simp
    have lenM: "length M = Suc j1" using j1d j1nz by (cases M) auto
    have j1len: "j1 < length M" using lenM by simp
    define L where "L = j1 - j0"
    have L0: "0 < L" unfolding L_def using j0j1 by simp
    have L1: "L = 1" unfolding L_def Leq by simp
    have lenY: "length Y = j0 + m * L"
      unfolding L_def by (rule oper_bad_len[OF Yd j0j1 j1len])
    have lenY1: "length Y = Suc j0" unfolding lenY L1 meq by simp
    have npre: "\<And>i. i < j0 \<Longrightarrow> Y ! i = M ! i"
      using oper_bad_nth_pre[OF Yd _ j1len j0j1] by blast
    have ncopy: "\<And>k q. k < m \<Longrightarrow> q < L \<Longrightarrow>
          Y ! (j0 + (k * L + q)) = (entry M 0 (j0 + q) + k * d0, entry M 1 (j0 + q))"
      unfolding L_def using oper_bad_nth_copy[OF Yd j0j1 j1len] by blast
    have hm0: "\<forall>k. j0 < k \<and> k \<le> j1 \<longrightarrow> entry M 0 j0 < entry M 0 k"
      by (rule block_head_min[OF hp j0d])
    have pairM: "\<And>j. (entry M 0 j, entry M 1 j) = M ! j"
      unfolding entry_def by simp
    have m1le: "1 \<le> m" unfolding meq by simp
    have ab: "a < b" using bdef by linarith
    have aj0: "a < j0" using ab beq by simp
    have Ya: "Y ! a = M ! a" by (rule npre[OF aj0])
    have Yj0: "Y ! j0 = (entry M 0 j0, entry M 1 j0)"
      using ncopy[of 0 0] m1le L0 by simp
    have levb: "fst (Y ! b) = entry M 0 j0" unfolding beq Yj0 by simp
    have d0pos: "0 < d0"
    proof (rule ccontr)
      assume "\<not> 0 < d0"
      hence "d0 = 0" by simp
      thus False using high levb m1le by simp
    qed
    have i1one: "i1 = 1"
      using idx1_le[of M j1] d0d d0pos i1d by (cases i1) auto
    have e0j: "entry M 0 j0 < entry M 0 j1" using hm0 j0j1 by simp
    have d0ex: "entry M 0 j0 + d0 = entry M 0 j1"
      unfolding d0d using i1one e0j by simp
    have e1j: "entry M 1 j0 < entry M 1 j1"
    proof -
      have "nextrel1 M j0 j1" using nR unfolding i1one nextR_def by simp
      thus ?thesis unfolding nextrel1_def by blast
    qed
    define K where "K = mrun Y a"
    have dropY: "drop (Suc b) Y = []" unfolding beq using lenY1 by simp
    have KD: "K = D" using KDef dropY unfolding K_def by simp
    have Kne: "K \<noteq> []" using KD Dne by simp
    have lenK: "length K = b - Suc a" unfolding K_def using bdef by simp
    have Kel: "\<And>t. t < b - Suc a \<Longrightarrow> K ! t = M ! (Suc a + t) \<and> fst (M ! a) < fst (K ! t)"
    proof -
      fix t assume tb: "t < b - Suc a"
      have tK: "t < length (mrun Y a)" using tb bdef by simp
      have tw: "K ! t = drop (Suc a) Y ! t"
        using tK unfolding K_def mrun_def by (rule takeWhile_nth)
      have "drop (Suc a) Y ! t = Y ! (Suc a + t)"
        using aY by (intro nth_drop) simp
      moreover have "Suc a + t < j0" using tb beq by simp
      ultimately have e: "K ! t = M ! (Suc a + t)" using tw npre by simp
      have "K ! t \<in> set K" using tb lenK by simp
      hence "fst (Y ! a) < fst (K ! t)"
        unfolding K_def mrun_def using set_takeWhileD by metis
      thus "K ! t = M ! (Suc a + t) \<and> fst (M ! a) < fst (K ! t)"
        using e Ya by simp
    qed
    have Mb: "M ! j0 = Y ! b" unfolding beq Yj0 using pairM by simp
    have mrMa: "mrun M a = K"
    proof -
      have bM: "b < length M" using beq j0j1 j1len by simp
      have Keq: "K = take (b - Suc a) (drop (Suc a) M)"
      proof (rule nth_equalityI)
        show "length K = length (take (b - Suc a) (drop (Suc a) M))"
          using lenK bM by simp
      next
        fix t assume "t < length K"
        hence tb: "t < b - Suc a" using lenK by simp
        show "K ! t = take (b - Suc a) (drop (Suc a) M) ! t"
          using Kel[OF tb] tb bM by simp
      qed
      have dsplit: "drop (Suc a) M = K @ M ! b # drop (Suc b) M"
      proof -
        have "drop (Suc a) M = take (b - Suc a) (drop (Suc a) M)
            @ drop (b - Suc a) (drop (Suc a) M)"
          by (rule append_take_drop_id[symmetric])
        moreover have "drop (b - Suc a) (drop (Suc a) M) = drop b M"
          using ab by (simp add: drop_drop)
        moreover have "drop b M = M ! b # drop (Suc b) M"
          using bM by (rule Cons_nth_drop_Suc[symmetric])
        ultimately show ?thesis using Keq by metis
      qed
      have allK: "\<forall>x \<in> set K. fst (M ! a) < fst x"
      proof
        fix x assume "x \<in> set K"
        then obtain t where tt: "t < length K" "x = K ! t" by (metis in_set_conv_nth)
        have tb2: "t < b - Suc a" using tt(1) lenK by simp
        have "fst (M ! a) < fst (K ! t)" using Kel[OF tb2] by blast
        thus "fst (M ! a) < fst x" using tt(2) by simp
      qed
      have "takeWhile (\<lambda>r. fst (M ! a) < fst r) (drop (Suc a) M)
          = K @ takeWhile (\<lambda>r. fst (M ! a) < fst r) (M ! b # drop (Suc b) M)"
        unfolding dsplit by (rule takeWhile_append2) (use allK in blast)
      moreover have "takeWhile (\<lambda>r. fst (M ! a) < fst r) (M ! b # drop (Suc b) M) = []"
      proof -
        have "fst (M ! b) = fst (M ! a)"
          using fb Ya Mb unfolding beq by simp
        thus ?thesis by simp
      qed
      ultimately show ?thesis unfolding mrun_def by simp
    qed
    have dropj1: "drop j1 M = [M ! j1]"
    proof -
      have "drop j1 M = M ! j1 # drop (Suc j1) M"
        using j1len by (rule Cons_nth_drop_Suc[symmetric])
      moreover have "drop (Suc j1) M = []" using lenM by simp
      ultimately show ?thesis by simp
    qed
    have dropj0M: "drop (Suc j0) M = [M ! j1]" using dropj1 Leq by simp
    have Mj0f: "fst (M ! j0) = entry M 0 j0" unfolding entry_def by simp
    have Mj1f: "fst (M ! j1) = entry M 0 j1" unfolding entry_def by simp
    have Mj1s: "snd (M ! j1) = entry M 1 j1" unfolding entry_def by simp
    have mrMb: "mrun M b = [M ! j1]"
      unfolding mrun_def beq dropj0M using e0j Mj0f Mj1f by simp
    have coreM: "sibrel K [M ! j1]"
    proof -
      have aM: "a < length M" using aj0 j0j1 j1len by simp
      have bM: "b < length M" using beq j0j1 j1len by simp
      have posM: "0 < fst (M ! a)" using pos Ya by simp
      have bdefM: "b = Suc a + length (mrun M a)" using bdef mrMa K_def by simp
      have fbM: "fst (M ! b) = fst (M ! a)" using fb Ya Mb unfolding beq by simp
      have sbM: "snd (M ! b) = snd (M ! a)" using sb Ya Mb unfolding beq by simp
      show ?thesis
        using R[unfolded sibm2_def, rule_format, OF aM posM bdefM bM fbM sbM]
        unfolding mrMa mrMb .
    qed
    define xx where "xx = (entry M 0 j1, entry M 1 j0)"
    have mapxx: "map (\<lambda>j. (entry M 0 j + m * d0, entry M 1 j)) [j0..<j1] = [xx]"
    proof -
      have "[j0..<j1] = [j0]" unfolding Leq by simp
      thus ?thesis unfolding xx_def meq using d0ex by simp
    qed
    have hdK: "K ! 0 = M ! (Suc a)"
    proof -
      have "0 < b - Suc a" using lenK Kne by (cases "b - Suc a") auto
      thus ?thesis using Kel[of 0] by simp
    qed
    have hdK': "hd K = M ! (Suc a)" using hdK Kne by (simp add: hd_conv_nth)
    have Kdec: "K = M ! (Suc a) # tl K" using Kne hdK' by (cases K) auto
    have stepA: "fst (M ! Suc a) \<le> Suc (fst (M ! a))"
    proof -
      have "Suc a < length M" using aj0 j0j1 j1len by simp
      thus ?thesis using B unfolding blockok_def by simp
    qed
    have fstMa: "fst (M ! a) = entry M 0 j0"
    proof -
      have "fst (Y ! a) = fst (Y ! b)" using fb by simp
      thus ?thesis using Ya levb by simp
    qed
    have main: "sibrel K [xx]"
    proof (cases "M ! j1 = M ! (Suc a)")
      case hdeq: True
      show ?thesis
      proof (cases "tl K = []")
        case True
        have Keq1: "K = [M ! j1]" using Kdec hdeq True by simp
        have desc: "fst xx = fst (M ! j1) \<and> snd xx < snd (M ! j1)"
          unfolding xx_def using Mj1f Mj1s e1j by simp
        have "snd (hd K) = maxr1 K \<and> snd (hd [xx]) = maxr1 [xx] \<and>
              K = [] @ M ! j1 # [] \<and> [xx] = [] @ xx # [] \<and>
              ((fst xx = fst (M ! j1) \<and> snd xx < snd (M ! j1))
               \<or> (fst xx < fst (M ! j1) \<and> snd xx = snd (M ! j1)))"
          using Keq1 desc by (simp add: maxr1_def)
        thus ?thesis unfolding sibrel_def by blast
      next
        case tlne: False
        have DP: "D = M ! j1 # tl K"
          using KD Kdec hdeq by metis
        show ?thesis
          using seam_copyhead_m1_P[OF R B ST j1d j1nz i1d hp j0d d0d Yd SY
              aY pos bdef bY fb sb ob high beq meq KDef Dne DP tlne]
          unfolding K_def dropY mapxx by simp
      qed
    next
      case hdne: False
      have dK: "K = [] @ M ! (Suc a) # tl K" using Kdec by simp
      have dK2: "[M ! j1] = [] @ M ! j1 # []" by simp
      have div: "fst (M ! j1) < fst (M ! (Suc a))
               \<or> (fst (M ! j1) = fst (M ! (Suc a)) \<and> snd (M ! j1) < snd (M ! (Suc a)))"
        by (rule sibrel_diverge[OF coreM dK dK2]) (use hdne in simp)
      from div consider
        (F1) "fst (M ! j1) = fst (M ! (Suc a))" "snd (M ! j1) < snd (M ! (Suc a))"
        | (F2) "fst (M ! j1) < fst (M ! (Suc a))"
        by blast
      thus ?thesis
      proof cases
        case F1
        have desc: "fst xx = fst (M ! (Suc a)) \<and> snd xx < snd (M ! (Suc a))"
          unfolding xx_def using Mj1f Mj1s e1j F1 by simp
        have "K = [] @ M ! (Suc a) # tl K \<and> [xx] = [] @ xx # [] \<and>
              (fst xx < fst (M ! (Suc a))
               \<or> (fst xx = fst (M ! (Suc a)) \<and> snd xx < snd (M ! (Suc a))))"
          using desc dK by simp
        thus ?thesis unfolding sibrel_def by blast
      next
        case F2
        have "fst (M ! (Suc a)) \<le> Suc (entry M 0 j0)" using stepA fstMa by simp
        moreover have "Suc (entry M 0 j0) \<le> entry M 0 j1"
          using d0ex d0pos by linarith
        moreover have "entry M 0 j1 < fst (M ! (Suc a))" using F2(1) Mj1f by simp
        ultimately have False by simp
        thus ?thesis ..
      qed
    qed
    show ?thesis
      using main unfolding K_def[symmetric] dropY mapxx by simp
  qed
qed

lemma seam_copyhead_deep:
  assumes "sibm2 M" and "blockok 0 M" and "M \<in> ST_PS"
    and "j1 = Lng M - 1" and "j1 \<noteq> 0"
    and "i1 = idx1 M j1" and "hasParent M i1 j1"
    and "j0 = parent M i1 j1"
    and "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
    and "Y = take j0 M @ concat (map (\<lambda>k.
           map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j)) [j0..<j1]) [0..<m])"
    and "sibm2 Y"
    and "a < length Y" and "0 < fst (Y ! a)"
    and "b = Suc a + length (mrun Y a)" and "b < length Y"
    and "fst (Y ! b) = fst (Y ! a)" and "snd (Y ! b) = snd (Y ! a)"
    and "\<forall>x \<in> set (drop (Suc b) Y). fst (Y ! b) < fst x"
    and "fst (Y ! b) < entry M 0 j0 + m * d0"
    and "j0 < b"
  shows "sibrel (mrun Y a) (drop (Suc b) Y
           @ map (\<lambda>j. (entry M 0 j + m * d0, entry M 1 j)) [j0..<j1])"
  sorry

lemma seam_open_copyhead:
  assumes "sibm2 M" and "blockok 0 M" and "M \<in> ST_PS"
    and "j1 = Lng M - 1" and "j1 \<noteq> 0"
    and "i1 = idx1 M j1" and "hasParent M i1 j1"
    and "j0 = parent M i1 j1"
    and "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
    and "Y = take j0 M @ concat (map (\<lambda>k.
           map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j)) [j0..<j1]) [0..<m])"
    and "sibm2 Y"
    and "a < length Y" and "0 < fst (Y ! a)"
    and "b = Suc a + length (mrun Y a)" and "b < length Y"
    and "fst (Y ! b) = fst (Y ! a)" and "snd (Y ! b) = snd (Y ! a)"
    and "\<forall>x \<in> set (drop (Suc b) Y). fst (Y ! b) < fst x"
    and "fst (Y ! b) < entry M 0 j0 + m * d0"
    and "j0 \<le> b"
  shows "sibrel (mrun Y a) (drop (Suc b) Y
           @ map (\<lambda>j. (entry M 0 j + m * d0, entry M 1 j)) [j0..<j1])"
proof -
  note R = assms(1) and B = assms(2) and ST = assms(3) and j1d = assms(4)
    and j1nz = assms(5) and i1d = assms(6) and hp = assms(7) and j0d = assms(8)
    and d0d = assms(9) and Yd = assms(10) and SY = assms(11) and aY = assms(12)
    and pos = assms(13) and bdef = assms(14) and bY = assms(15) and fb = assms(16)
    and sb = assms(17) and ob = assms(18) and high = assms(19) and bj0 = assms(20)
  show ?thesis
  proof (cases "b = j0")
    case False
    hence bgt: "j0 < b" using bj0 by simp
    show ?thesis
      by (rule seam_copyhead_deep[OF R B ST j1d j1nz i1d hp j0d d0d Yd SY
            aY pos bdef bY fb sb ob high bgt])
  next
    case beq: True
    define cp where "cp = (\<lambda>k. map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j)) [j0..<j1])"
    define C where "C = cp m"
    define K where "K = mrun Y a"
    define K1 where "K1 = drop (Suc b) Y"
    have mapC: "map (\<lambda>j. (entry M 0 j + m * d0, entry M 1 j)) [j0..<j1] = C"
      unfolding C_def cp_def ..
    have Yd': "Y = take j0 M @ concat (map cp [0..<m])"
      unfolding cp_def by (rule Yd)
    have nR: "nextR M i1 j0 j1" unfolding j0d by (rule parent_nextR[OF hp])
    have j0j1: "j0 < j1" using nR by (rule nextR_less)
    have lenM: "length M = Suc j1" using j1d j1nz by (cases M) auto
    have j1len: "j1 < length M" using lenM by simp
    define L where "L = j1 - j0"
    have L0: "0 < L" unfolding L_def using j0j1 by simp
    have lenY: "length Y = j0 + m * L"
      unfolding L_def by (rule oper_bad_len[OF Yd j0j1 j1len])
    have npre: "\<And>i. i < j0 \<Longrightarrow> Y ! i = M ! i"
      using oper_bad_nth_pre[OF Yd _ j1len j0j1] by blast
    have ncopy: "\<And>k q. k < m \<Longrightarrow> q < L \<Longrightarrow>
          Y ! (j0 + (k * L + q)) = (entry M 0 (j0 + q) + k * d0, entry M 1 (j0 + q))"
      unfolding L_def using oper_bad_nth_copy[OF Yd j0j1 j1len] by blast
    have hm0: "\<forall>k. j0 < k \<and> k \<le> j1 \<longrightarrow> entry M 0 j0 < entry M 0 k"
      by (rule block_head_min[OF hp j0d])
    have pairM: "\<And>j. (entry M 0 j, entry M 1 j) = M ! j"
      unfolding entry_def by simp
    have m1le: "1 \<le> m" using beq bY lenY by (cases m) auto
    have ab: "a < b" using bdef by linarith
    have Yj0: "Y ! j0 = (entry M 0 j0, entry M 1 j0)"
      using ncopy[of 0 0] m1le L0 by simp
    have levb: "fst (Y ! b) = entry M 0 j0" unfolding beq Yj0 by simp
    have d0pos: "0 < d0"
    proof (rule ccontr)
      assume "\<not> 0 < d0"
      hence "d0 = 0" by simp
      thus False using high levb m1le by simp
    qed
    have i1one: "i1 = 1"
      using idx1_le[of M j1] d0d d0pos i1d by (cases i1) auto
    have e0j: "entry M 0 j0 < entry M 0 j1" using hm0 j0j1 by simp
    have d0ex: "entry M 0 j0 + d0 = entry M 0 j1"
      unfolding d0d using i1one e0j by simp
    have e1j: "entry M 1 j0 < entry M 1 j1"
    proof -
      have "nextrel1 M j0 j1" using nR unfolding i1one nextR_def by simp
      thus ?thesis unfolding nextrel1_def by blast
    qed
    have aj0: "a < j0" using ab beq by simp
    have Ya: "Y ! a = M ! a" by (rule npre[OF aj0])
    define blk where "blk = drop j0 (take j1 M)"
    define blktail where "blktail = drop (Suc j0) (take j1 M)"
    have lenblk: "length blk = L" unfolding blk_def L_def using j1len by simp
    have blkne: "blk \<noteq> []" using lenblk L0 by auto
    have blknth: "\<And>q. q < L \<Longrightarrow> blk ! q = M ! (j0 + q)"
      unfolding blk_def L_def using j1len by simp
    have cpnth: "\<And>k q. q < L \<Longrightarrow> cp k ! q = (entry M 0 (j0+q) + k * d0, entry M 1 (j0+q))"
      unfolding cp_def L_def by simp
    have cpk_shf: "\<And>k. cp k = shf (k * d0) blk"
    proof (rule nth_equalityI)
      fix k show "length (cp k) = length (shf (k * d0) blk)"
        using lenblk unfolding L_def by (simp add: cp_def)
    next
      fix k q assume "q < length (cp k)"
      hence qL: "q < L" unfolding cp_def L_def by simp
      have "shf (k * d0) blk ! q = (fst (M ! (j0+q)) + k * d0, snd (M ! (j0+q)))"
        using shf_nth[of q blk "k * d0"] blknth[OF qL] lenblk qL by simp
      thus "cp k ! q = shf (k * d0) blk ! q"
        using cpnth[OF qL] unfolding entry_def by simp
    qed
    have cp0: "cp 0 = blk" using cpk_shf[of 0] by simp
    have bt_blk: "blktail = drop 1 blk"
      unfolding blktail_def blk_def by (simp add: drop_drop)
    have sndC: "\<And>c. c \<in> set C \<Longrightarrow> \<exists>c' \<in> set blk. snd c = snd c'"
    proof -
      fix c assume "c \<in> set C"
      hence "c \<in> set (shf (m * d0) blk)" using cpk_shf unfolding C_def by simp
      thus "\<exists>c' \<in> set blk. snd c = snd c'"
        unfolding shf_def by force
    qed
    have blkdec: "blk = blk ! 0 # drop 1 blk"
      using blkne by (cases blk) auto
    have sndblk: "\<And>c. c \<in> set blk \<Longrightarrow> snd c = entry M 1 j0 \<or> c \<in> set blktail"
    proof -
      fix c assume "c \<in> set blk"
      hence "c \<in> set (blk ! 0 # drop 1 blk)" using blkdec by metis
      moreover have "blk ! 0 = (entry M 0 j0, entry M 1 j0)"
        using blknth[OF L0] pairM by simp
      ultimately show "snd c = entry M 1 j0 \<or> c \<in> set blktail"
        unfolding bt_blk by auto
    qed
    have dropj0M: "drop (Suc j0) M = blktail @ [M ! j1]"
    proof -
      have Mdec: "M = take j1 M @ [M ! j1]"
      proof -
        have "drop j1 M = M ! j1 # drop (Suc j1) M"
          using j1len by (rule Cons_nth_drop_Suc[symmetric])
        moreover have "drop (Suc j1) M = []" using lenM by simp
        ultimately have "drop j1 M = [M ! j1]" by simp
        thus ?thesis by (metis append_take_drop_id)
      qed
      have "drop (Suc j0) M = drop (Suc j0) (take j1 M)
          @ drop (Suc j0 - length (take j1 M)) [M ! j1]"
        by (subst Mdec) (rule drop_append)
      thus ?thesis unfolding blktail_def using j0j1 j1len by simp
    qed
    have dropbY: "K1 = blktail @ concat (map cp [1..<m])"
    proof -
      have "K1 = drop (Suc j0 - length (take j0 M)) (concat (map cp [0..<m]))"
        unfolding K1_def beq Yd'
        by (subst drop_append) (use j0j1 j1len in simp)
      also have "\<dots> = drop 1 (concat (map cp [0..<m]))"
        using j0j1 j1len by simp
      also have "concat (map cp [0..<m]) = blk @ concat (map cp [1..<m])"
      proof -
        have "[0..<m] = 0 # [1..<m]" using m1le by (simp add: upt_conv_Cons)
        thus ?thesis using cp0 by simp
      qed
      also have "drop 1 (blk @ concat (map cp [1..<m]))
          = blktail @ concat (map cp [1..<m])"
        unfolding bt_blk using lenblk L0 by (simp add: drop_append)
      finally show ?thesis .
    qed
    have lenK: "length K = b - Suc a" unfolding K_def using bdef by simp
    have Kel: "\<And>t. t < b - Suc a \<Longrightarrow> K ! t = M ! (Suc a + t) \<and> fst (M ! a) < fst (K ! t)"
    proof -
      fix t assume tb: "t < b - Suc a"
      have tK: "t < length (mrun Y a)" using tb bdef by simp
      have tw: "K ! t = drop (Suc a) Y ! t"
        using tK unfolding K_def mrun_def by (rule takeWhile_nth)
      have "drop (Suc a) Y ! t = Y ! (Suc a + t)"
        using aY by (intro nth_drop) simp
      moreover have "Suc a + t < j0" using tb beq by simp
      ultimately have e: "K ! t = M ! (Suc a + t)" using tw npre by simp
      have "K ! t \<in> set K" using tb lenK by simp
      hence "fst (Y ! a) < fst (K ! t)"
        unfolding K_def mrun_def using set_takeWhileD by metis
      thus "K ! t = M ! (Suc a + t) \<and> fst (M ! a) < fst (K ! t)"
        using e Ya by simp
    qed
    have Mb: "M ! j0 = Y ! b" unfolding beq Yj0 using pairM by simp
    have mrMa: "mrun M a = K"
    proof -
      have bM: "b < length M" using beq j0j1 j1len by simp
      have Keq: "K = take (b - Suc a) (drop (Suc a) M)"
      proof (rule nth_equalityI)
        show "length K = length (take (b - Suc a) (drop (Suc a) M))"
          using lenK bM by simp
      next
        fix t assume "t < length K"
        hence tb: "t < b - Suc a" using lenK by simp
        show "K ! t = take (b - Suc a) (drop (Suc a) M) ! t"
          using Kel[OF tb] tb bM by simp
      qed
      have dsplit: "drop (Suc a) M = K @ M ! b # drop (Suc b) M"
      proof -
        have "drop (Suc a) M = take (b - Suc a) (drop (Suc a) M)
            @ drop (b - Suc a) (drop (Suc a) M)"
          by (rule append_take_drop_id[symmetric])
        moreover have "drop (b - Suc a) (drop (Suc a) M) = drop b M"
          using ab by (simp add: drop_drop)
        moreover have "drop b M = M ! b # drop (Suc b) M"
          using bM by (rule Cons_nth_drop_Suc[symmetric])
        ultimately show ?thesis using Keq by metis
      qed
      have allK: "\<forall>x \<in> set K. fst (M ! a) < fst x"
      proof
        fix x assume "x \<in> set K"
        then obtain t where tt: "t < length K" "x = K ! t" by (metis in_set_conv_nth)
        have tb2: "t < b - Suc a" using tt(1) lenK by simp
        have "fst (M ! a) < fst (K ! t)" using Kel[OF tb2] by blast
        thus "fst (M ! a) < fst x" using tt(2) by simp
      qed
      have "takeWhile (\<lambda>r. fst (M ! a) < fst r) (drop (Suc a) M)
          = K @ takeWhile (\<lambda>r. fst (M ! a) < fst r) (M ! b # drop (Suc b) M)"
        unfolding dsplit by (rule takeWhile_append2) (use allK in blast)
      moreover have "takeWhile (\<lambda>r. fst (M ! a) < fst r) (M ! b # drop (Suc b) M) = []"
      proof -
        have "fst (M ! b) = fst (M ! a)"
          using fb Ya Mb unfolding beq by simp
        thus ?thesis by simp
      qed
      ultimately show ?thesis unfolding mrun_def by simp
    qed
    have coreM: "sibrel K (blktail @ [M ! j1])"
    proof -
      have aM: "a < length M" using aj0 j0j1 j1len by simp
      have bM: "b < length M" using beq j0j1 j1len by simp
      have posM: "0 < fst (M ! a)" using pos Ya by simp
      have bdefM: "b = Suc a + length (mrun M a)" using bdef mrMa K_def by simp
      have fbM: "fst (M ! b) = fst (M ! a)" using fb Ya Mb unfolding beq by simp
      have sbM: "snd (M ! b) = snd (M ! a)" using sb Ya Mb unfolding beq by simp
      have obMj0: "\<forall>x \<in> set (drop (Suc j0) M). fst (M ! j0) < fst x"
      proof
        fix x assume "x \<in> set (drop (Suc j0) M)"
        then obtain t where t: "t < length M - Suc j0" "x = drop (Suc j0) M ! t"
          by (metis in_set_conv_nth length_drop)
        have xi: "x = M ! (Suc j0 + t)"
        proof -
          have "drop (Suc j0) M ! t = M ! (Suc j0 + t)"
            by (intro nth_drop) (use j0j1 j1len in simp)
          thus ?thesis using t(2) by simp
        qed
        have "entry M 0 j0 < entry M 0 (Suc j0 + t)"
          using hm0 t(1) lenM by simp
        thus "fst (M ! j0) < fst x" using xi unfolding entry_def by simp
      qed
      have mrMb: "mrun M b = blktail @ [M ! j1]"
      proof -
        have "mrun M b = drop (Suc j0) M"
          unfolding mrun_def beq using obMj0 by (simp add: takeWhile_eq_all_conv)
        thus ?thesis unfolding dropj0M .
      qed
      show ?thesis
        using R[unfolded sibm2_def, rule_format, OF aM posM bdefM bM fbM sbM]
        unfolding mrMa mrMb .
    qed
    have mrYb: "mrun Y b = K1"
      unfolding mrun_def K1_def using ob by (simp add: takeWhile_eq_all_conv)
    have SYf: "sibrel K K1"
      using SY[unfolded sibm2_def, rule_format, OF aY pos bdef bY fb sb]
      unfolding K_def mrYb .
    define xx where "xx = (entry M 0 j0 + d0, entry M 1 j0)"
    have neasc: "M ! j1 \<noteq> xx \<and>
        \<not> (fst (M ! j1) < fst xx
           \<or> (fst (M ! j1) = fst xx \<and> snd (M ! j1) < snd xx))"
    proof -
      have Mj1: "M ! j1 = (entry M 0 j1, entry M 1 j1)" using pairM by simp
      have "fst xx = entry M 0 j1" unfolding xx_def using d0ex by simp
      thus ?thesis using e1j Mj1 unfolding xx_def by simp
    qed
    have cp1x: "1 < m \<Longrightarrow> cp 1 = xx # tl (cp 1)"
    proof -
      assume "1 < m"
      have "cp 1 ! 0 = xx" using cpnth[OF L0] unfolding xx_def by simp
      moreover have "cp 1 \<noteq> []" unfolding cp_def using j0j1 by simp
      ultimately show "cp 1 = xx # tl (cp 1)" by (metis hd_conv_nth list.exhaust_sel)
    qed
    have cdec2: "1 < m \<Longrightarrow> concat (map cp [1..<m]) = cp 1 @ concat (map cp [Suc 1..<m])"
    proof -
      assume "1 < m"
      hence "[1..<m] = 1 # [Suc 1..<m]" by (simp add: upt_conv_Cons)
      thus ?thesis by simp
    qed
    have main: "sibrel K (K1 @ C)"
    proof -
      from SYf consider (eqf) "K1 = K"
        | (pref) D where "D \<noteq> []" "K = K1 @ D"
        | (lxf) p x x1 r r1 where "K = p @ x # r" "K1 = p @ x1 # r1"
            "fst x1 < fst x \<or> (fst x1 = fst x \<and> snd x1 < snd x)"
        unfolding sibrel_def by blast
      thus ?thesis
      proof cases
        case eqf
        show ?thesis
        proof (cases "1 < m")
          case False
          hence meq: "m = 1" using m1le by simp
          have K1bt: "K1 = blktail" using dropbY unfolding meq by simp
          have "blktail @ [M ! j1] = K @ [M ! j1]" using eqf K1bt by simp
          hence False using sibrel_nopref[OF coreM] by blast
          thus ?thesis ..
        next
          case True
          have Kdec: "K = blktail @ xx # (tl (cp 1) @ concat (map cp [Suc 1..<m]))"
            using eqf[symmetric] dropbY cdec2[OF True] cp1x[OF True] by simp
          have K1Mdec: "blktail @ [M ! j1] = blktail @ M ! j1 # []" by simp
          have False
            using sibrel_ascent[OF coreM Kdec K1Mdec] neasc by blast
          thus ?thesis ..
        qed
      next
        case pref
        show ?thesis
        proof (cases "1 < m")
          case False
          hence meq: "m = 1" using m1le by simp
          show ?thesis
            using seam_copyhead_m1[OF R B ST j1d j1nz i1d hp j0d d0d Yd SY
                aY pos bdef bY fb sb ob high beq meq
                pref(2)[unfolded K_def K1_def] pref(1)]
            unfolding K_def K1_def C_def cp_def by simp
        next
          case True
          have Kdec: "K = blktail @ xx # (tl (cp 1) @ concat (map cp [Suc 1..<m]) @ D)"
            using pref(2) dropbY cdec2[OF True] cp1x[OF True] by simp
          have K1Mdec: "blktail @ [M ! j1] = blktail @ M ! j1 # []" by simp
          have False
            using sibrel_ascent[OF coreM Kdec K1Mdec] neasc by blast
          thus ?thesis ..
        qed
      next
        case lxf
        have ext: "K1 @ C = p @ x1 # (r1 @ C)" unfolding lxf(2) by simp
        have "K = p @ x # r \<and> K1 @ C = p @ x1 # (r1 @ C)
              \<and> (fst x1 < fst x \<or> (fst x1 = fst x \<and> snd x1 < snd x))"
          using lxf(1) ext lxf(3) by blast
        thus ?thesis unfolding sibrel_def by blast
      qed
    qed
    show ?thesis using main unfolding K_def K1_def mapC by simp
  qed
qed

text \<open>(seam, prefix-head assembly) The complete open-extension analysis for
  ties headed in the prefix: equal family refuted (\<open>seam_E_refute\<close>), prefix
  family closed for \<open>m = 0\<close> by the three-way split of the base-sequence fact
  and refuted for \<open>m \<ge> 2\<close> by the ascent clash, lexdiff family extended in
  place with head-maximality carried by the row-1 sets of the copies.\<close>

lemma seam_open_blift:
  assumes R: "sibm2 M" and B: "blockok 0 M" and ST: "M \<in> ST_PS"
    and j1d: "j1 = Lng M - 1" and j1nz: "j1 \<noteq> 0"
    and i1d: "i1 = idx1 M j1" and hp: "hasParent M i1 j1"
    and j0d: "j0 = parent M i1 j1"
    and d0d: "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
    and Yd: "Y = take j0 M @ concat (map (\<lambda>k.
           map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j)) [j0..<j1]) [0..<m])"
    and SY: "sibm2 Y"
    and aY: "a < length Y" and pos: "0 < fst (Y ! a)"
    and bdef: "b = Suc a + length (mrun Y a)" and bY: "b < length Y"
    and fb: "fst (Y ! b) = fst (Y ! a)" and sb: "snd (Y ! b) = snd (Y ! a)"
    and ob: "\<forall>x \<in> set (drop (Suc b) Y). fst (Y ! b) < fst x"
    and high: "fst (Y ! b) < entry M 0 j0 + m * d0"
    and bj0: "b < j0"
  shows "sibrel (mrun Y a) (drop (Suc b) Y
           @ map (\<lambda>j. (entry M 0 j + m * d0, entry M 1 j)) [j0..<j1])"
proof -
  define cp where "cp = (\<lambda>k. map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j)) [j0..<j1])"
  define C where "C = cp m"
  define K where "K = mrun Y a"
  define K1 where "K1 = drop (Suc b) Y"
  have mapC: "map (\<lambda>j. (entry M 0 j + m * d0, entry M 1 j)) [j0..<j1] = C"
    unfolding C_def cp_def ..
  have Yd': "Y = take j0 M @ concat (map cp [0..<m])"
    unfolding cp_def by (rule Yd)
  have nR: "nextR M i1 j0 j1" unfolding j0d by (rule parent_nextR[OF hp])
  have j0j1: "j0 < j1" using nR by (rule nextR_less)
  have lenM: "length M = Suc j1" using j1d j1nz by (cases M) auto
  have j1len: "j1 < length M" using lenM by simp
  define L where "L = j1 - j0"
  have L0: "0 < L" unfolding L_def using j0j1 by simp
  have npre: "\<And>i. i < j0 \<Longrightarrow> Y ! i = M ! i"
    using oper_bad_nth_pre[OF Yd _ j1len j0j1] by blast
  have hm0: "\<forall>k. j0 < k \<and> k \<le> j1 \<longrightarrow> entry M 0 j0 < entry M 0 k"
    by (rule block_head_min[OF hp j0d])
  have pairM: "\<And>j. (entry M 0 j, entry M 1 j) = M ! j"
    unfolding entry_def by simp
  have ab: "a < b" using bdef by linarith
  have aj0: "a < j0" using ab bj0 by simp
  have Yb: "Y ! b = M ! b" by (rule npre[OF bj0])
  have Ya: "Y ! a = M ! a" by (rule npre[OF aj0])
  define blk where "blk = drop j0 (take j1 M)"
  have lenblk: "length blk = L" unfolding blk_def L_def using j1len by simp
  have blkne: "blk \<noteq> []" using lenblk L0 by auto
  have blknth: "\<And>q. q < L \<Longrightarrow> blk ! q = M ! (j0 + q)"
    unfolding blk_def L_def using j1len by simp
  have cpnth: "\<And>k q. q < L \<Longrightarrow> cp k ! q = (entry M 0 (j0+q) + k * d0, entry M 1 (j0+q))"
    unfolding cp_def L_def by simp
  have cpk_shf: "\<And>k. cp k = shf (k * d0) blk"
  proof (rule nth_equalityI)
    fix k show "length (cp k) = length (shf (k * d0) blk)"
      using lenblk unfolding L_def by (simp add: cp_def)
  next
    fix k q assume "q < length (cp k)"
    hence qL: "q < L" unfolding cp_def L_def by simp
    have "shf (k * d0) blk ! q = (fst (M ! (j0+q)) + k * d0, snd (M ! (j0+q)))"
      using shf_nth[of q blk "k * d0"] blknth[OF qL] lenblk qL by simp
    thus "cp k ! q = shf (k * d0) blk ! q"
      using cpnth[OF qL] unfolding entry_def by simp
  qed
  have cp0: "cp 0 = blk" using cpk_shf[of 0] by simp
  have sndC: "\<And>c. c \<in> set C \<Longrightarrow> \<exists>c' \<in> set blk. snd c = snd c'"
  proof -
    fix c assume "c \<in> set C"
    hence "c \<in> set (shf (m * d0) blk)" using cpk_shf unfolding C_def by simp
    thus "\<exists>c' \<in> set blk. snd c = snd c'"
      unfolding shf_def by force
  qed
  have dropbM: "drop (Suc b) M = drop (Suc b) (take j0 M) @ blk @ [M ! j1]"
  proof -
    have "drop (Suc b) M = drop (Suc b) (take j0 M @ drop j0 M)" by simp
    also have "\<dots> = drop (Suc b) (take j0 M)
        @ drop (Suc b - length (take j0 M)) (drop j0 M)"
      by (rule drop_append)
    also have "\<dots> = drop (Suc b) (take j0 M) @ drop j0 M"
      using bj0 j1len j0j1 by simp
    also have "drop j0 M = blk @ [M ! j1]"
    proof -
      have Mdec: "M = take j1 M @ [M ! j1]"
      proof -
        have "drop j1 M = M ! j1 # drop (Suc j1) M"
          using j1len by (rule Cons_nth_drop_Suc[symmetric])
        moreover have "drop (Suc j1) M = []" using lenM by simp
        ultimately have "drop j1 M = [M ! j1]" by simp
        thus ?thesis by (metis append_take_drop_id)
      qed
      have "drop j0 M = drop j0 (take j1 M)
          @ drop (j0 - length (take j1 M)) [M ! j1]"
        by (subst Mdec) (rule drop_append)
      thus ?thesis unfolding blk_def using j0j1 j1len by simp
    qed
    finally show ?thesis .
  qed
  define P0 where "P0 = drop (Suc b) (take j0 M)"
  have dropbY: "K1 = P0 @ concat (map cp [0..<m])"
    unfolding Yd' P0_def K1_def
    by (subst drop_append) (use bj0 j1len j0j1 in simp)
  have levlow: "fst (Y ! b) < entry M 0 j0"
  proof (cases m)
    case 0 thus ?thesis using high by simp
  next
    case (Suc km)
    have lenY: "length Y = j0 + m * L"
      unfolding L_def by (rule oper_bad_len[OF Yd j0j1 j1len])
    have j0Y: "j0 < length Y" unfolding lenY Suc using L0 by simp
    have Yj0: "Y ! j0 = (entry M 0 j0, entry M 1 j0)"
      using oper_bad_nth_copy[OF Yd j0j1 j1len, of 0 0] L0 Suc
      unfolding L_def by simp
    have "drop (Suc b) Y ! (j0 - Suc b) \<in> set (drop (Suc b) Y)"
      using bj0 j0Y by (intro nth_mem) simp
    moreover have "drop (Suc b) Y ! (j0 - Suc b) = Y ! j0"
    proof -
      have "drop (Suc b) Y ! (j0 - Suc b) = Y ! (Suc b + (j0 - Suc b))"
        using bY by (intro nth_drop) simp
      thus ?thesis using bj0 by simp
    qed
    ultimately have "fst (Y ! b) < fst (Y ! j0)" using ob by auto
    thus ?thesis using Yj0 by simp
  qed
  have obM: "\<forall>x \<in> set (drop (Suc b) M). fst (M ! b) < fst x"
  proof
    fix x assume "x \<in> set (drop (Suc b) M)"
    then obtain t where t: "t < length M - Suc b" "x = drop (Suc b) M ! t"
      by (metis in_set_conv_nth length_drop)
    have xi: "x = M ! (Suc b + t)"
    proof -
      have "drop (Suc b) M ! t = M ! (Suc b + t)"
        by (intro nth_drop) (use bj0 j0j1 j1len in simp)
      thus ?thesis using t(2) by simp
    qed
    show "fst (M ! b) < fst x"
    proof (cases "Suc b + t < j0")
      case True
      have "M ! (Suc b + t) = Y ! (Suc b + t)" using npre[OF True] by simp
      moreover have "Y ! (Suc b + t) \<in> set (drop (Suc b) Y)"
      proof -
        have lenY: "length Y = j0 + m * L"
          unfolding L_def by (rule oper_bad_len[OF Yd j0j1 j1len])
        have "Suc b + t < length Y" using True lenY by simp
        hence "drop (Suc b) Y ! t = Y ! (Suc b + t)"
          by (intro nth_drop) (use bY in simp_all)
        moreover have "t < length (drop (Suc b) Y)"
          using True lenY by simp
        ultimately show ?thesis by (metis nth_mem)
      qed
      ultimately show ?thesis using ob Yb xi by auto
    next
      case False
      hence ge: "j0 \<le> Suc b + t" by simp
      have le1: "Suc b + t \<le> j1" using t(1) lenM by simp
      show ?thesis
      proof (cases "Suc b + t = j0")
        case True
        thus ?thesis using xi levlow Yb pairM by (metis fst_conv)
      next
        case False
        hence "j0 < Suc b + t" using ge by simp
        hence "entry M 0 j0 < entry M 0 (Suc b + t)" using hm0 le1 by simp
        thus ?thesis using xi levlow Yb unfolding entry_def by simp
      qed
    qed
  qed
  have mrMb: "mrun M b = P0 @ blk @ [M ! j1]"
  proof -
    have "mrun M b = drop (Suc b) M"
      unfolding mrun_def using obM by (simp add: takeWhile_eq_all_conv)
    thus ?thesis unfolding dropbM P0_def .
  qed
  have lenK: "length K = b - Suc a" unfolding K_def using bdef by simp
  have Kel: "\<And>t. t < b - Suc a \<Longrightarrow> K ! t = M ! (Suc a + t) \<and> fst (M ! a) < fst (K ! t)"
  proof -
    fix t assume tb: "t < b - Suc a"
    have tK: "t < length (mrun Y a)" using tb bdef by simp
    have tw: "K ! t = drop (Suc a) Y ! t"
      using tK unfolding K_def mrun_def by (rule takeWhile_nth)
    have "drop (Suc a) Y ! t = Y ! (Suc a + t)"
      using aY by (intro nth_drop) simp
    moreover have "Suc a + t < j0" using tb bj0 by simp
    ultimately have e: "K ! t = M ! (Suc a + t)" using tw npre by simp
    have "K ! t \<in> set K" using tb lenK by simp
    hence "fst (Y ! a) < fst (K ! t)"
      unfolding K_def mrun_def using set_takeWhileD by metis
    thus "K ! t = M ! (Suc a + t) \<and> fst (M ! a) < fst (K ! t)"
      using e Ya by simp
  qed
  have mrMa: "mrun M a = K"
  proof -
    have bM: "b < length M" using bj0 j0j1 j1len by simp
    have Keq: "K = take (b - Suc a) (drop (Suc a) M)"
    proof (rule nth_equalityI)
      show "length K = length (take (b - Suc a) (drop (Suc a) M))"
        using lenK bM by simp
    next
      fix t assume "t < length K"
      hence tb: "t < b - Suc a" using lenK by simp
      show "K ! t = take (b - Suc a) (drop (Suc a) M) ! t"
        using Kel[OF tb] tb bM by simp
    qed
    have dsplit: "drop (Suc a) M = K @ M ! b # drop (Suc b) M"
    proof -
      have "drop (Suc a) M = take (b - Suc a) (drop (Suc a) M)
          @ drop (b - Suc a) (drop (Suc a) M)"
        by (rule append_take_drop_id[symmetric])
      moreover have "drop (b - Suc a) (drop (Suc a) M) = drop b M"
        using ab by (simp add: drop_drop)
      moreover have "drop b M = M ! b # drop (Suc b) M"
        using bM by (rule Cons_nth_drop_Suc[symmetric])
      ultimately show ?thesis using Keq by metis
    qed
    have allK: "\<forall>x \<in> set K. fst (M ! a) < fst x"
    proof
      fix x assume "x \<in> set K"
      then obtain t where tt: "t < length K" "x = K ! t" by (metis in_set_conv_nth)
      have tb2: "t < b - Suc a" using tt(1) lenK by simp
      have "fst (M ! a) < fst (K ! t)" using Kel[OF tb2] by blast
      thus "fst (M ! a) < fst x" using tt(2) by simp
    qed
    have "takeWhile (\<lambda>r. fst (M ! a) < fst r) (drop (Suc a) M)
        = K @ takeWhile (\<lambda>r. fst (M ! a) < fst r) (M ! b # drop (Suc b) M)"
      unfolding dsplit by (rule takeWhile_append2) (use allK in blast)
    moreover have "takeWhile (\<lambda>r. fst (M ! a) < fst r) (M ! b # drop (Suc b) M) = []"
      using fb Ya Yb by simp
    ultimately show ?thesis unfolding mrun_def by simp
  qed
  have coreM: "sibrel K (P0 @ blk @ [M ! j1])"
  proof -
    have aM: "a < length M" using aj0 j0j1 j1len by simp
    have bM: "b < length M" using bj0 j0j1 j1len by simp
    have posM: "0 < fst (M ! a)" using pos Ya by simp
    have bdefM: "b = Suc a + length (mrun M a)" using bdef mrMa K_def by simp
    have fbM: "fst (M ! b) = fst (M ! a)" using fb Ya Yb by simp
    have sbM: "snd (M ! b) = snd (M ! a)" using sb Ya Yb by simp
    show ?thesis
      using R[unfolded sibm2_def, rule_format, OF aM posM bdefM bM fbM sbM]
      unfolding mrMa mrMb .
  qed
  have mrYb: "mrun Y b = K1"
    unfolding mrun_def K1_def using ob by (simp add: takeWhile_eq_all_conv)
  have SYf: "sibrel K K1"
    using SY[unfolded sibm2_def, rule_format, OF aY pos bdef bY fb sb]
    unfolding K_def mrYb .
  have main: "sibrel K (K1 @ C)"
  proof -
    from SYf consider (eqf) "K1 = K"
      | (pref) D where "D \<noteq> []" "K = K1 @ D"
      | (lxf) p x x1 r r1 where "K = p @ x # r" "K1 = p @ x1 # r1"
          "fst x1 < fst x \<or> (fst x1 = fst x \<and> snd x1 < snd x)"
      unfolding sibrel_def by blast
    thus ?thesis
    proof cases
      case eqf
      have "mrun Y a \<noteq> drop (Suc b) Y"
        by (rule seam_E_refute[OF R B ST j1d j1nz i1d hp j0d d0d Yd
              aY pos bdef bY fb sb ob high bj0])
      thus ?thesis using eqf unfolding K_def K1_def by simp
    next
      case pref
      show ?thesis
      proof (cases m)
        case m0: 0
        have K1P0: "K1 = P0" using dropbY unfolding m0 by simp
        have CB: "C = blk" unfolding C_def m0 using cp0 by simp
        from coreM consider (eq2) "K = P0 @ blk @ [M ! j1]"
          | (pre2) D2 where "D2 \<noteq> []" "K = (P0 @ blk @ [M ! j1]) @ D2"
          | (lx2) p x x1 r r1 where "K = p @ x # r" "P0 @ blk @ [M ! j1] = p @ x1 # r1"
              "fst x1 < fst x \<or> (fst x1 = fst x \<and> snd x1 < snd x)"
          unfolding sibrel_def by blast
        thus ?thesis
        proof cases
          case eq2
          have "K = (K1 @ C) @ [M ! j1]" unfolding K1P0 CB using eq2 by simp
          thus ?thesis unfolding sibrel_def by blast
        next
          case pre2
          have "K = (K1 @ C) @ ([M ! j1] @ D2)"
            unfolding K1P0 CB using pre2(2) by simp
          moreover have "[M ! j1] @ D2 \<noteq> []" by simp
          ultimately show ?thesis unfolding sibrel_def by blast
        next
          case lx2
          show ?thesis
          proof (cases "r1 = []")
            case True
            have pe: "P0 @ blk = p \<and> M ! j1 = x1"
            proof -
              have "P0 @ blk @ [M ! j1] = (P0 @ blk) @ [M ! j1]" by simp
              moreover have "p @ x1 # r1 = p @ [x1]" unfolding True by simp
              ultimately show ?thesis
                using lx2(2) by (metis butlast_snoc last_snoc)
            qed
            have "K = (K1 @ C) @ x # r"
              unfolding K1P0 CB using lx2(1) pe by simp
            thus ?thesis unfolding sibrel_def by blast
          next
            case False
            have bl: "P0 @ blk = p @ x1 # butlast r1"
            proof -
              have "butlast (P0 @ blk @ [M ! j1]) = P0 @ blk"
                by (simp add: butlast_append)
              moreover have "butlast (p @ x1 # r1) = p @ x1 # butlast r1"
                using False by (simp add: butlast_append)
              ultimately show ?thesis using lx2(2) by simp
            qed
            show ?thesis
              unfolding sibrel_def K1P0 CB
              using lx2(1) bl lx2(3) by blast
          qed
        qed
      next
        case (Suc km)
        show ?thesis
        proof (cases km)
          case 0
          have m1: "m = 1" using Suc 0 by simp
          show ?thesis
            using seam_open_m1[OF R B ST j1d j1nz i1d hp j0d d0d Yd SY
                aY pos bdef bY fb sb ob high bj0 m1
                pref(2)[unfolded K_def K1_def] pref(1)]
            unfolding K_def K1_def C_def cp_def by simp
        next
          case (Suc kn)
          have m2: "2 \<le> m" using \<open>m = Suc km\<close> Suc by simp
          have cdec: "concat (map cp [0..<m]) = blk @ cp 1 @ concat (map cp [Suc 1..<m])"
          proof -
            have "[0..<m] = 0 # [1..<m]"
              using m2 by (simp add: upt_conv_Cons)
            moreover have "[1..<m] = 1 # [Suc 1..<m]"
              using m2 by (simp add: upt_conv_Cons)
            ultimately show ?thesis using cp0 by simp
          qed
          define x where "x = (entry M 0 j0 + d0, entry M 1 j0)"
          have cp1: "cp 1 = x # tl (cp 1)"
          proof -
            have "cp 1 ! 0 = x" using cpnth[OF L0] unfolding x_def by simp
            moreover have "cp 1 \<noteq> []" unfolding cp_def using j0j1 by simp
            ultimately show ?thesis by (metis hd_conv_nth list.exhaust_sel)
          qed
          have Kdec: "K = (P0 @ blk) @ x # (tl (cp 1) @ concat (map cp [Suc 1..<m]) @ D)"
            using pref(2) dropbY cdec cp1 by simp
          have K1Mdec: "P0 @ blk @ [M ! j1] = (P0 @ blk) @ M ! j1 # []" by simp
          have e0j: "entry M 0 j0 < entry M 0 j1" using hm0 j0j1 by simp
          have Mj1: "M ! j1 = (entry M 0 j1, entry M 1 j1)" using pairM by simp
          have neasc: "M ! j1 \<noteq> x \<and>
              \<not> (fst (M ! j1) < fst x
                 \<or> (fst (M ! j1) = fst x \<and> snd (M ! j1) < snd x))"
          proof (cases "0 < i1")
            case False
            hence "d0 = 0" using d0d by simp
            hence "fst x = entry M 0 j0" unfolding x_def by simp
            thus ?thesis using e0j Mj1 unfolding x_def by simp
          next
            case True
            hence i1one: "i1 = 1" using idx1_le[of M j1] i1d by simp
            have dx: "fst x = entry M 0 j1"
              unfolding x_def using d0d True e0j by simp
            have "nextrel1 M j0 j1" using nR unfolding i1one nextR_def by simp
            hence "entry M 1 j0 < entry M 1 j1" unfolding nextrel1_def by blast
            thus ?thesis using dx Mj1 unfolding x_def by simp
          qed
          show ?thesis
            using sibrel_ascent[OF coreM Kdec K1Mdec] neasc by blast
        qed
      qed
    next
      case lxf
      have ext: "K1 @ C = p @ x1 # (r1 @ C)" unfolding lxf(2) by simp
      have "K = p @ x # r \<and> K1 @ C = p @ x1 # (r1 @ C)
            \<and> (fst x1 < fst x \<or> (fst x1 = fst x \<and> snd x1 < snd x))"
        using lxf(1) ext lxf(3) by blast
      thus ?thesis unfolding sibrel_def by blast
    qed
  qed
  show ?thesis using main unfolding K_def K1_def mapC by simp
qed

text \<open>(seam, open-extension core) When the appended copy's head is still
  above an open tie-sibling run's level, the WHOLE copy joins the run; the
  result stays in \<open>sibrel\<close>.  (Empirically 150 instances at closure
  sampling: equal-family never reaches here, prefix-family extensions land
  in P/F1/F2, head-max is preserved.)\<close>

lemma seam_open_core:
  assumes "sibm2 M" and "blockok 0 M" and "M \<in> ST_PS"
    and "j1 = Lng M - 1" and "j1 \<noteq> 0"
    and "i1 = idx1 M j1" and "hasParent M i1 j1"
    and "j0 = parent M i1 j1"
    and "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
    and "Y = take j0 M @ concat (map (\<lambda>k.
           map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j)) [j0..<j1]) [0..<m])"
    and "sibm2 Y"
    and "a < length Y" and "0 < fst (Y ! a)"
    and "b = Suc a + length (mrun Y a)" and "b < length Y"
    and "fst (Y ! b) = fst (Y ! a)" and "snd (Y ! b) = snd (Y ! a)"
    and "\<forall>x \<in> set (drop (Suc b) Y). fst (Y ! b) < fst x"
    and "fst (Y ! b) < entry M 0 j0 + m * d0"
  shows "sibrel (mrun Y a) (drop (Suc b) Y
           @ map (\<lambda>j. (entry M 0 j + m * d0, entry M 1 j)) [j0..<j1])"
proof (cases "b < j0")
  case True
  show ?thesis
    by (rule seam_open_blift[OF assms(1) assms(2) assms(3) assms(4) assms(5)
          assms(6) assms(7) assms(8) assms(9) assms(10) assms(11) assms(12)
          assms(13) assms(14) assms(15) assms(16) assms(17) assms(18)
          assms(19) True])
next
  case False
  hence ge: "j0 \<le> b" by simp
  show ?thesis
    by (rule seam_open_copyhead[OF assms(1) assms(2) assms(3) assms(4) assms(5)
          assms(6) assms(7) assms(8) assms(9) assms(10) assms(11) assms(12)
          assms(13) assms(14) assms(15) assms(16) assms(17) assms(18)
          assms(19) ge])
qed

lemma seam_I_open:
  assumes R: "sibm2 M" and B: "blockok 0 M" and ST: "M \<in> ST_PS"
    and j1d: "j1 = Lng M - 1" and j1nz: "j1 \<noteq> 0"
    and i1d: "i1 = idx1 M j1" and hp: "hasParent M i1 j1"
    and j0d: "j0 = parent M i1 j1"
    and d0d: "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
    and Yd: "Y = take j0 M @ concat (map (\<lambda>k.
           map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j)) [j0..<j1]) [0..<m])"
    and SY: "sibm2 Y"
    and aY: "a < length Y" and pos: "0 < fst (Y ! a)"
    and bdef: "b = Suc a + length (mrun Y a)" and bY: "b < length Y"
    and fb: "fst (Y ! b) = fst (Y ! a)" and sb: "snd (Y ! b) = snd (Y ! a)"
    and ob: "\<forall>x \<in> set (drop (Suc b) Y). fst (Y ! b) < fst x"
  shows "sibrel (mrun Y a) (drop (Suc b) Y @ takeWhile (\<lambda>r. fst (Y ! b) < fst r)
           (map (\<lambda>j. (entry M 0 j + m * d0, entry M 1 j)) [j0..<j1]))"
proof -
  define C where "C = map (\<lambda>j. (entry M 0 j + m * d0, entry M 1 j)) [j0..<j1]"
  have nR: "nextR M i1 j0 j1" unfolding j0d by (rule parent_nextR[OF hp])
  have j0j1: "j0 < j1" using nR by (rule nextR_less)
  define L where "L = j1 - j0"
  have L0: "0 < L" unfolding L_def using j0j1 by simp
  have lenC: "length C = L" unfolding C_def L_def by simp
  have Cnth: "\<And>q. q < L \<Longrightarrow> C ! q = (entry M 0 (j0+q) + m * d0, entry M 1 (j0+q))"
    unfolding C_def L_def by simp
  have hm0: "\<forall>k. j0 < k \<and> k \<le> j1 \<longrightarrow> entry M 0 j0 < entry M 0 k"
    by (rule block_head_min[OF hp j0d])
  have mrYb: "mrun Y b = drop (Suc b) Y"
    unfolding mrun_def using ob by (simp add: takeWhile_eq_all_conv)
  show ?thesis
  proof (cases "fst (Y ! b) < entry M 0 j0 + m * d0")
    case high: True
    have tw: "takeWhile (\<lambda>r. fst (Y ! b) < fst r) C = C"
    proof (rule takeWhile_eq_all_conv[THEN iffD2], intro ballI)
      fix x assume "x \<in> set C"
      then obtain q where q: "q < L" "x = C ! q"
        using lenC by (metis in_set_conv_nth)
      show "fst (Y ! b) < fst x"
      proof (cases "q = 0")
        case True
        thus ?thesis using q Cnth[OF L0] high by simp
      next
        case False
        have "entry M 0 j0 < entry M 0 (j0 + q)"
          using hm0 False q(1) unfolding L_def by simp
        thus ?thesis using q Cnth[OF q(1)] high by simp
      qed
    qed
    show ?thesis
      unfolding C_def[symmetric] tw
      by (rule seam_open_core[OF R B ST j1d j1nz i1d hp j0d d0d Yd SY
            aY pos bdef bY fb sb ob high, folded C_def])
  next
    case low: False
    have Cne: "C \<noteq> []" using lenC L0 by auto
    have hdC: "hd C = (entry M 0 j0 + m * d0, entry M 1 j0)"
      using Cnth[OF L0] Cne by (simp add: hd_conv_nth)
    have tw: "takeWhile (\<lambda>r. fst (Y ! b) < fst r) C = []"
      using low hdC Cne by (cases C) auto
    have "sibrel (mrun Y a) (mrun Y b)"
      by (rule SY[unfolded sibm2_def, rule_format, OF aY pos bdef bY fb sb])
    thus ?thesis
      unfolding C_def[symmetric] tw mrYb[symmetric] by simp
  qed
qed

text \<open>(seam, climb-tie refutation core) In the \<open>i1 = 1\<close> block, a column at
  the level of \<open>j1\<close> whose tail is clear up to \<open>j1\<close> carries at least the
  row-1 value of \<open>j1\<close> (empirically exactly equal, 265/265; together with
  \<open>entry M 1 j0 < entry M 1 j1\<close> this refutes the cross-seam tie for
  \<open>d0 > 0\<close>).  Same value-side lower-bound family as \<open>r1ok_climb\<close>.\<close>

lemma CFGA_r1:
  assumes ST: "M \<in> ST_PS"
    and j1d: "j1 = Lng M - 1" and j1nz: "j1 \<noteq> 0"
    and i1d: "idx1 M j1 = 1" and hp: "hasParent M 1 j1"
    and j0d: "j0 = parent M 1 j1"
    and j0jq: "j0 < jq" and jqj1: "jq < j1"
    and e0q: "entry M 0 jq = entry M 0 j1"
    and tcl: "\<forall>l. jq < l \<and> l < j1 \<longrightarrow> entry M 0 j1 < entry M 0 l"
  shows "entry M 1 j1 \<le> entry M 1 jq"
proof -
  have lenM: "length M = Suc j1" using j1d j1nz by (cases M) auto
  have jqM: "jq < length M" using jqj1 lenM by simp
  have j1M: "j1 < length M" using lenM by simp
  define W where "W = {w. w < jq \<and> entry M 0 w < entry M 0 jq}"
  have finW: "finite W" unfolding W_def by simp
  have j0W: "j0 \<in> W"
  proof -
    have "entry M 0 j0 < entry M 0 jq"
      using block_head_min[OF hp j0d] j0jq jqj1 by simp
    thus ?thesis unfolding W_def using j0jq by simp
  qed
  define w0 where "w0 = Max W"
  have w0W: "w0 \<in> W" unfolding w0_def using finW j0W by (intro Max_in) auto
  have w0jq: "w0 < jq" and w0lev: "entry M 0 w0 < entry M 0 jq"
    using w0W unfolding W_def by auto
  have w0max: "\<And>p. w0 < p \<Longrightarrow> p < jq \<Longrightarrow> entry M 0 jq \<le> entry M 0 p"
  proof -
    fix p assume pw: "w0 < p" and pjq: "p < jq"
    show "entry M 0 jq \<le> entry M 0 p"
    proof (rule ccontr)
      assume "\<not> entry M 0 jq \<le> entry M 0 p"
      hence "p \<in> W" unfolding W_def using pjq by simp
      hence "p \<le> w0" unfolding w0_def using finW by simp
      thus False using pw by simp
    qed
  qed
  define mid where "mid = take (jq - Suc w0) (drop (Suc w0) M)"
  define rest where "rest = drop (Suc jq) M"
  have w0M: "w0 < length M" using w0jq jqM by simp
  have midnth: "\<And>t. t < jq - Suc w0 \<Longrightarrow> mid ! t = M ! (Suc w0 + t)"
    unfolding mid_def using w0jq jqM by simp
  have lenmid: "length mid = jq - Suc w0"
    unfolding mid_def using w0jq jqM by simp
  have Mdec: "M = take w0 M @ M ! w0 # mid @ (M ! jq # rest)"
  proof -
    have d1: "M = take w0 M @ M ! w0 # drop (Suc w0) M"
      using id_take_nth_drop[OF w0M] by simp
    have iq: "jq - Suc w0 < length (drop (Suc w0) M)"
      using w0jq jqM by simp
    have nq: "drop (Suc w0) M ! (jq - Suc w0) = M ! jq"
      using w0jq jqM by simp
    have ar: "Suc (jq - Suc w0) + Suc w0 = Suc jq"
      using w0jq by linarith
    have d3: "drop (Suc (jq - Suc w0)) (drop (Suc w0) M) = drop (Suc jq) M"
      unfolding drop_drop ar ..
    have d2: "drop (Suc w0) M
        = mid @ drop (Suc w0) M ! (jq - Suc w0) # drop (Suc (jq - Suc w0)) (drop (Suc w0) M)"
      unfolding mid_def by (rule id_take_nth_drop[OF iq])
    have "drop (Suc w0) M = mid @ M ! jq # drop (Suc jq) M"
      using d2 unfolding nq d3 .
    thus ?thesis using d1 unfolding rest_def by metis
  qed
  have restnth: "\<And>t. t < j1 - jq \<Longrightarrow> rest ! t = M ! (Suc jq + t)"
    unfolding rest_def using jqM lenM by simp
  have lenrest: "length rest = j1 - jq"
    unfolding rest_def using lenM by simp
  have fbA: "fbseg (snd (M ! w0)) (M ! jq # rest)"
    unfolding fbseg_def
  proof (intro conjI exI)
    show "M ! jq # rest \<noteq> []" by simp
    show "take w0 M @ (M ! w0 # mid @ (M ! jq # rest)) @ [] \<in> ST_PS"
      using ST Mdec by (metis append_Nil2 append_Cons append_assoc)
    show "snd (M ! w0) = snd (M ! w0)" ..
    show "\<forall>r \<in> set mid. fst (hd (M ! jq # rest)) \<le> fst r"
    proof
      fix r assume "r \<in> set mid"
      then obtain t where t: "t < jq - Suc w0" "r = mid ! t"
        using lenmid by (metis in_set_conv_nth)
      have h1: "Suc w0 + t < jq" using t(1) by linarith
      have "entry M 0 jq \<le> entry M 0 (Suc w0 + t)"
        using w0max[of "Suc w0 + t"] h1 by simp
      thus "fst (hd (M ! jq # rest)) \<le> fst r"
        using midnth[OF t(1)] t(2) unfolding entry_def by simp
    qed
    show "\<forall>r \<in> set (mid @ (M ! jq # rest)). fst (M ! w0) < fst r"
    proof
      fix r assume "r \<in> set (mid @ (M ! jq # rest))"
      then consider (m) "r \<in> set mid" | (c) "r = M ! jq" | (rr) "r \<in> set rest"
        by auto
      thus "fst (M ! w0) < fst r"
      proof cases
        case m
        then obtain t where t: "t < jq - Suc w0" "r = mid ! t"
          using lenmid by (metis in_set_conv_nth)
        have h1: "Suc w0 + t < jq" using t(1) by linarith
        have "entry M 0 w0 < entry M 0 (Suc w0 + t)"
          using w0max[of "Suc w0 + t"] h1 w0lev by simp
        thus ?thesis using midnth[OF t(1)] t(2) unfolding entry_def by simp
      next
        case c
        thus ?thesis using w0lev unfolding entry_def by simp
      next
        case rr
        then obtain t where t: "t < j1 - jq" "r = rest ! t"
          using lenrest by (metis in_set_conv_nth)
        have "entry M 0 j1 \<le> entry M 0 (Suc jq + t)"
        proof (cases "Suc jq + t = j1")
          case True thus ?thesis by simp
        next
          case False
          hence lt: "Suc jq + t < j1" using t(1) by simp
          have "entry M 0 j1 < entry M 0 (Suc jq + t)"
            using tcl[rule_format, of "Suc jq + t"] lt by simp
          thus ?thesis by simp
        qed
        hence "entry M 0 w0 < entry M 0 (Suc jq + t)"
          using w0lev e0q by simp
        thus ?thesis using restnth[OF t(1)] t(2) unfolding entry_def by simp
      qed
    qed
  qed
  have restsplit: "rest = take (j1 - Suc jq) rest @ [M ! j1]"
  proof -
    have "rest = take (j1 - Suc jq) rest @ drop (j1 - Suc jq) rest" by simp
    moreover have "drop (j1 - Suc jq) rest = [M ! j1]"
    proof -
      have "drop (j1 - Suc jq) rest = drop (j1 - Suc jq) (drop (Suc jq) M)"
        unfolding rest_def ..
      also have "\<dots> = drop j1 M" using jqj1 by (simp add: drop_drop)
      also have "\<dots> = M ! j1 # drop (Suc j1) M"
        by (rule Cons_nth_drop_Suc[symmetric, OF j1M])
      also have "drop (Suc j1) M = []" using lenM by simp
      finally show ?thesis by simp
    qed
    ultimately show ?thesis by simp
  qed
  have Tsplit: "dropWhile (\<lambda>r. fst (M ! jq) < fst r) rest = M ! j1 # []"
  proof -
    have allpre: "\<forall>x \<in> set (take (j1 - Suc jq) rest). fst (M ! jq) < fst x"
    proof
      fix x assume "x \<in> set (take (j1 - Suc jq) rest)"
      then obtain t where t1: "t < length (take (j1 - Suc jq) rest)"
        and t2: "x = take (j1 - Suc jq) rest ! t"
        by (metis in_set_conv_nth)
      have tn: "t < j1 - Suc jq" using t1 by simp
      have xe: "x = rest ! t" using t2 tn by simp
      have lt: "Suc jq + t < j1" using tn by linarith
      have "entry M 0 j1 < entry M 0 (Suc jq + t)"
        using tcl[rule_format, of "Suc jq + t"] lt by simp
      hence "entry M 0 jq < entry M 0 (Suc jq + t)" using e0q by simp
      moreover have "t < j1 - jq" using tn by linarith
      ultimately show "fst (M ! jq) < fst x"
        using restnth[of t] xe unfolding entry_def by simp
    qed
    have "dropWhile (\<lambda>r. fst (M ! jq) < fst r) rest
        = dropWhile (\<lambda>r. fst (M ! jq) < fst r) [M ! j1]"
      by (subst restsplit) (rule dropWhile_append2[OF allpre[rule_format]])
    also have "\<dots> = [M ! j1]"
      using e0q unfolding entry_def by simp
    finally show ?thesis by simp
  qed
  have F: "fst (M ! j1) = fst (M ! jq)"
    using e0q unfolding entry_def by simp
  have "snd (M ! j1) \<le> snd (M ! jq)"
    by (rule NT_dom_sub_eq[OF fbA Tsplit F])
  thus ?thesis unfolding entry_def by simp
qed

text \<open>The seam step: appending one more shifted copy of the block preserves
  the sibling-run invariant.  (The whole bad-branch preservation reduces to
  this by induction on the copy count; the base \<open>m = 0\<close> is \<open>sibm2_take\<close>.)\<close>

lemma sibm2_snoc_copy:
  assumes R: "sibm2 M" and B: "blockok 0 M" and ST: "M \<in> ST_PS"
    and j1d: "j1 = Lng M - 1" and j1nz: "j1 \<noteq> 0"
    and i1d: "i1 = idx1 M j1" and hp: "hasParent M i1 j1"
    and j0d: "j0 = parent M i1 j1"
    and d0d: "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
    and Sm: "sibm2 (take j0 M @ concat (map (\<lambda>k.
           map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j)) [j0..<j1]) [0..<m]))"
  shows "sibm2 (take j0 M @ concat (map (\<lambda>k.
           map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j)) [j0..<j1]) [0..<Suc m]))"
proof -
  define cp where "cp = (\<lambda>k. map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j)) [j0..<j1])"
  define Y where "Y = take j0 M @ concat (map cp [0..<m])"
  define C where "C = cp m"
  have Yeq: "Y = take j0 M @ concat (map (\<lambda>k.
        map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j)) [j0..<j1]) [0..<m])"
    unfolding Y_def cp_def ..
  have SY: "sibm2 Y" using Sm unfolding Yeq[symmetric] .
  have nR: "nextR M i1 j0 j1" unfolding j0d by (rule parent_nextR[OF hp])
  have j0j1: "j0 < j1" using nR by (rule nextR_less)
  have j1len: "j1 < length M" using j1d j1nz by (cases M) auto
  define L where "L = j1 - j0"
  have L0: "0 < L" unfolding L_def using j0j1 by simp
  have lenY: "length Y = j0 + m * L"
    unfolding L_def by (rule oper_bad_len[OF Yeq j0j1 j1len])
  have lenC: "length C = L"
    unfolding C_def cp_def L_def by simp
  have hm0: "\<forall>k. j0 < k \<and> k \<le> j1 \<longrightarrow> entry M 0 j0 < entry M 0 k"
    by (rule block_head_min[OF hp j0d])
  have pairM: "\<And>j. (entry M 0 j, entry M 1 j) = M ! j"
    unfolding entry_def by simp
  define blk where "blk = drop j0 (take j1 M)"
  have lenblk: "length blk = L"
    unfolding blk_def L_def using j1len by simp
  have blknth: "\<And>q. q < L \<Longrightarrow> blk ! q = M ! (j0 + q)"
    unfolding blk_def L_def using j1len by simp
  have cpnth: "\<And>k q. q < L \<Longrightarrow> cp k ! q = (entry M 0 (j0+q) + k * d0, entry M 1 (j0+q))"
    unfolding cp_def L_def by simp
  have Ceq: "C = shf (m * d0) blk"
  proof (rule nth_equalityI)
    show "length C = length (shf (m * d0) blk)" using lenC lenblk by simp
  next
    fix q assume "q < length C"
    hence qL: "q < L" using lenC by simp
    have "C ! q = (entry M 0 (j0+q) + m * d0, entry M 1 (j0+q))"
      unfolding C_def by (rule cpnth[OF qL])
    moreover have "shf (m * d0) blk ! q
        = (fst (M ! (j0+q)) + m * d0, snd (M ! (j0+q)))"
      using shf_nth[of q blk "m * d0"] blknth[OF qL] lenblk qL by simp
    ultimately show "C ! q = shf (m * d0) blk ! q"
      unfolding entry_def by simp
  qed
  have npre: "\<And>i. i < j0 \<Longrightarrow> Y ! i = M ! i"
    using oper_bad_nth_pre[OF Yeq _ j1len j0j1] by blast
  have ncopy: "\<And>k q. k < m \<Longrightarrow> q < L \<Longrightarrow>
        Y ! (j0 + (k * L + q)) = (entry M 0 (j0 + q) + k * d0, entry M 1 (j0 + q))"
    unfolding L_def using oper_bad_nth_copy[OF Yeq j0j1 j1len] by blast
  have main: "sibm2 (Y @ C)"
    unfolding sibm2_def
  proof (intro allI impI)
    fix a b
    assume aL: "a < length (Y @ C)" and pos: "0 < fst ((Y @ C) ! a)"
      and bdef: "b = Suc a + length (mrun (Y @ C) a)" and bL: "b < length (Y @ C)"
      and fb: "fst ((Y @ C) ! b) = fst ((Y @ C) ! a)"
      and sb: "snd ((Y @ C) ! b) = snd ((Y @ C) ! a)"
    have ab: "a < b" using bdef by linarith
    have runelem: "\<And>p. a < p \<Longrightarrow> p < b \<Longrightarrow> fst ((Y @ C) ! a) < fst ((Y @ C) ! p)"
    proof -
      fix p assume ap: "a < p" and pb: "p < b"
      have pi: "p - Suc a < length (mrun (Y @ C) a)" using ap pb bdef by linarith
      have "mrun (Y @ C) a ! (p - Suc a) \<in> set (mrun (Y @ C) a)"
        using pi by simp
      hence P: "fst ((Y @ C) ! a) < fst (mrun (Y @ C) a ! (p - Suc a))"
        unfolding mrun_def using set_takeWhileD by metis
      have "mrun (Y @ C) a ! (p - Suc a) = drop (Suc a) (Y @ C) ! (p - Suc a)"
        using pi unfolding mrun_def by (rule takeWhile_nth)
      also have "\<dots> = (Y @ C) ! (Suc a + (p - Suc a))"
        using aL by (intro nth_drop) simp
      also have "\<dots> = (Y @ C) ! p" using ap by simp
      finally show "fst ((Y @ C) ! a) < fst ((Y @ C) ! p)" using P by simp
    qed
    show "sibrel (mrun (Y @ C) a) (mrun (Y @ C) b)"
    proof (cases "a < length Y")
      case aY: True
      have na: "(Y @ C) ! a = Y ! a" using aY by (simp add: nth_append)
      show ?thesis
      proof (cases "b < length Y")
        case bY: True
        have nb: "(Y @ C) ! b = Y ! b" using bY by (simp add: nth_append)
        have mra: "mrun (Y @ C) a = mrun Y a"
        proof (cases "\<forall>x \<in> set (drop (Suc a) Y). fst (Y ! a) < fst x")
          case True
          have "mrun (Y @ C) a = drop (Suc a) Y @ takeWhile (\<lambda>r. fst (Y ! a) < fst r) C"
            unfolding mrun_append[OF aY] if_P[OF True] ..
          hence "length Y - Suc a \<le> length (mrun (Y @ C) a)" by simp
          hence "length Y \<le> b" using bdef aY by linarith
          hence False using bY by simp
          thus ?thesis ..
        next
          case False
          show ?thesis unfolding mrun_append[OF aY] if_not_P[OF False] ..
        qed
        have bdefY: "b = Suc a + length (mrun Y a)" using bdef mra by simp
        have posY: "0 < fst (Y ! a)" using pos na by simp
        have fbY: "fst (Y ! b) = fst (Y ! a)" using fb na nb by simp
        have sbY: "snd (Y ! b) = snd (Y ! a)" using sb na nb by simp
        show ?thesis
        proof (cases "\<forall>x \<in> set (drop (Suc b) Y). fst (Y ! b) < fst x")
          case ob: False
          have mrb: "mrun (Y @ C) b = mrun Y b"
            unfolding mrun_append[OF bY] if_not_P[OF ob] ..
          show ?thesis unfolding mra mrb
            by (rule SY[unfolded sibm2_def, rule_format, OF aY posY bdefY bY fbY sbY])
        next
          case ob: True
          have mrb: "mrun (Y @ C) b
              = drop (Suc b) Y @ takeWhile (\<lambda>r. fst (Y ! b) < fst r) C"
            unfolding mrun_append[OF bY] if_P[OF ob] ..
          show ?thesis unfolding mra mrb unfolding C_def cp_def
            by (rule seam_I_open[OF R B ST j1d j1nz i1d hp j0d d0d
                  Yeq[unfolded cp_def] SY aY posY bdefY bY fbY sbY ob])
        qed
      next
        case bC: False
        hence bY2: "length Y \<le> b" by simp
        have hC: "C ! 0 = (entry M 0 j0 + m * d0, entry M 1 j0)"
          unfolding C_def using cpnth[OF L0] by simp
        have ctail_gt: "\<And>q. 0 < q \<Longrightarrow> q < L \<Longrightarrow> fst (C ! 0) < fst (C ! q)"
        proof -
          fix q assume q0: "0 < (q::nat)" and qL: "q < L"
          have "entry M 0 j0 < entry M 0 (j0 + q)"
            using hm0 q0 qL unfolding L_def by simp
          thus "fst (C ! 0) < fst (C ! q)"
            unfolding C_def by (simp add: cpnth[OF qL] cpnth[OF L0])
        qed
        have beq: "b = length Y"
        proof (rule ccontr)
          assume "b \<noteq> length Y"
          hence blt: "length Y < b" using bY2 by simp
          define qb where "qb = b - length Y"
          have qb0: "0 < qb" unfolding qb_def using blt by simp
          have qbL: "qb < L"
            unfolding qb_def using bL lenC bY2
            by (simp add: less_diff_conv2 add.commute)
          have nb: "(Y @ C) ! b = C ! qb"
            unfolding qb_def using bY2 by (simp add: nth_append)
          have hd_in_run: "fst ((Y @ C) ! a) < fst ((Y @ C) ! length Y)"
            by (rule runelem[OF _ blt]) (use aY in simp)
          have nY: "(Y @ C) ! length Y = C ! 0" by (simp add: nth_append)
          have "fst (C ! 0) < fst (C ! qb)" by (rule ctail_gt[OF qb0 qbL])
          moreover have "fst (C ! qb) = fst ((Y @ C) ! a)" using fb nb by simp
          ultimately show False using hd_in_run nY by simp
        qed
        have nb: "(Y @ C) ! b = C ! 0" unfolding beq by (simp add: nth_append)
        have leva: "fst (Y ! a) = entry M 0 j0 + m * d0"
          using fb na nb hC by simp
        have snda: "snd (Y ! a) = entry M 1 j0"
          using sb na nb hC by simp
        have openY: "\<forall>x \<in> set (drop (Suc a) Y). fst (Y ! a) < fst x"
        proof
          fix x assume "x \<in> set (drop (Suc a) Y)"
          then obtain t where t: "t < length Y - Suc a" "x = drop (Suc a) Y ! t"
            by (metis in_set_conv_nth length_drop)
          have pY: "Suc a + t < length Y" using t(1) by simp
          have "x = Y ! (Suc a + t)" using t aY by simp
          hence xe: "x = (Y @ C) ! (Suc a + t)" using pY by (simp add: nth_append)
          have "fst ((Y @ C) ! a) < fst ((Y @ C) ! (Suc a + t))"
            by (rule runelem) (use pY beq in simp_all)
          thus "fst (Y ! a) < fst x" using na xe by simp
        qed
        have mra: "mrun (Y @ C) a = drop (Suc a) Y"
        proof -
          have e: "mrun (Y @ C) a
              = drop (Suc a) Y @ takeWhile (\<lambda>r. fst (Y ! a) < fst r) C"
            unfolding mrun_append[OF aY] if_P[OF openY] ..
          have "length (mrun (Y @ C) a) = length Y - Suc a"
            using bdef beq aY by simp
          hence "takeWhile (\<lambda>r. fst (Y ! a) < fst r) C = []"
            using e by simp
          thus ?thesis using e by simp
        qed
        have mrb: "mrun (Y @ C) b = drop 1 C"
        proof -
          have "mrun (Y @ C) b = mrun C 0"
            using mrun_suffix[OF bY2 bL] beq by simp
          moreover have "mrun C 0 = drop 1 C"
          proof -
            have "\<forall>x \<in> set (drop 1 C). fst (C ! 0) < fst x"
            proof
              fix x assume "x \<in> set (drop 1 C)"
              then obtain t where t: "t < length C - 1" "x = drop 1 C ! t"
                by (metis in_set_conv_nth length_drop)
              have "x = C ! (1 + t)" using t lenC L0 by simp
              thus "fst (C ! 0) < fst x"
                using ctail_gt[of "1 + t"] t(1) lenC by simp
            qed
            thus ?thesis
              unfolding mrun_def using lenC L0
              by (metis One_nat_def drop0 drop_Suc_Cons hd_drop_conv_nth
                    length_pos_if_in_set list.exhaust_sel list.size(3)
                    not_gr_zero takeWhile_eq_all_conv zero_neq_one)
          qed
          ultimately show ?thesis by simp
        qed
        have openYi: "\<And>p. a < p \<Longrightarrow> p < length Y \<Longrightarrow> fst (Y ! a) < fst (Y ! p)"
        proof -
          fix p assume ap: "a < p" and pY: "p < length Y"
          have "fst ((Y @ C) ! a) < fst ((Y @ C) ! p)"
            by (rule runelem[OF ap]) (use pY beq in simp)
          thus "fst (Y ! a) < fst (Y ! p)"
            using na pY by (simp add: nth_append)
        qed
        show ?thesis
        proof (cases m)
          case 0
          have Ytk: "Y = take j0 M" unfolding Y_def 0 by simp
          have aj0: "a < j0" using aY lenY 0 by simp
          have lenM: "length M = Suc j1" using j1d j1nz by (cases M) auto
          have j0M: "j0 < length M" using j0j1 j1len by simp
          have Ma: "Y ! a = M ! a" using npre[OF aj0] .
          have dropM: "drop (Suc a) M = drop (Suc a) (take j0 M) @ drop j0 M"
          proof -
            have "drop (Suc a) M = drop (Suc a) (take j0 M @ drop j0 M)" by simp
            also have "\<dots> = drop (Suc a) (take j0 M)
                @ drop (Suc a - length (take j0 M)) (drop j0 M)"
              by (rule drop_append)
            also have "\<dots> = drop (Suc a) (take j0 M) @ drop j0 M"
              using aj0 j0M by simp
            finally show ?thesis .
          qed
          have dj0: "drop j0 M = M ! j0 # drop (Suc j0) M"
            using j0M by (rule Cons_nth_drop_Suc[symmetric])
          have fstj0: "fst (M ! j0) = fst (M ! a)"
          proof -
            have "fst (M ! j0) = entry M 0 j0" unfolding entry_def by simp
            thus ?thesis using leva Ma 0 by simp
          qed
          have mraM: "mrun M a = drop (Suc a) (take j0 M)"
          proof -
            have allpre: "\<forall>x \<in> set (drop (Suc a) (take j0 M)). fst (M ! a) < fst x"
              using openY Ma Ytk by simp
            have "takeWhile (\<lambda>r. fst (M ! a) < fst r) (drop (Suc a) M)
                  = drop (Suc a) (take j0 M)
                    @ takeWhile (\<lambda>r. fst (M ! a) < fst r) (drop j0 M)"
              unfolding dropM by (rule takeWhile_append2) (use allpre in blast)
            also have "takeWhile (\<lambda>r. fst (M ! a) < fst r) (drop j0 M) = []"
              unfolding dj0 using fstj0 by simp
            finally show ?thesis unfolding mrun_def by simp
          qed
          have lenK: "length (mrun M a) = j0 - Suc a"
            unfolding mraM using j0M by simp
          have bM: "j0 = Suc a + length (mrun M a)" using lenK aj0 by simp
          have posM: "0 < fst (M ! a)" using pos na Ma by simp
          have sndj0: "snd (M ! j0) = snd (M ! a)"
          proof -
            have "snd (M ! j0) = entry M 1 j0" unfolding entry_def by simp
            thus ?thesis using snda Ma by simp
          qed
          have aM: "a < length M" using aj0 j0M by simp
          from R[unfolded sibm2_def, rule_format, OF aM posM bM j0M fstj0 sndj0]
          have core: "sibrel (mrun M a) (mrun M j0)" by simp
          have mrj0: "mrun M j0 = drop (Suc j0) M"
          proof -
            have "\<forall>x \<in> set (drop (Suc j0) M). fst (M ! j0) < fst x"
            proof
              fix x assume "x \<in> set (drop (Suc j0) M)"
              then obtain t where t: "t < length M - Suc j0" "x = drop (Suc j0) M ! t"
                by (metis in_set_conv_nth length_drop)
              have xe: "x = M ! (Suc j0 + t)"
                using t j0M by simp
              have "entry M 0 j0 < entry M 0 (Suc j0 + t)"
                using hm0 t(1) lenM by simp
              thus "fst (M ! j0) < fst x"
                unfolding xe entry_def by simp
            qed
            thus ?thesis unfolding mrun_def by (simp add: takeWhile_eq_all_conv)
          qed
          have K1eq2: "drop 1 C = take (L - 1) (mrun M j0)"
          proof -
            have "C = blk" unfolding Ceq 0 by simp
            hence "drop 1 C = drop (Suc j0) (take j1 M)"
              unfolding blk_def by (simp add: drop_drop)
            also have "\<dots> = take (j1 - Suc j0) (drop (Suc j0) M)"
              by (rule drop_take)
            finally show ?thesis unfolding mrj0 L_def by simp
          qed
          show ?thesis
            unfolding mra mrb K1eq2
            using sibrel_trunc[OF core] mraM Ytk by simp
        next
          case (Suc km)
          define pstar where "pstar = j0 + km * L"
          have kmm: "km < m" unfolding Suc by simp
          have pstarY: "pstar < length Y"
            unfolding pstar_def lenY Suc using L0 by simp
          have Ypstar: "Y ! pstar = (entry M 0 j0 + km * d0, entry M 1 j0)"
            using ncopy[OF kmm L0] unfolding pstar_def by simp
          have lenYS: "length Y = j0 + km * L + L"
            using lenY unfolding Suc by simp
          show ?thesis
          proof (cases "d0 = 0")
            case d0z: True
            have apstar: "a = pstar"
            proof (rule ccontr)
              assume ane: "a \<noteq> pstar"
              show False
              proof (cases "a < pstar")
                case True
                have "fst (Y ! a) < fst (Y ! pstar)"
                  by (rule openYi[OF True pstarY])
                thus False using leva Ypstar d0z by simp
              next
                case False
                hence pa: "pstar < a" using ane by simp
                define qa where "qa = a - pstar"
                have qa0: "0 < qa" unfolding qa_def using pa by simp
                have qaL: "qa < L"
                proof -
                  have "a < pstar + L" using aY lenYS unfolding pstar_def by simp
                  thus ?thesis unfolding qa_def using pa
                    by (simp add: less_diff_conv2 less_imp_le add.commute)
                qed
                have adec: "a = j0 + (km * L + qa)"
                  unfolding qa_def pstar_def using pa pstar_def by simp
                have "Y ! a = (entry M 0 (j0 + qa) + km * d0, entry M 1 (j0 + qa))"
                  unfolding adec by (rule ncopy[OF kmm qaL])
                hence "entry M 0 (j0 + qa) = entry M 0 j0"
                  using leva d0z by simp
                moreover have "entry M 0 j0 < entry M 0 (j0 + qa)"
                  using hm0 qa0 qaL unfolding L_def by simp
                ultimately show False by simp
              qed
            qed
            have Ysplit: "Y = (take j0 M @ concat (map cp [0..<km])) @ cp km"
              unfolding Y_def Suc by simp
            have lenpre: "length (take j0 M @ concat (map cp [0..<km])) = pstar"
            proof -
              have "length (concat (map cp [0..<km])) = km * L"
                unfolding cp_def L_def by (rule concat_map_upt_length) simp
              moreover have "length (take j0 M) = j0" using j0j1 j1len by simp
              ultimately show ?thesis unfolding pstar_def by simp
            qed
            have Keq: "drop (Suc a) Y = drop 1 (cp km)"
            proof -
              have "drop (Suc a) Y
                  = drop (Suc a) (take j0 M @ concat (map cp [0..<km]))
                    @ drop (Suc a - length (take j0 M @ concat (map cp [0..<km])))
                        (cp km)"
                unfolding Ysplit by (rule drop_append)
              hence "drop (Suc a) Y
                  = drop (Suc a) (take j0 M @ concat (map cp [0..<km]))
                    @ drop (Suc a - pstar) (cp km)"
                unfolding lenpre .
              moreover have "drop (Suc a) (take j0 M @ concat (map cp [0..<km])) = []"
                using lenpre apstar by simp
              ultimately show ?thesis using apstar by simp
            qed
            have cpkm: "cp km = cp m" unfolding cp_def d0z by simp
            show ?thesis
              unfolding mra mrb Keq cpkm C_def[symmetric]
              unfolding sibrel_def by blast
          next
            case d0p: False
            have i1one: "i1 = 1"
              using idx1_le[of M j1] d0d d0p i1d by (cases i1) auto
            have e0j: "entry M 0 j0 < entry M 0 j1"
              using hm0 j0j1 by simp
            have ed: "entry M 0 j0 + d0 = entry M 0 j1"
              unfolding d0d using i1one e0j by simp
            have pa: "pstar < a"
            proof (rule ccontr)
              assume "\<not> pstar < a"
              hence le: "a \<le> pstar" by simp
              show False
              proof (cases "a = pstar")
                case True
                have "entry M 0 j0 + km * d0 = entry M 0 j0 + m * d0"
                  using leva Ypstar True by simp
                thus False using d0p Suc by simp
              next
                case False
                hence "a < pstar" using le by simp
                from openYi[OF this pstarY]
                have "entry M 0 j0 + m * d0 < entry M 0 j0 + km * d0"
                  using leva Ypstar by simp
                thus False using Suc d0p by simp
              qed
            qed
            define qa where "qa = a - pstar"
            have qa0: "0 < qa" unfolding qa_def using pa by simp
            have qaL: "qa < L"
            proof -
              have "a < pstar + L" using aY lenYS unfolding pstar_def by simp
              thus ?thesis unfolding qa_def using pa
                by (simp add: less_diff_conv2 less_imp_le add.commute)
            qed
            have adec: "a = j0 + (km * L + qa)"
              unfolding qa_def pstar_def using pa pstar_def by simp
            have Ya: "Y ! a = (entry M 0 (j0 + qa) + km * d0, entry M 1 (j0 + qa))"
              unfolding adec by (rule ncopy[OF kmm qaL])
            have e0qa: "entry M 0 (j0 + qa) = entry M 0 j1"
            proof -
              have "entry M 0 (j0 + qa) + km * d0 = entry M 0 j0 + m * d0"
                using leva Ya by simp
              hence "entry M 0 (j0 + qa) = entry M 0 j0 + d0"
                unfolding Suc by simp
              thus ?thesis using ed by simp
            qed
            have e1qa: "entry M 1 (j0 + qa) = entry M 1 j0"
              using snda Ya by simp
            have tclear: "\<forall>l. j0 + qa < l \<and> l < j1 \<longrightarrow> entry M 0 j1 < entry M 0 l"
            proof (intro allI impI)
              fix l assume lr: "j0 + qa < l \<and> l < j1"
              define q' where "q' = l - j0"
              have q'r: "qa < q'" "q' < L"
                unfolding q'_def L_def using lr by auto
              have ldec: "l = j0 + q'" unfolding q'_def using lr by simp
              have pp: "a < pstar + q'" using adec q'r(1) by (simp add: pstar_def)
              have ppY: "pstar + q' < length Y"
                unfolding pstar_def lenY Suc using q'r(2) by simp
              have Yp: "Y ! (pstar + q') = (entry M 0 (j0 + q') + km * d0, entry M 1 (j0 + q'))"
                using ncopy[OF kmm q'r(2)] unfolding pstar_def by (simp add: add.assoc)
              from openYi[OF pp ppY]
              have "entry M 0 (j0 + qa) + km * d0 < entry M 0 (j0 + q') + km * d0"
                using Ya Yp by simp
              thus "entry M 0 j1 < entry M 0 l"
                using e0qa ldec by simp
            qed
            have jqr: "j0 < j0 + qa" "j0 + qa < j1"
              using qa0 qaL unfolding L_def by auto
            have "entry M 1 j1 \<le> entry M 1 (j0 + qa)"
              by (rule CFGA_r1[OF ST j1d j1nz i1d[unfolded i1one, symmetric]
                    hp[unfolded i1one] j0d[unfolded i1one] jqr(1) jqr(2) e0qa tclear])
            hence le1: "entry M 1 j1 \<le> entry M 1 j0" using e1qa by simp
            have "nextrel1 M j0 j1" using nR unfolding i1one nextR_def by simp
            hence "entry M 1 j0 < entry M 1 j1" unfolding nextrel1_def by blast
            thus ?thesis using le1 by simp
          qed
        qed
      qed
    next
      case aC: False
      hence aY2: "length Y \<le> a" by simp
      define qa where "qa = a - length Y"
      define qb where "qb = b - length Y"
      have bY2: "length Y \<le> b" using ab aY2 by simp
      have qaC: "qa < length C"
        unfolding qa_def using aL aY2
        by (simp add: less_diff_conv2 add.commute)
      have qbC: "qb < length C"
        unfolding qb_def using bL bY2
        by (simp add: less_diff_conv2 add.commute)
      have qaL: "qa < L" using qaC lenC by simp
      have qbL: "qb < L" using qbC lenC by simp
      have mra: "mrun (Y @ C) a = mrun C qa"
        unfolding qa_def by (rule mrun_suffix[OF aY2 aL])
      have mrb: "mrun (Y @ C) b = mrun C qb"
        unfolding qb_def by (rule mrun_suffix[OF bY2 bL])
      have na: "(Y @ C) ! a = C ! qa"
        unfolding qa_def using aY2 by (simp add: nth_append)
      have nb: "(Y @ C) ! b = C ! qb"
        unfolding qb_def using bY2 by (simp add: nth_append)
      have bq: "qb = Suc qa + length (mrun C qa)"
      proof -
        have "b = Suc a + length (mrun C qa)" using bdef mra by simp
        thus ?thesis unfolding qa_def qb_def using aY2 by linarith
      qed
      have qa0: "0 < qa"
      proof (rule ccontr)
        assume "\<not> 0 < qa"
        hence qaz: "qa = 0" by simp
        have "\<forall>x \<in> set (drop 1 C). fst (C ! 0) < fst x"
        proof
          fix x assume "x \<in> set (drop 1 C)"
          then obtain t where t: "t < length C - 1" "x = drop 1 C ! t"
            by (metis in_set_conv_nth length_drop)
          have "x = C ! (1 + t)" using t lenC L0 by simp
          moreover have "entry M 0 j0 < entry M 0 (j0 + (1 + t))"
            using hm0 t(1) lenC unfolding L_def by simp
          ultimately show "fst (C ! 0) < fst x"
            using cpnth[of "1+t" m] cpnth[OF L0] t(1) lenC
            unfolding C_def by simp
        qed
        hence "mrun C 0 = drop 1 C"
          unfolding mrun_def using lenC L0
          by (metis One_nat_def drop0 drop_Suc_Cons hd_drop_conv_nth
                length_pos_if_in_set list.exhaust_sel list.size(3)
                not_gr_zero takeWhile_eq_all_conv zero_neq_one)
        hence "length (mrun C 0) = L - 1" using lenC by simp
        hence "qb = L" using bq qaz L0 by simp
        thus False using qbL by simp
      qed
      have posblk: "0 < fst (blk ! qa)"
      proof -
        have "entry M 0 j0 < entry M 0 (j0 + qa)"
          using hm0 qa0 qaL unfolding L_def by simp
        thus ?thesis using blknth[OF qaL] unfolding entry_def by simp
      qed
      have blksfx: "take j1 M = take j0 M @ blk"
        unfolding blk_def
        by (metis append_take_drop_id j0j1 min.absorb1 nat_less_le take_take)
      have lentj0: "length (take j0 M) = j0" using j0j1 j1len by simp
      have mrblk: "\<And>q. q < L \<Longrightarrow> mrun (take j1 M) (j0 + q) = mrun blk q"
      proof -
        fix q assume qL: "q < L"
        have "length (take j0 M) \<le> j0 + q" using lentj0 by simp
        moreover have "j0 + q < length (take j0 M @ blk)"
          using lentj0 lenblk qL by simp
        ultimately have "mrun (take j0 M @ blk) (j0 + q)
            = mrun blk (j0 + q - length (take j0 M))"
          by (rule mrun_suffix)
        thus "mrun (take j1 M) (j0 + q) = mrun blk q"
          unfolding blksfx[symmetric] using lentj0 by simp
      qed
      have tjnth: "\<And>q. q < L \<Longrightarrow> take j1 M ! (j0 + q) = M ! (j0 + q)"
        unfolding L_def using j1len by simp
      have fblk: "fst (blk ! qb) = fst (blk ! qa)"
      proof -
        have "fst (C ! qb) = fst (C ! qa)" using fb sb na nb by simp
        thus ?thesis
          using shf_nth[of qa blk "m*d0"] shf_nth[of qb blk "m*d0"]
            qaL qbL lenblk unfolding Ceq by simp
      qed
      have sblk: "snd (blk ! qb) = snd (blk ! qa)"
      proof -
        have "snd (C ! qb) = snd (C ! qa)" using sb na nb by simp
        thus ?thesis
          using shf_nth[of qa blk "m*d0"] shf_nth[of qb blk "m*d0"]
            qaL qbL lenblk unfolding Ceq by simp
      qed
      have core: "sibrel (mrun (take j1 M) (j0 + qa)) (mrun (take j1 M) (j0 + qb))"
      proof -
        have S1: "sibm2 (take j1 M)" by (rule sibm2_take[OF R])
        have i1': "j0 + qa < length (take j1 M)"
          using qaL j1len unfolding L_def by simp
        have i2': "0 < fst (take j1 M ! (j0 + qa))"
          using posblk blknth[OF qaL] tjnth[OF qaL] by simp
        have i3': "j0 + qb = Suc (j0 + qa) + length (mrun (take j1 M) (j0 + qa))"
        proof -
          have "length (mrun C qa) = length (mrun blk qa)"
            unfolding Ceq using shf_mrun[of qa blk "m*d0"] qaL lenblk by simp
          thus ?thesis using bq mrblk[OF qaL] by simp
        qed
        have i4': "j0 + qb < length (take j1 M)"
          using qbL j1len unfolding L_def by simp
        have i5': "fst (take j1 M ! (j0 + qb)) = fst (take j1 M ! (j0 + qa))"
          using fblk blknth[OF qaL] blknth[OF qbL] tjnth[OF qaL] tjnth[OF qbL] by simp
        have i6': "snd (take j1 M ! (j0 + qb)) = snd (take j1 M ! (j0 + qa))"
          using sblk blknth[OF qaL] blknth[OF qbL] tjnth[OF qaL] tjnth[OF qbL] by simp
        from S1[unfolded sibm2_def, rule_format, OF i1' i2' i3' i4' i5' i6']
        show ?thesis .
      qed
      have "sibrel (mrun blk qa) (mrun blk qb)"
        using core mrblk[OF qaL] mrblk[OF qbL] by simp
      hence "sibrel (shf (m*d0) (mrun blk qa)) (shf (m*d0) (mrun blk qb))"
        by (rule shf_sibrel)
      thus ?thesis
        unfolding mra mrb unfolding Ceq
        using shf_mrun[of qa blk "m*d0"] shf_mrun[of qb blk "m*d0"]
          qaL qbL lenblk by simp
    qed
  qed
  show ?thesis
    using main unfolding Y_def C_def cp_def by simp
qed

lemma sibm2_oper_bad:
  assumes "sibm2 M" and "blockok 0 M" and "M \<in> ST_PS"
    and "j1 = Lng M - 1" and "j1 \<noteq> 0"
    and "i1 = idx1 M j1" and "hasParent M i1 j1"
    and "j0 = parent M i1 j1"
    and "d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0)"
    and opeq: "oper M n = take j0 M @ concat (map (\<lambda>k.
           map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j)) [j0..<j1]) [0..<n])"
  shows "sibm2 (oper M n)"
proof -
  have all: "sibm2 (take j0 M @ concat (map (\<lambda>k.
        map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j)) [j0..<j1]) [0..<n]))"
  proof (induct n)
    case 0 show ?case using sibm2_take[OF assms(1)] by simp
  next
    case (Suc n)
    show ?case by (rule sibm2_snoc_copy[OF assms(1-9) Suc])
  qed
  show ?thesis unfolding opeq by (rule all)
qed

lemma sibm2_oper:
  assumes R: "sibm2 M" and ST: "M \<in> ST_PS" and n1: "1 \<le> n"
  shows "sibm2 (oper M n)"
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
      moreover have "sibm2 (Pred M)"
        unfolding Pred_def using R sibm2_butlast by simp
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
        moreover have "sibm2 (Pred M)"
          unfolding Pred_def using R sibm2_butlast by simp
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
          by (rule sibm2_oper_bad[OF R b ST j1_def False i1_def hp j0_def d0_def opeq])
      qed
    qed
  qed
qed

theorem sibm2_ST_PS: "M \<in> ST_PS \<Longrightarrow> sibm2 M"
proof (induction M rule: ST_PS.induct)
  case (diag v) show ?case by (rule sibm2_diagSeq)
next
  case (oper M n)
  show ?case by (rule sibm2_oper[OF oper.IH oper.hyps(1) oper.hyps(2)])
qed

text \<open>(SIB, repaired) On subscript ties the runs are related by \<open>sibrel\<close>:
  equal, proper prefix, or first-difference descent with both runs
  head-maximal (memo 続29; closure+2 windows: 3027 configs, all in family,
  zero \<open>NT_tie\<close> violations).  The window truncation of the successor's run
  is absorbed by \<open>sibrel_trunc\<close>.\<close>

lemma SIB_shape2:
  assumes A: "fbseg u (c # rest)"
    and T: "dropWhile (\<lambda>r. fst c < fst r) rest = c1 # rest1"
    and tie: "snd c1 = snd c"
  shows "sibrel (takeWhile (\<lambda>r. fst c < fst r) rest)
                (takeWhile (\<lambda>r. fst c1 < fst r) rest1)"
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
  have sm: "sibm2 H" unfolding H_def by (rule sibm2_ST_PS[OF h])
  have bb: "b = Suc ic + length (mrun H ic)" unfolding b_def mric by simp
  have fstb: "fst (H ! b) = fst (H ! ic)" unfolding Hb Hic using lvl by simp
  have sndb: "snd (H ! b) = snd (H ! ic)" unfolding Hb Hic using tie by simp
  have icpos: "0 < fst (H ! ic)" unfolding Hic using cpos by simp
  from sm[unfolded sibm2_def, rule_format, OF icH icpos bb bH fstb sndb]
  have core: "sibrel (mrun H ic) (mrun H b)" .
  from mrb_pre obtain E where E: "mrun H b = ?K1 @ E" by blast
  have tk: "?K1 = take (length ?K1) (mrun H b)"
    unfolding E by simp
  show ?thesis
    using sibrel_trunc[OF core[unfolded mric], of "length ?K1"] tk by metis
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

text \<open>(G6, unified dominance core) On a provenance segment \<^emph>\<open>any\<close> visible
  critical whose head subscript attains the max row-1 is at most the
  max-row1 suffix image — no fire, no head-max and no violator premise
  (closure+2: 711342 visible max-headed criticals over 460931 dseg
  windows, zero violations).  Subsumes \<open>E6_dom_tie\<close>, the deep tie case and
  \<open>E6_lpl\<close>.  The exact \<open>dseg\<close> shape (adjacent dominator, \<open>u = snd pp\<close>) is
  essential: both the \<open>u = 0\<close> relaxation and the \<open>fbseg\<close> mid-gap relaxation
  already fail at closure+1 (84795 resp. 10586 violations).\<close>

lemma E6_G6:
  assumes "dseg u S"
    and "g \<in> Gterm u (nrm (translate S))" and "g \<noteq> Z"
    and "hdsub g = maxr1 S"
  shows "ole g (nrm (translate (msfx S)))"
  sorry

lemma E6_dom_tie:
  assumes "dseg u S" and "pfire u (nrm (translate S))"
    and "g \<in> Gterm u (nrm (translate S))" and "\<not> olt g (nrm (translate S))"
    and "g \<noteq> Z" and "hdsub g = maxr1 S"
  shows "ole g (nrm (translate (msfx S)))"
  by (rule E6_G6[OF assms(1) assms(3) assms(5) assms(6)])

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

text \<open>(QDIAG) In the q-cut configuration a firing extension already forces
  the segment's row 1 to be strictly increasing — the segment's own fire is
  redundant (closure+2: 32491 extension-fire positions, zero violations;
  without any fire premise 20819 violations).\<close>

lemma E6_QDIAG:
  assumes "segprov u S q" and "S \<noteq> []"
    and "pfire u (nrm (translate (S @ [q])))"
    and "maxr1 S < snd q"
    and "Suc i < length S"
  shows "snd (S ! i) < snd (S ! Suc i)"
  sorry

text \<open>(V4) In the both-fire q-cut configuration the x-side suffix is the last
  column alone.\<close>

lemma E6_qcut_last:
  assumes "segprov u S q" and "S \<noteq> []"
    and "pfire u (nrm (translate S))" and "pfire u (nrm (translate (S @ [q])))"
    and "maxr1 S < snd q"
  shows "msfx S = [last S]"
proof -
  have step: "\<And>i. Suc i < length S \<Longrightarrow> snd (S ! i) < snd (S ! Suc i)"
    using E6_QDIAG[OF assms(1,2,4,5)] by blast
  have mono: "\<And>j. j < length S \<Longrightarrow> \<forall>i. i \<le> j \<longrightarrow> snd (S ! i) \<le> snd (S ! j)"
  proof -
    fix j
    show "j < length S \<Longrightarrow> \<forall>i. i \<le> j \<longrightarrow> snd (S ! i) \<le> snd (S ! j)"
    proof (induction j)
      case 0 thus ?case by simp
    next
      case (Suc j)
      have jS: "j < length S" using Suc.prems by simp
      show ?case
      proof (intro allI impI)
        fix i assume "i \<le> Suc j"
        thus "snd (S ! i) \<le> snd (S ! Suc j)"
        proof (cases "i = Suc j")
          case True thus ?thesis by simp
        next
          case False
          hence "i \<le> j" using \<open>i \<le> Suc j\<close> by simp
          hence "snd (S ! i) \<le> snd (S ! j)" using Suc.IH jS by blast
          also have "\<dots> < snd (S ! Suc j)" using step Suc.prems by blast
          finally show ?thesis by simp
        qed
      qed
    qed
  qed
  have Sne: "S \<noteq> []" by (rule assms(2))
  define n where "n = length S - 1"
  have nS: "n < length S" unfolding n_def using Sne by (cases S) auto
  have lastn: "last S = S ! n" unfolding n_def using Sne by (simp add: last_conv_nth)
  have lastmax: "\<And>x. x \<in> set S \<Longrightarrow> snd x \<le> snd (last S)"
  proof -
    fix x assume "x \<in> set S"
    then obtain i where ii: "i < length S" "x = S ! i" by (metis in_set_conv_nth)
    have "i \<le> n" unfolding n_def using ii(1) by simp
    thus "snd x \<le> snd (last S)" using mono[OF nS] ii(2) lastn by simp
  qed
  have mx: "maxr1 S = snd (last S)"
    unfolding maxr1_def
  proof (rule Max_eqI)
    show "finite (snd ` set S)" by simp
    show "\<And>s. s \<in> snd ` set S \<Longrightarrow> s \<le> snd (last S)" using lastmax by auto
    show "snd (last S) \<in> snd ` set S" using Sne by (simp add: last_in_set)
  qed
  have blstrict: "\<forall>x \<in> set (butlast S). snd x < maxr1 S"
  proof
    fix x assume "x \<in> set (butlast S)"
    then obtain i where ii: "i < length (butlast S)" "x = butlast S ! i"
      by (metis in_set_conv_nth)
    have iln: "i < n" unfolding n_def using ii(1) by simp
    have xe: "x = S ! i" using ii by (simp add: nth_butlast)
    have "snd (S ! i) \<le> snd (S ! (n - 1))"
      using mono[of "n - 1"] nS iln by auto
    also have "\<dots> < snd (S ! n)"
      using step[of "n - 1"] iln nS by auto
    finally show "snd x < maxr1 S" using xe mx lastn by simp
  qed
  have dec: "S = butlast S @ [last S]" using Sne by simp
  have "msfx S = dropWhile (\<lambda>c. snd c < maxr1 S) (butlast S @ [last S])"
    unfolding msfx_def using dec by metis
  also have "\<dots> = dropWhile (\<lambda>c. snd c < maxr1 S) [last S]"
    by (rule dropWhile_append2) (use blstrict in blast)
  also have "\<dots> = [last S]" using mx by simp
  finally show ?thesis .
qed

text \<open>(FBS) Fire is butlast-stable on long provenance segments: if the
  extended segment fires, so does the segment itself once it has at least
  two columns (closure+2: 5370 extended fires, zero violations, including
  mid-host \<open>q\<close>).\<close>

lemma E6_FBS:
  assumes "segprov u S q" and "2 \<le> length S"
    and "pfire u (nrm (translate (S @ [q])))"
  shows "pfire u (nrm (translate S))"
  sorry

text \<open>(V5) In the extension-only-fire configuration the segment is a single
  column.\<close>

lemma E6_iii_singleton:
  assumes "segprov u S q" and "S \<noteq> []"
    and "\<not> pfire u (nrm (translate S))" and "pfire u (nrm (translate (S @ [q])))"
  shows "\<exists>c. S = [c]"
proof (cases "2 \<le> length S")
  case True
  have "pfire u (nrm (translate S))"
    by (rule E6_FBS[OF assms(1) True assms(4)])
  thus ?thesis using assms(3) by simp
next
  case False
  have "length S \<noteq> 0" using assms(2) by simp
  hence "length S = 1" using False by arith
  thus ?thesis by (metis One_nat_def length_0_conv length_Suc_conv)
qed

text \<open>(seam-MIN) On any \<^emph>\<open>firing\<close> provenance segment the max-row1 suffix has
  a row0-minimal head.  This is the q-free general form: no both-fire
  coupling, no cut condition (closure+2: 458980 fire segments, zero
  violations; the fire premise is essential — without it closure+1 already
  has 70 violations).\<close>

lemma E6_seam_MIN:
  assumes "segprov u S q" and "S \<noteq> []"
    and "pfire u (nrm (translate S))"
  shows "\<forall>x \<in> set (msfx S). fst (hd (msfx S)) \<le> fst x"
  sorry

text \<open>(seam-INV) Under the same fire premise the suffix head also stays
  at-or-below the appended column's row0 whenever that column cuts
  at-or-below the segment's max row1 (closure+2: 426489 same-cut fire
  positions, zero violations).\<close>

lemma E6_seam_INV:
  assumes "segprov u S q" and "S \<noteq> []"
    and "pfire u (nrm (translate S))"
    and "snd q \<le> maxr1 S"
  shows "fst (hd (msfx S)) \<le> fst q"
  sorry

text \<open>(seam) In the both-fire same-cut configuration the max-row1 suffix
  satisfies the spiral invariants against the appended column.\<close>

lemma E6_seam:
  assumes "segprov u S q" and "S \<noteq> []"
    and "pfire u (nrm (translate S))" and "pfire u (nrm (translate (S @ [q])))"
    and "snd q \<le> maxr1 S"
  shows "fst (hd (msfx S)) \<le> fst q \<and> (\<forall>x \<in> set (msfx S). fst (hd (msfx S)) \<le> fst x)"
  using E6_seam_INV[OF assms(1,2,3,5)] E6_seam_MIN[OF assms(1,2,3)] by blast

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
    and "fst p \<le> fst q"
    and "\<forall>x \<in> set rest. fst p \<le> fst x"
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
    proof -
      have invq: "fst p \<le> fst q" using INV unfolding C by simp
      have inv2r: "\<forall>x \<in> set rest. fst p \<le> fst x"
        using INV2 unfolding C by simp
      show ?thesis by (rule STS_B[OF host[unfolded C] Tne hdTeq invq inv2r])
    qed
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

text \<open>(LPL) A proper later piece whose normalized head subscript matches the
  head-maximal whole loses to the whole: from \<open>E6_G6\<close>, since head-maximality
  makes the suffix the whole segment, and the size bound makes the bound
  strict.\<close>

lemma E6_lpl:
  assumes D: "dseg u S" and HM: "snd (hd S) = maxr1 S"
    and SC: "S = pre' @ C @ post'" and Cne: "C \<noteq> []" and Pne: "pre' \<noteq> []"
    and HS: "hdsub (nrm (translate C)) = maxr1 S"
    and G: "nrm (translate C) \<in> Gterm u (nrm (translate S))"
  shows "olt (nrm (translate C)) (nrm (translate S))"
proof -
  have Sne: "S \<noteq> []" using D unfolding dseg_def by blast
  obtain c ct where C: "C = c # ct" using Cne by (cases C) auto
  have NZ: "nrm (translate C) \<noteq> Z" unfolding C by (rule NT_neZ)
  have mS: "msfx S = S"
  proof -
    obtain s ss where S: "S = s # ss" using Sne by (cases S) auto
    have "\<not> snd s < maxr1 S" using HM unfolding S by simp
    thus ?thesis unfolding msfx_def S by simp
  qed
  have "ole (nrm (translate C)) (nrm (translate (msfx S)))"
    by (rule E6_G6[OF D G NZ HS])
  moreover have "nrm (translate C) \<noteq> nrm (translate S)"
    using Gterm_size[OF G] by auto
  ultimately show ?thesis unfolding mS by auto
qed

text \<open>(HDOM) A head-maximal class segment has no fire: every critical loses.
  Resolved down to \<open>E6_lpl\<close> by the catalogue, the subscript bound, and prefix
  monotonicity \<dash> all through the unified core \<open>E6_G6\<close>.\<close>

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
      have hsC: "hdsub (nrm (translate Cp)) = maxr1 S"
        using w(4) True unfolding w(3) by simp
      have "olt (nrm (translate Cp)) (nrm (translate S))"
        by (rule E6_lpl[OF D HM w(1) w(2) pne hsC G[unfolded w(3)]])
      thus False using w(3) V by simp
    qed
  qed
qed

text \<open>The level of the head of a tie-sibling run: the host block discipline
  forces the first run column one level above its head column.\<close>

lemma fbseg_run_hd_level:
  assumes A: "fbseg u (c # rest)"
    and ne: "takeWhile (\<lambda>r. fst c < fst r) rest \<noteq> []"
  shows "fst (hd (takeWhile (\<lambda>r. fst c < fst r) rest)) = Suc (fst c)"
proof -
  let ?K = "takeWhile (\<lambda>r. fst c < fst r) rest"
  from A obtain pre pp mid post
    where h: "pre @ (pp # mid @ (c # rest)) @ post \<in> ST_PS"
    unfolding fbseg_def by blast
  define H where "H = pre @ (pp # mid @ (c # rest)) @ post"
  define ic where "ic = length pre + 1 + length mid"
  have rne: "rest \<noteq> []" using ne by auto
  have hdK: "hd ?K = hd rest"
    using ne by (cases rest) (auto split: if_splits)
  have gt: "fst c < fst (hd ?K)"
    using ne set_takeWhileD by (metis hd_in_set)
  have so: "stepsok H"
    using blockok_stepsok blockok_ST_PS[OF h] H_def by blast
  have Hic: "H ! ic = c"
  proof -
    have "H = (pre @ pp # mid) @ c # (rest @ post)"
      unfolding H_def by simp
    moreover have "length (pre @ pp # mid) = ic" unfolding ic_def by simp
    ultimately show ?thesis by (metis nth_append_length)
  qed
  have Hic1: "H ! Suc ic = hd rest"
  proof -
    have "H = (pre @ pp # mid @ [c]) @ hd rest # (tl rest @ post)"
      unfolding H_def using rne by simp
    moreover have "length (pre @ pp # mid @ [c]) = Suc ic"
      unfolding ic_def by simp
    ultimately show ?thesis by (metis nth_append_length)
  qed
  have ln: "Suc ic < length H"
  proof -
    have "length H = length pre + 1 + length mid + 1 + length rest + length post"
      unfolding H_def by simp
    thus ?thesis unfolding ic_def using rne by (cases rest) auto
  qed
  have "fst (H ! Suc ic) \<le> Suc (fst (H ! ic))"
    using so[unfolded stepsok_def, rule_format, OF ln] .
  hence "fst (hd rest) \<le> Suc (fst c)" unfolding Hic Hic1 .
  thus ?thesis using gt hdK by simp
qed

text \<open>(tie no-fire, class facts) A tie-sibling run that is not head-maximal
  never fires at its head's subscript: the row-1 maximum is buried under a
  lower-subscript head, so visibility fails.  (Empirically: closure+2, all
  3027 tie window configurations are no-fire on both sides; the non-head-max
  ones \<dash> 24 configs \<dash> are exactly the P/E-shaped ones.)\<close>

text \<open>If the head subscript of an fbseg window is already below \<open>u\<close>, the
  whole \<open>u\<close>-visible catalogue is empty: the sum-spine subscripts only
  decrease (\<open>NT_dom_sub_eq\<close> along the forced level-ties), so no subterm is
  ever exposed at \<open>u\<close>.\<close>

lemma Gterm_empty_lowhead:
  assumes "fbseg w S" and "S \<noteq> []" and "snd (hd S) < u"
  shows "Gterm u (nrm (translate S)) = {}"
  using assms
proof (induct S arbitrary: w rule: length_induct)
  case (1 S)
  note IH = 1(1) and fb = 1(2) and ne = 1(3) and low = 1(4)
  obtain c0 rest0 where C: "S = c0 # rest0" using ne by (cases S) auto
  let ?T = "dropWhile (\<lambda>r. fst c0 < fst r) rest0"
  have sh: "nrm (translate S)
      = P (snd c0) (proj (snd c0) (nrm (translate (takeWhile (\<lambda>r. fst c0 < fst r) rest0))))
                   (nrm (translate ?T))"
    unfolding C by (rule NT_shape[OF fb[unfolded C] refl])
  have lowc: "snd c0 < u" using low C by simp
  have Tempty: "Gterm u (nrm (translate ?T)) = {}"
  proof (cases ?T)
    case Nil
    show ?thesis unfolding Nil by simp
  next
    case (Cons c1 rest1)
    have Tne: "?T \<noteq> []" unfolding Cons by simp
    have fbT: "fbseg w ?T" by (rule fbseg_T_desc[OF fb[unfolded C] Tne])
    have lvl: "fst c1 = fst c0"
      by (rule fbseg_hd_level[OF fb[unfolded C] Cons])
    have sub: "snd c1 \<le> snd c0"
      by (rule NT_dom_sub_eq[OF fb[unfolded C] Cons lvl])
    have lenT: "length ?T < length S"
      unfolding C using length_dropWhile_le[of "\<lambda>r. fst c0 < fst r" rest0]
      by simp
    have lowT: "snd (hd ?T) < u" unfolding Cons using sub lowc by simp
    show ?thesis
      using IH[rule_format, OF lenT fbT Tne lowT] .
  qed
  show ?case unfolding sh using lowc Tempty by simp
qed

text \<open>(tie no-fire, high-head residuals) The only unproven part of the tie
  no-fire facts: a non-head-maximal tie run whose head subscript is not
  below the tie subscript (empirically empty at closure+2).\<close>

lemma E6_tie_nofire_high0:
  assumes A: "fbseg u (c # rest)"
    and D: "dropWhile (\<lambda>r. fst c < fst r) rest = c1 # rest1"
    and S: "snd c1 = snd c"
    and NE: "takeWhile (\<lambda>r. fst c < fst r) rest \<noteq> []"
    and NH: "snd (hd (takeWhile (\<lambda>r. fst c < fst r) rest))
         \<noteq> maxr1 (takeWhile (\<lambda>r. fst c < fst r) rest)"
    and HI: "snd c \<le> snd (hd (takeWhile (\<lambda>r. fst c < fst r) rest))"
  shows "\<not> pfire (snd c) (nrm (translate (takeWhile (\<lambda>r. fst c < fst r) rest)))"
proof -
  define K where "K = takeWhile (\<lambda>r. fst c < fst r) rest"
  have KNE: "K \<noteq> []" unfolding K_def by (rule NE)
  obtain pre pp mid post where H: "pre @ (pp # mid @ (c # rest)) @ post \<in> ST_PS"
    and dom: "\<forall>r \<in> set (mid @ (c # rest)). fst pp < fst r"
    using A unfolding fbseg_def by blast
  define H' where "H' = pre @ (pp # mid @ (c # rest)) @ post"
  have HST: "H' \<in> ST_PS" unfolding H'_def by (rule H)
  have T1: "t1ok H'" and T3: "t3ok H'"
    using t13ok_ST_PS[OF HST] by blast+
  define a where "a = length pre + (1 + length mid)"
  have nthc: "H' ! a = c"
    unfolding H'_def a_def by (simp add: nth_append)
  have dropa: "drop (Suc a) H' = rest @ post"
    unfolding H'_def a_def by (simp add: drop_append)
  have rdec: "rest = K @ (c1 # rest1)"
    unfolding K_def using D by (metis takeWhile_dropWhile_id)
  have mrK: "mrun H' a = K"
  proof -
    have nP: "\<not> fst c < fst c1"
    proof -
      have "dropWhile (\<lambda>r. fst c < fst r) rest \<noteq> []" using D by simp
      hence "\<not> fst c < fst (hd (dropWhile (\<lambda>r. fst c < fst r) rest))"
        by (rule hd_dropWhile)
      thus ?thesis using D by simp
    qed
    have allK: "\<forall>x \<in> set K. fst c < fst x"
      unfolding K_def using set_takeWhileD by metis
    have split: "rest @ post = K @ ((c1 # rest1) @ post)" using rdec by simp
    have "takeWhile (\<lambda>r. fst c < fst r) (rest @ post)
        = K @ takeWhile (\<lambda>r. fst c < fst r) ((c1 # rest1) @ post)"
      unfolding split by (rule takeWhile_append2) (use allK in blast)
    moreover have "takeWhile (\<lambda>r. fst c < fst r) ((c1 # rest1) @ post) = []"
      using nP by simp
    ultimately show ?thesis unfolding mrun_def nthc dropa by simp
  qed
  have lenH: "length H' = length pre + 2 + length mid + length rest + length post"
    unfolding H'_def by simp
  have lrest: "length rest = length K + 1 + length rest1" using rdec by simp
  have aH: "a < length H'" unfolding a_def lenH by simp
  have bH: "Suc a + length K < length H'"
    unfolding a_def lenH lrest by simp
  have nthc1: "H' ! (Suc a + length K) = c1"
  proof -
    have "H' ! (Suc a + length K) = drop (Suc a) H' ! length K"
      using bH by (simp add: add.commute)
    also have "\<dots> = (K @ ((c1 # rest1) @ post)) ! length K"
      unfolding dropa using rdec by simp
    also have "\<dots> = c1" by (simp add: nth_append)
    finally show ?thesis .
  qed
  have posH: "0 < fst (H' ! a)"
  proof -
    have "c \<in> set (mid @ (c # rest))" by simp
    hence "fst pp < fst c" using dom by blast
    thus ?thesis unfolding nthc by simp
  qed
  have bdefH: "Suc a + length K = Suc a + length (mrun H' a)" using mrK by simp
  have sndt: "snd (H' ! (Suc a + length K)) = snd (H' ! a)"
    unfolding nthc1 nthc using S by simp
  have t1b: "\<forall>x \<in> set K. snd x \<le> Suc (snd c)"
    using T1[unfolded t1ok_def, rule_format, of a "Suc a + length K"]
      aH posH bdefH bH sndt unfolding mrK nthc by blast
  define y where "y = snd (hd K)"
  have yK: "y \<in> snd ` set K" unfolding y_def using KNE by (simp add: hd_in_set)
  have yub: "y \<le> Suc (snd c)" using t1b yK by auto
  have ylb: "snd c \<le> y" using HI unfolding y_def K_def .
  have hmK: "snd (hd K) = maxr1 K"
  proof (cases "y = snd c")
    case True
    have hdt: "snd (hd (mrun H' a)) = snd (H' ! a)"
      unfolding mrK nthc using True y_def by simp
    have mne: "mrun H' a \<noteq> []" unfolding mrK by (rule KNE)
    have t3b: "\<forall>x \<in> set K. snd x \<le> snd c"
      using T3[unfolded t3ok_def, rule_format, of a "Suc a + length K"]
        aH posH bdefH bH sndt mne hdt unfolding mrK nthc by blast
    have "Max (snd ` set K) = y"
      by (rule Max_eqI) (use t3b yK True in auto)
    thus ?thesis unfolding maxr1_def y_def by simp
  next
    case False
    hence yS: "y = Suc (snd c)" using yub ylb by arith
    have "Max (snd ` set K) = y"
      by (rule Max_eqI) (use t1b yK yS in auto)
    thus ?thesis unfolding maxr1_def y_def by simp
  qed
  have False using NH[folded K_def] hmK by simp
  thus ?thesis ..
qed

lemma E6_tie_nofire_high1:
  assumes A: "fbseg u (c # rest)"
    and D: "dropWhile (\<lambda>r. fst c < fst r) rest = c1 # rest1"
    and S: "snd c1 = snd c"
    and NE: "takeWhile (\<lambda>r. fst c1 < fst r) rest1 \<noteq> []"
    and NH: "snd (hd (takeWhile (\<lambda>r. fst c1 < fst r) rest1))
         \<noteq> maxr1 (takeWhile (\<lambda>r. fst c1 < fst r) rest1)"
    and HI: "snd c1 \<le> snd (hd (takeWhile (\<lambda>r. fst c1 < fst r) rest1))"
  shows "\<not> pfire (snd c1) (nrm (translate (takeWhile (\<lambda>r. fst c1 < fst r) rest1)))"
proof -
  define K where "K = takeWhile (\<lambda>r. fst c < fst r) rest"
  define K1 where "K1 = takeWhile (\<lambda>r. fst c1 < fst r) rest1"
  have K1NE: "K1 \<noteq> []" unfolding K1_def by (rule NE)
  obtain pre pp mid post where H: "pre @ (pp # mid @ (c # rest)) @ post \<in> ST_PS"
    and dom: "\<forall>r \<in> set (mid @ (c # rest)). fst pp < fst r"
    using A unfolding fbseg_def by blast
  define H' where "H' = pre @ (pp # mid @ (c # rest)) @ post"
  have HST: "H' \<in> ST_PS" unfolding H'_def by (rule H)
  have T14: "t14ok H'" using t13ok_ST_PS[OF HST] by blast
  define a where "a = length pre + (1 + length mid)"
  have nthc: "H' ! a = c"
    unfolding H'_def a_def by (simp add: nth_append)
  have dropa: "drop (Suc a) H' = rest @ post"
    unfolding H'_def a_def by (simp add: drop_append)
  have rdec: "rest = K @ (c1 # rest1)"
    unfolding K_def using D by (metis takeWhile_dropWhile_id)
  have mrK: "mrun H' a = K"
  proof -
    have nP: "\<not> fst c < fst c1"
    proof -
      have "dropWhile (\<lambda>r. fst c < fst r) rest \<noteq> []" using D by simp
      hence "\<not> fst c < fst (hd (dropWhile (\<lambda>r. fst c < fst r) rest))"
        by (rule hd_dropWhile)
      thus ?thesis using D by simp
    qed
    have allK: "\<forall>x \<in> set K. fst c < fst x"
      unfolding K_def using set_takeWhileD by metis
    have split: "rest @ post = K @ ((c1 # rest1) @ post)" using rdec by simp
    have "takeWhile (\<lambda>r. fst c < fst r) (rest @ post)
        = K @ takeWhile (\<lambda>r. fst c < fst r) ((c1 # rest1) @ post)"
      unfolding split by (rule takeWhile_append2) (use allK in blast)
    moreover have "takeWhile (\<lambda>r. fst c < fst r) ((c1 # rest1) @ post) = []"
      using nP by simp
    ultimately show ?thesis unfolding mrun_def nthc dropa by simp
  qed
  have lenH: "length H' = length pre + 2 + length mid + length rest + length post"
    unfolding H'_def by simp
  have lrest: "length rest = length K + 1 + length rest1" using rdec by simp
  have aH: "a < length H'" unfolding a_def lenH by simp
  define b where "b = Suc a + length K"
  have bH: "b < length H'" unfolding b_def a_def lenH lrest by simp
  have nthc1: "H' ! b = c1"
  proof -
    have "H' ! b = drop (Suc a) H' ! length K"
      unfolding b_def using bH[unfolded b_def] by (simp add: add.commute)
    also have "\<dots> = (K @ ((c1 # rest1) @ post)) ! length K"
      unfolding dropa using rdec by simp
    also have "\<dots> = c1" by (simp add: nth_append)
    finally show ?thesis .
  qed
  have posH: "0 < fst (H' ! a)"
  proof -
    have "c \<in> set (mid @ (c # rest))" by simp
    hence "fst pp < fst c" using dom by blast
    thus ?thesis unfolding nthc by simp
  qed
  have bdefH: "b = Suc a + length (mrun H' a)" unfolding b_def mrK ..
  have sndt: "snd (H' ! b) = snd (H' ! a)"
    unfolding nthc1 nthc using S by simp
  have dropb: "drop (Suc b) H' = rest1 @ post"
  proof -
    have "drop (Suc b) H' = drop (Suc (length K)) (drop (Suc a) H')"
      unfolding b_def by (simp add: drop_drop add.commute)
    also have "\<dots> = drop (Suc (length K)) (K @ ((c1 # rest1) @ post))"
      unfolding dropa using rdec by simp
    also have "\<dots> = rest1 @ post" by simp
    finally show ?thesis .
  qed
  have mrb: "mrun H' b = takeWhile (\<lambda>r. fst c1 < fst r) (rest1 @ post)"
    unfolding mrun_def nthc1 dropb ..
  have K1pre: "K1 = take (length K1) (mrun H' b)"
  proof (cases "takeWhile (\<lambda>r. fst c1 < fst r) rest1 = rest1")
    case True
    have "mrun H' b = rest1 @ takeWhile (\<lambda>r. fst c1 < fst r) post"
      unfolding mrb by (rule takeWhile_append2) (use True set_takeWhileD in \<open>force\<close>)
    moreover have "K1 = rest1" unfolding K1_def by (rule True)
    ultimately show ?thesis by simp
  next
    case False
    then obtain w where w: "w \<in> set rest1" "\<not> fst c1 < fst w"
      by (metis set_takeWhileD takeWhile_eq_all_conv)
    have "mrun H' b = takeWhile (\<lambda>r. fst c1 < fst r) rest1"
      unfolding mrb using w by (rule takeWhile_append1)
    thus ?thesis unfolding K1_def by simp
  qed
  have mbne: "mrun H' b \<noteq> []" using K1pre K1NE by auto
  have hdeq1: "hd (mrun H' b) = hd K1"
  proof -
    have l0: "0 < length K1" using K1NE by (cases K1) auto
    have "hd K1 = K1 ! 0" using K1NE by (simp add: hd_conv_nth)
    also have "\<dots> = take (length K1) (mrun H' b) ! 0" using K1pre by metis
    also have "\<dots> = mrun H' b ! 0" using l0 by simp
    also have "\<dots> = hd (mrun H' b)" using mbne by (simp add: hd_conv_nth)
    finally show ?thesis by simp
  qed
  have hib: "snd (H' ! b) \<le> snd (hd (mrun H' b))"
    using HI nthc1 hdeq1 unfolding K1_def by simp
  have hmb: "snd (hd (mrun H' b)) = maxr1 (mrun H' b)"
    using T14[unfolded t14ok_def, rule_format, of a b]
      aH posH bdefH bH sndt mbne hib by blast
  have hmK1: "snd (hd K1) = maxr1 K1"
    using hm_take[OF _ hmb] K1pre K1NE by metis
  have False using NH[folded K1_def] hmK1 by simp
  thus ?thesis ..
qed

lemma E6_tie_nofire0:
  assumes "fbseg u (c # rest)"
    and "dropWhile (\<lambda>r. fst c < fst r) rest = c1 # rest1"
    and "snd c1 = snd c"
    and "takeWhile (\<lambda>r. fst c < fst r) rest \<noteq> []"
    and "snd (hd (takeWhile (\<lambda>r. fst c < fst r) rest))
         \<noteq> maxr1 (takeWhile (\<lambda>r. fst c < fst r) rest)"
  shows "\<not> pfire (snd c) (nrm (translate (takeWhile (\<lambda>r. fst c < fst r) rest)))"
proof (cases "snd (hd (takeWhile (\<lambda>r. fst c < fst r) rest)) < snd c")
  case True
  have fbK: "fbseg (snd c) (takeWhile (\<lambda>r. fst c < fst r) rest)"
    by (rule dseg_fbseg[OF fbseg_K_dseg[OF assms(1) assms(4)]])
  have "Gterm (snd c) (nrm (translate (takeWhile (\<lambda>r. fst c < fst r) rest))) = {}"
    by (rule Gterm_empty_lowhead[OF fbK assms(4) True])
  thus ?thesis by simp
next
  case False
  hence ge: "snd c \<le> snd (hd (takeWhile (\<lambda>r. fst c < fst r) rest))" by simp
  show ?thesis
    by (rule E6_tie_nofire_high0[OF assms(1) assms(2) assms(3) assms(4) assms(5) ge])
qed

lemma E6_tie_nofire1:
  assumes "fbseg u (c # rest)"
    and "dropWhile (\<lambda>r. fst c < fst r) rest = c1 # rest1"
    and "snd c1 = snd c"
    and "takeWhile (\<lambda>r. fst c1 < fst r) rest1 \<noteq> []"
    and "snd (hd (takeWhile (\<lambda>r. fst c1 < fst r) rest1))
         \<noteq> maxr1 (takeWhile (\<lambda>r. fst c1 < fst r) rest1)"
  shows "\<not> pfire (snd c1) (nrm (translate (takeWhile (\<lambda>r. fst c1 < fst r) rest1)))"
proof (cases "snd (hd (takeWhile (\<lambda>r. fst c1 < fst r) rest1)) < snd c1")
  case True
  have fbT: "fbseg u (c1 # rest1)"
    using fbseg_T_desc[OF assms(1)] assms(2) by simp
  have fbK: "fbseg (snd c1) (takeWhile (\<lambda>r. fst c1 < fst r) rest1)"
    by (rule dseg_fbseg[OF fbseg_K_dseg[OF fbT assms(4)]])
  have "Gterm (snd c1) (nrm (translate (takeWhile (\<lambda>r. fst c1 < fst r) rest1))) = {}"
    by (rule Gterm_empty_lowhead[OF fbK assms(4) True])
  thus ?thesis by simp
next
  case False
  hence ge: "snd c1 \<le> snd (hd (takeWhile (\<lambda>r. fst c1 < fst r) rest1))" by simp
  show ?thesis
    by (rule E6_tie_nofire_high1[OF assms(1) assms(2) assms(3) assms(4) assms(5) ge])
qed

text \<open>(fdlex value core) The sole frozen comparison core of the tie machinery
  under \<open>sibrel6\<close>: on an adjacent tie-sibling pair whose runs diverge at the
  first difference with a lexicographic drop, the projected normalized images
  never invert — with \<^emph>\<open>no\<close> head-maximality and \<^emph>\<open>no\<close> position constraint
  (closure+5: 10500 first-difference pairs, zero violations, including the
  strict \<open>olt\<close> of the raw images; closure+6 shape check 0/1156797).
  Subsumes the former \<open>NT_lexdiff_lt\<close> and \<open>NT_enddrop\<close>.\<close>

lemma NT_tie_fdlex:
  assumes "fbseg u (c # rest)"
    and "dropWhile (\<lambda>r. fst c < fst r) rest = c1 # rest1"
    and "snd c1 = snd c"
    and "takeWhile (\<lambda>r. fst c < fst r) rest = p @ x # r"
    and "takeWhile (\<lambda>r. fst c1 < fst r) rest1 = p @ x1 # r1"
    and "fst x1 < fst x \<or> (fst x1 = fst x \<and> snd x1 < snd x)"
  shows "\<not> olt (proj (snd c) (nrm (translate (takeWhile (\<lambda>r. fst c < fst r) rest))))
               (proj (snd c1) (nrm (translate (takeWhile (\<lambda>r. fst c1 < fst r) rest1))))"
  sorry

lemma NT_tie_resolved:
  assumes A: "fbseg u (c # rest)"
    and T: "dropWhile (\<lambda>r. fst c < fst r) rest = c1 # rest1"
    and tie: "snd c1 = snd c"
  shows "\<not> olt (proj (snd c) (nrm (translate (takeWhile (\<lambda>r. fst c < fst r) rest))))
               (proj (snd c1) (nrm (translate (takeWhile (\<lambda>r. fst c1 < fst r) rest1))))"
proof -
  let ?K = "takeWhile (\<lambda>r. fst c < fst r) rest"
  let ?K1 = "takeWhile (\<lambda>r. fst c1 < fst r) rest1"
  have nfK: "?K \<noteq> [] \<Longrightarrow> \<not> pfire (snd c) (nrm (translate ?K))"
  proof -
    assume Kne: "?K \<noteq> []"
    show "\<not> pfire (snd c) (nrm (translate ?K))"
    proof (cases "snd (hd ?K) = maxr1 ?K")
      case True
      show ?thesis by (rule E6_hdom[OF fbseg_K_dseg[OF A Kne] True])
    next
      case False
      show ?thesis by (rule E6_tie_nofire0[OF A T tie Kne False])
    qed
  qed
  have fbT: "fbseg u (c1 # rest1)"
    using fbseg_T_desc[OF A] T by simp
  have nfK1: "?K1 \<noteq> [] \<Longrightarrow> \<not> pfire (snd c1) (nrm (translate ?K1))"
  proof -
    assume K1ne: "?K1 \<noteq> []"
    show "\<not> pfire (snd c1) (nrm (translate ?K1))"
    proof (cases "snd (hd ?K1) = maxr1 ?K1")
      case True
      show ?thesis by (rule E6_hdom[OF fbseg_K_dseg[OF fbT K1ne] True])
    next
      case False
      show ?thesis by (rule E6_tie_nofire1[OF A T tie K1ne False])
    qed
  qed
  from SIB_shape2[OF A T tie] consider (eq) "?K1 = ?K"
    | (pre) D where "D \<noteq> []" "?K = ?K1 @ D"
    | (fd) p x x1 r r1 where "?K = p @ x # r" "?K1 = p @ x1 # r1"
        "fst x1 < fst x \<or> (fst x1 = fst x \<and> snd x1 < snd x)"
    unfolding sibrel_def by blast
  thus ?thesis
  proof cases
    case eq
    show ?thesis unfolding eq tie using olt_irrefl by blast
  next
    case pre
    have Kne: "?K \<noteq> []" using pre by auto
    have pK: "proj (snd c) (nrm (translate ?K)) = nrm (translate ?K)"
      by (rule proj_nofire[OF nfK[OF Kne]])
    show ?thesis
    proof (cases "?K1 = []")
      case True
      have z: "nrm (translate ?K1) = Z" unfolding True by simp
      have "proj (snd c1) (nrm (translate ?K1)) = Z" unfolding z by (simp add: proj_Z)
      thus ?thesis using not_olt_Z by simp
    next
      case K1ne: False
      have pK1: "proj (snd c1) (nrm (translate ?K1)) = nrm (translate ?K1)"
        by (rule proj_nofire[OF nfK1[OF K1ne]])
      from A obtain pre' pp mid post
        where h: "pre' @ (pp # mid @ (c # rest)) @ post \<in> ST_PS"
        unfolding fbseg_def by blast
      have r: "rest = ?K @ dropWhile (\<lambda>r. fst c < fst r) rest" by simp
      have eqh: "pre' @ (pp # mid @ (c # rest)) @ post
                 = (pre' @ (pp # mid) @ [c]) @ ?K1 @ D
                   @ (dropWhile (\<lambda>r. fst c < fst r) rest @ post)"
        by (subst r) (simp add: pre(2))
      have h2: "(pre' @ (pp # mid) @ [c]) @ ?K1 @ D
                @ (dropWhile (\<lambda>r. fst c < fst r) rest @ post) \<in> ST_PS"
        using h unfolding eqh .
      have "olt (nrm (translate ?K1)) (nrm (translate (?K1 @ D)))"
        by (rule NT_prefix_lt[OF h2 K1ne pre(1)])
      hence "olt (nrm (translate ?K1)) (nrm (translate ?K))"
        using pre(2) by simp
      thus ?thesis unfolding pK pK1
        using olt_total olt_irrefl olt_trans by blast
    qed
  next
    case fd
    show ?thesis by (rule NT_tie_fdlex[OF A T tie fd(1) fd(2) fd(3)])
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
proof (rule ccontr)
  assume cl: "dropWhile (\<lambda>r. fst c0 < fst r) rest \<noteq> []"
  let ?K = "takeWhile (\<lambda>r. fst c0 < fst r) rest"
  have bnd: "\<And>x. x \<in> set (c0 # ?K) \<Longrightarrow> snd x \<le> max u (snd c0)"
    using ginv_dseg_bound[OF assms(1) cl] by blast
  have mx: "max u (snd c0) = snd c0" using assms(2) by simp
  have "maxr1 ?K \<le> snd c0"
    unfolding maxr1_def
  proof (intro Max.boundedI)
    show "finite (snd ` set ?K)" by simp
    show "snd ` set ?K \<noteq> {}" using assms(3) by simp
    show "\<And>s. s \<in> snd ` set ?K \<Longrightarrow> s \<le> snd c0"
      using bnd mx by auto
  qed
  thus False using assms(4) assms(5) by simp
qed

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

text \<open>(TOP) Adjacent top-level trees descend weakly under \<open>nrm\<close>: the later
  tree's image — or the image of any nonempty initial portion of it — is at
  most the earlier full tree's image (closure+2: 967 adjacent root pairs,
  zero violations).  The top-layer analogue of \<open>NT_dom\<close>, previously
  unstated (memo 続27補6).\<close>

lemma TOP_desc:
  assumes "pre @ K @ K1 @ post \<in> ST_PS"
    and "K \<noteq> []" and "K1 \<noteq> []"
    and "fst (hd K) = 0" and "\<forall>x \<in> set (tl K). 0 < fst x"
    and "fst (hd K1) = 0" and "\<forall>x \<in> set (tl K1). 0 < fst x"
  shows "ole (nrm (translate K1)) (nrm (translate K))"
  sorry

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
