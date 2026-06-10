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
     \<or> (snd (hd K) = maxr1 K \<and> snd (hd K1) = maxr1 K1 \<and>
        (\<exists>p x x1 r r1. K = p @ x # r \<and> K1 = p @ x1 # r1 \<and>
           ((fst x1 = fst x \<and> snd x1 < snd x)
            \<or> (fst x1 < fst x \<and> snd x1 = snd x))))"

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

lemma sibrel_trunc:
  assumes R: "sibrel K K1"
  shows "sibrel K (take s K1)"
proof (cases "length K1 \<le> s")
  case True
  thus ?thesis using R by simp
next
  case False
  hence sl: "s < length K1" by simp
  have K1ne: "K1 \<noteq> []" using sl by auto
  have dec: "K1 = take s K1 @ drop s K1" by simp
  have dne: "drop s K1 \<noteq> []" using sl by simp
  from R show ?thesis unfolding sibrel_def
  proof (elim disjE)
    assume "K1 = K"
    hence "K = take s K1 @ drop s K1" using dec by simp
    thus "take s K1 = K \<or> (\<exists>D. D \<noteq> [] \<and> K = take s K1 @ D)
        \<or> (snd (hd K) = maxr1 K \<and> snd (hd (take s K1)) = maxr1 (take s K1) \<and>
           (\<exists>p x x1 r r1. K = p @ x # r \<and> take s K1 = p @ x1 # r1 \<and>
              ((fst x1 = fst x \<and> snd x1 < snd x)
               \<or> (fst x1 < fst x \<and> snd x1 = snd x))))"
      using dne by blast
  next
    assume "\<exists>D. D \<noteq> [] \<and> K = K1 @ D"
    then obtain D where D: "D \<noteq> []" "K = K1 @ D" by blast
    have "K = take s K1 @ (drop s K1 @ D)"
      using D(2) dec by (metis append.assoc)
    thus "take s K1 = K \<or> (\<exists>D. D \<noteq> [] \<and> K = take s K1 @ D)
        \<or> (snd (hd K) = maxr1 K \<and> snd (hd (take s K1)) = maxr1 (take s K1) \<and>
           (\<exists>p x x1 r r1. K = p @ x # r \<and> take s K1 = p @ x1 # r1 \<and>
              ((fst x1 = fst x \<and> snd x1 < snd x)
               \<or> (fst x1 < fst x \<and> snd x1 = snd x))))"
      using dne by blast
  next
    assume L: "snd (hd K) = maxr1 K \<and> snd (hd K1) = maxr1 K1 \<and>
        (\<exists>p x x1 r r1. K = p @ x # r \<and> K1 = p @ x1 # r1 \<and>
           ((fst x1 = fst x \<and> snd x1 < snd x)
            \<or> (fst x1 < fst x \<and> snd x1 = snd x)))"
    then obtain p x x1 r r1 where w: "K = p @ x # r" "K1 = p @ x1 # r1"
      and lx: "(fst x1 = fst x \<and> snd x1 < snd x)
               \<or> (fst x1 < fst x \<and> snd x1 = snd x)" by blast
    have hmK: "snd (hd K) = maxr1 K" and hmK1: "snd (hd K1) = maxr1 K1"
      using L by blast+
    show "take s K1 = K \<or> (\<exists>D. D \<noteq> [] \<and> K = take s K1 @ D)
        \<or> (snd (hd K) = maxr1 K \<and> snd (hd (take s K1)) = maxr1 (take s K1) \<and>
           (\<exists>p x x1 r r1. K = p @ x # r \<and> take s K1 = p @ x1 # r1 \<and>
              ((fst x1 = fst x \<and> snd x1 < snd x)
               \<or> (fst x1 < fst x \<and> snd x1 = snd x))))"
    proof (cases "s \<le> length p")
      case True
      have tp: "take s K1 = take s p" unfolding w(2) using True by simp
      have tpK: "take s K1 = take s K" unfolding tp w(1) using True by simp
      have "K = take s K1 @ drop s K" using tpK by (metis append_take_drop_id)
      moreover have "drop s K \<noteq> []"
        unfolding w(1) using True by simp
      ultimately show ?thesis by blast
    next
      case False
      hence sp: "length p < s" by simp
      have t1: "take s K1 = p @ x1 # take (s - length p - 1) r1"
      proof -
        have "take s K1 = take s p @ take (s - length p) (x1 # r1)"
          unfolding w(2) by (simp add: take_append)
        moreover have "take s p = p" using sp by simp
        moreover have "take (s - length p) (x1 # r1)
                       = x1 # take (s - length p - 1) r1"
          using sp by (cases "s - length p") auto
        ultimately show ?thesis by simp
      qed
      have ne: "take s K1 \<noteq> []" unfolding t1 by simp
      have hm1: "snd (hd (take s K1)) = maxr1 (take s K1)"
        by (rule hm_take[OF ne hmK1])
      show ?thesis using hmK hm1 w(1) t1 lx by blast
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
    | (lx) p x x1 r r1 where "K = p @ x # r" "K2 = p @ x1 # r1"
        "(fst x1 = fst x \<and> snd x1 < snd x) \<or> (fst x1 < fst x \<and> snd x1 = snd x)"
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
    case lx
    have pK: "length p < length K" unfolding lx(1) by simp
    have "K ! length p = x" unfolding lx(1) by simp
    moreover have "K2 ! length p = x1" unfolding lx(2) by simp
    moreover have "K2 ! length p = K ! length p"
      unfolding E using pK by (simp add: nth_append)
    ultimately have "x1 = x" by simp
    thus False using lx(3) by auto
  qed
qed

lemma sibrel_ascent:
  assumes R: "sibrel K K2"
    and dK: "K = p @ x # r" and dK2: "K2 = p @ x1 # r1"
    and ne: "x1 \<noteq> x"
    and asc: "\<not> ((fst x1 = fst x \<and> snd x1 < snd x) \<or> (fst x1 < fst x \<and> snd x1 = snd x))"
  shows False
proof -
  have nthK: "K ! length p = x" unfolding dK by simp
  have nthK2: "K2 ! length p = x1" unfolding dK2 by simp
  have pK: "length p < length K" unfolding dK by simp
  have pK2: "length p < length K2" unfolding dK2 by simp
  from R consider (eq) "K2 = K"
    | (pre) D where "D \<noteq> []" "K = K2 @ D"
    | (lx) p' x' x1' r' r1' where "K = p' @ x' # r'" "K2 = p' @ x1' # r1'"
        "(fst x1' = fst x' \<and> snd x1' < snd x') \<or> (fst x1' < fst x' \<and> snd x1' = snd x')"
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
    case lx
    have nthK': "K ! length p' = x'" unfolding lx(1) by simp
    have nthK2': "K2 ! length p' = x1'" unfolding lx(2) by simp
    have pK': "length p' < length K" unfolding lx(1) by simp
    have pK2': "length p' < length K2" unfolding lx(2) by simp
    have x1x': "x1' \<noteq> x'" using lx(3) by auto
    consider (less) "length p' < length p" | (same) "length p' = length p"
      | (more) "length p < length p'" by linarith
    thus False
    proof cases
      case same
      have "x' = x" using nthK nthK' same by simp
      moreover have "x1' = x1" using nthK2 nthK2' same by simp
      ultimately show False using lx(3) asc by simp
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
        unfolding lx(1) using more by (simp add: nth_append)
      moreover have "K2 ! length p = p' ! length p"
        unfolding lx(2) using more by (simp add: nth_append)
      ultimately have "x = x1" using nthK nthK2 by simp
      thus False using ne by simp
    qed
  qed
qed

text \<open>Pure seam ingredients: the block head is the strict row-0 minimum of
  the block (via the row-0 ancestor chain), and runs are unchanged by an
  append unless they were open.\<close>

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
    | (LX) p x x1 r r1 where
        "snd (hd K) = maxr1 K" "snd (hd K1) = maxr1 K1"
        "K = p @ x # r" "K1 = p @ x1 # r1"
        "(fst x1 = fst x \<and> snd x1 < snd x) \<or> (fst x1 < fst x \<and> snd x1 = snd x)"
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
    case LX
    have Kne: "K \<noteq> []" and K1ne: "K1 \<noteq> []" unfolding LX(3) LX(4) by simp_all
    have hm: "snd (hd (shf s K)) = maxr1 (shf s K)"
      using LX(1) Kne by (simp add: shf_hd shf_maxr1)
    have hm1: "snd (hd (shf s K1)) = maxr1 (shf s K1)"
      using LX(2) K1ne by (simp add: shf_hd shf_maxr1)
    have d1: "shf s K = shf s p @ (fst x + s, snd x) # shf s r"
      unfolding LX(3) shf_def by simp
    have d2: "shf s K1 = shf s p @ (fst x1 + s, snd x1) # shf s r1"
      unfolding LX(4) shf_def by simp
    have lxs: "(fst (fst x1 + s, snd x1) = fst (fst x + s, snd x)
                \<and> snd (fst x1 + s, snd x1) < snd (fst x + s, snd x))
               \<or> (fst (fst x1 + s, snd x1) < fst (fst x + s, snd x)
                \<and> snd (fst x1 + s, snd x1) = snd (fst x + s, snd x))"
      using LX(5) by auto
    show ?thesis unfolding sibrel_def using hm hm1 d1 d2 lxs by blast
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
          \<not> ((fst (M ! j1) = fst x \<and> snd (M ! j1) < snd x)
             \<or> (fst (M ! j1) < fst x \<and> snd (M ! j1) = snd x))"
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
  sorry

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

lemma E6_tie_nofire0:
  assumes "fbseg u (c # rest)"
    and "dropWhile (\<lambda>r. fst c < fst r) rest = c1 # rest1"
    and "snd c1 = snd c"
    and "takeWhile (\<lambda>r. fst c < fst r) rest \<noteq> []"
    and "snd (hd (takeWhile (\<lambda>r. fst c < fst r) rest))
         \<noteq> maxr1 (takeWhile (\<lambda>r. fst c < fst r) rest)"
  shows "\<not> pfire (snd c) (nrm (translate (takeWhile (\<lambda>r. fst c < fst r) rest)))"
  sorry

lemma E6_tie_nofire1:
  assumes "fbseg u (c # rest)"
    and "dropWhile (\<lambda>r. fst c < fst r) rest = c1 # rest1"
    and "snd c1 = snd c"
    and "takeWhile (\<lambda>r. fst c1 < fst r) rest1 \<noteq> []"
    and "snd (hd (takeWhile (\<lambda>r. fst c1 < fst r) rest1))
         \<noteq> maxr1 (takeWhile (\<lambda>r. fst c1 < fst r) rest1)"
  shows "\<not> pfire (snd c1) (nrm (translate (takeWhile (\<lambda>r. fst c1 < fst r) rest1)))"
  sorry

text \<open>(lexdiff value lemma) For head-maximal dominated runs with equal head
  level, a first-difference descent (equal level and smaller row 1, or
  smaller level and equal row 1) strictly decreases the normalised value.
  (Empirically: 1164974 cross-host pairs of truncated dominated runs,
  zero failures.)\<close>

lemma NT_lexdiff_lt:
  assumes "dseg u K" and "dseg u1 K1"
    and "snd (hd K) = maxr1 K" and "snd (hd K1) = maxr1 K1"
    and "fst (hd K1) = fst (hd K)"
    and "K = p @ x # r" and "K1 = p @ x1 # r1"
    and "(fst x1 = fst x \<and> snd x1 < snd x) \<or> (fst x1 < fst x \<and> snd x1 = snd x)"
  shows "olt (nrm (translate K1)) (nrm (translate K))"
  sorry

text \<open>Resolution of \<open>NT_tie\<close> from \<open>SIB_shape2\<close> (repaired, memo 続29): equal
  runs give equal projections; a proper prefix is strictly below by prefix
  monotonicity; a first-difference descent is strictly below by
  \<open>NT_lexdiff_lt\<close>; projections are trivial by head-max no-fire (\<open>E6_hdom\<close>)
  or tie no-fire (\<open>E6_tie_nofire0/1\<close>).  (Same stratified placement as the
  other resolved lemmas.)\<close>

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
  from SIB_shape2[OF A T tie] show ?thesis
    unfolding sibrel_def
  proof (elim disjE)
    assume eq: "?K1 = ?K"
    show ?thesis unfolding eq tie using olt_irrefl by blast
  next
    assume "\<exists>D. D \<noteq> [] \<and> ?K = ?K1 @ D"
    then obtain D where D: "D \<noteq> []" "?K = ?K1 @ D" by blast
    have Kne: "?K \<noteq> []" using D by auto
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
  next
    assume L: "snd (hd ?K) = maxr1 ?K \<and> snd (hd ?K1) = maxr1 ?K1 \<and>
        (\<exists>p x x1 r r1. ?K = p @ x # r \<and> ?K1 = p @ x1 # r1 \<and>
           ((fst x1 = fst x \<and> snd x1 < snd x)
            \<or> (fst x1 < fst x \<and> snd x1 = snd x)))"
    then obtain p x x1 r r1 where w1: "?K = p @ x # r" and w2: "?K1 = p @ x1 # r1"
      and lx: "(fst x1 = fst x \<and> snd x1 < snd x)
               \<or> (fst x1 < fst x \<and> snd x1 = snd x)" by blast
    have hmK: "snd (hd ?K) = maxr1 ?K" and hmK1: "snd (hd ?K1) = maxr1 ?K1"
      using L by blast+
    have Kne: "?K \<noteq> []" unfolding w1 by simp
    have K1ne: "?K1 \<noteq> []" unfolding w2 by simp
    have dsK: "dseg (snd c) ?K" by (rule fbseg_K_dseg[OF A Kne])
    have dsK1: "dseg (snd c1) ?K1" by (rule fbseg_K_dseg[OF fbT K1ne])
    have pK: "proj (snd c) (nrm (translate ?K)) = nrm (translate ?K)"
      by (rule proj_nofire[OF E6_hdom[OF dsK hmK]])
    have pK1: "proj (snd c1) (nrm (translate ?K1)) = nrm (translate ?K1)"
      by (rule proj_nofire[OF E6_hdom[OF dsK1 hmK1]])
    have lvl: "fst c1 = fst c" by (rule fbseg_hd_level[OF A T])
    have lvlK: "fst (hd ?K) = Suc (fst c)"
      by (rule fbseg_run_hd_level[OF A Kne])
    have lvlK1: "fst (hd ?K1) = Suc (fst c1)"
      by (rule fbseg_run_hd_level[OF fbT K1ne])
    have hdlv: "fst (hd ?K1) = fst (hd ?K)" using lvlK lvlK1 lvl by simp
    have "olt (nrm (translate ?K1)) (nrm (translate ?K))"
      by (rule NT_lexdiff_lt[OF dsK dsK1 hmK hmK1 hdlv w1 w2 lx])
    thus ?thesis unfolding pK pK1
      using olt_total olt_irrefl olt_trans by blast
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
