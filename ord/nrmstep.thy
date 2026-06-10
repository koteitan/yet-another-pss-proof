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

subsection \<open>Transport of \<open>Einc\<close> through \<open>proj\<close>\<close>

text \<open>Provenance: the pair under transport is the normalized image of an
  all-dominated standard sub-segment and its one-column extension; \<open>u\<close> is the
  enclosing head's row-1 value.  (The transport cases are false for arbitrary
  \<open>Einc\<close> pairs \<dash> e.g.\ a leaf inserted into a region discarded by the
  projection; provenance is what excludes those.)\<close>

definition segprov :: "nat \<Rightarrow> pairseq \<Rightarrow> nat \<times> nat \<Rightarrow> bool" where
  "segprov u S q \<longleftrightarrow> (\<exists>pre pp. pre @ (pp # S) @ [q] \<in> ST_PS
                       \<and> (\<forall>r \<in> set S. fst pp < fst r) \<and> fst pp < fst q \<and> u = snd pp)"

text \<open>The two remaining transport cases (class lemmas; empirically zero
  violations on all standard hosts, with \<open>x\<close> always a leaf in the
  only-extended-fires case).\<close>

lemma projE_iii:
  assumes "segprov u S q"
    and "Einc (nrm (translate S)) (nrm (translate (S @ [q])))"
    and "\<not> pfire u (nrm (translate S))" and "pfire u (nrm (translate (S @ [q])))"
  shows "Einc (nrm (translate S)) (proj u (nrm (translate (S @ [q]))))"
  sorry

lemma projE_ii:
  assumes "segprov u S q"
    and "Einc (nrm (translate S)) (nrm (translate (S @ [q])))"
    and "pfire u (nrm (translate S))" and "pfire u (nrm (translate (S @ [q])))"
  shows "Einc (proj u (nrm (translate S))) (proj u (nrm (translate (S @ [q]))))"
  sorry

lemma projE:
  assumes R: "Einc (nrm (translate S)) (nrm (translate (S @ [q])))"
    and PV: "segprov u S q"
  shows "Einc (proj u (nrm (translate S))) (proj u (nrm (translate (S @ [q]))))"
proof (cases "pfire u (nrm (translate S))")
  case xf: True
  have x'f: "pfire u (nrm (translate (S @ [q])))"
  proof -
    obtain g where "g \<in> Gterm u (nrm (translate S))" "\<not> olt g (nrm (translate S))"
      using xf by blast
    from fire_transport[OF R this] show ?thesis .
  qed
  show ?thesis by (rule projE_ii[OF PV R xf x'f])
next
  case xnf: False
  have px: "proj u (nrm (translate S)) = nrm (translate S)" by (rule proj_nofire[OF xnf])
  show ?thesis
  proof (cases "pfire u (nrm (translate (S @ [q])))")
    case x'f: True
    show ?thesis unfolding px by (rule projE_iii[OF PV R xnf x'f])
  next
    case x'nf: False
    have px': "proj u (nrm (translate (S @ [q]))) = nrm (translate (S @ [q]))"
      by (rule proj_nofire[OF x'nf])
    show ?thesis unfolding px px' by (rule R)
  qed
qed

subsection \<open>Row-0 step discipline of contiguous sublists\<close>

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

subsection \<open>Standardness supplies the bundle\<close>

text \<open>The two remaining leaf obligations of the structural bundle against a
  standard host: the appended column's row-1 value does not exceed the head's
  at a new-summand position (sibling tops), and the no-absorb pair at tail
  positions (head preservation of \<open>nrm\<close> + sibling order).\<close>

text \<open>With equal row-0 values, the appended column is the next summand after
  \<open>p\<close>'s block at the same level of the host's translation; the \<open>cnf\<close> discipline
  of standard forms (non-increasing summand heads) gives the row-1 comparison.\<close>

lemma STS_A_aux:
  "\<forall>r\<in>set rest. fst p < fst r \<Longrightarrow> fst q = fst p \<Longrightarrow>
   cnf (translate (pre @ (p # rest) @ [q])) \<Longrightarrow> snd q \<le> snd p"
proof (induct pre rule: length_induct)
  case (1 pre)
  note IH = 1(1) and dom = 1(2) and fq = 1(3) and CNF = 1(4)
  show ?case
  proof (cases pre)
    case Nil
    have Tc: "[q] = [] \<or> \<not> fst p < fst (hd [q])" using fq by simp
    have e: "translate ((p # rest) @ [q])
              = P (snd p) (translate rest) (translate [q])"
      using translate_block_append[of rest "fst p" "[q]" "snd p"] dom Tc
      by (simp add: append.assoc)
    have e2: "translate [q] = P (snd q) Z Z"
      by (simp only: translate.simps(2) takeWhile.simps(1) dropWhile.simps(1)
                     translate.simps(1))
    have c: "cnf (P (snd p) (translate rest) (P (snd q) Z Z))"
      using CNF unfolding Nil append_Nil e e2 .
    have nlt: "\<not> (P (snd p) (translate rest) Z <o P (snd q) Z Z)"
      using c by simp
    show ?thesis
    proof (rule ccontr)
      assume "\<not> snd q \<le> snd p"
      hence "snd p < snd q" by simp
      hence "P (snd p) (translate rest) Z <o P (snd q) Z Z" by simp
      thus False using nlt by blast
    qed
  next
    case (Cons e pre')
    let ?Pe = "\<lambda>r. fst e < fst r"
    let ?tail = "pre' @ (p # rest) @ [q]"
    have et: "translate (pre @ (p # rest) @ [q])
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
      have allT: "\<forall>x \<in> set ?tail. ?Pe x" using all segP by auto
      have tw: "takeWhile ?Pe ?tail = ?tail"
        using allT by (simp add: takeWhile_eq_all_conv)
      have cnfK: "cnf (translate ?tail)"
      proof -
        have "cnf (P (snd e) (translate ?tail) (translate (dropWhile ?Pe ?tail)))"
          using CNF unfolding et tw .
        thus ?thesis by (cases "translate (dropWhile ?Pe ?tail)") auto
      qed
      have lp: "length pre' < length pre" by (simp add: Cons)
      show ?thesis using IH[rule_format, OF lp] dom fq cnfK by blast
    next
      case ncut: False
      have Dform: "\<exists>pre''. dropWhile ?Pe ?tail = pre'' @ (p # rest) @ [q]
                            \<and> length pre'' < length pre"
      proof (cases "\<forall>x \<in> set pre'. ?Pe x")
        case True
        hence "\<not> fst e < fst p" using ncut by blast
        hence "dropWhile ?Pe ((p # rest) @ [q]) = (p # rest) @ [q]" by simp
        hence "dropWhile ?Pe ?tail = (p # rest) @ [q]"
          using True by (simp add: dropWhile_append2)
        thus ?thesis unfolding Cons by (intro exI[of _ "[]"]) simp
      next
        case False
        then obtain w where w: "w \<in> set pre'" "\<not> ?Pe w" by blast
        have "dropWhile ?Pe ?tail = dropWhile ?Pe pre' @ (p # rest) @ [q]"
          using w by (simp add: dropWhile_append1)
        moreover have "length (dropWhile ?Pe pre') < length pre"
          unfolding Cons using length_dropWhile_le[of ?Pe pre']
          by (simp add: le_imp_less_Suc)
        ultimately show ?thesis by blast
      qed
      obtain pre'' where D: "dropWhile ?Pe ?tail = pre'' @ (p # rest) @ [q]"
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
  assumes "pre @ (p # rest) @ [q] \<in> ST_PS"
    and "dropWhile (\<lambda>r. fst p < fst r) rest = []"
    and "fst q = fst p"
  shows "snd q \<le> snd p"
proof -
  have dom: "\<forall>r\<in>set rest. fst p < fst r"
    using assms(2) by (simp add: dropWhile_eq_Nil_conv)
  have "cnf (translate (pre @ (p # rest) @ [q]))"
    using cnf_ST_PS[OF assms(1)] .
  thus ?thesis using STS_A_aux dom assms(3) by blast
qed

lemma STS_B:
  assumes "pre @ (p # rest) @ [q] \<in> ST_PS"
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
  "pre @ C @ [q] \<in> ST_PS \<Longrightarrow> C \<noteq> [] \<Longrightarrow> fst (hd C) \<le> fst q \<Longrightarrow>
   \<forall>x \<in> set C. fst (hd C) \<le> fst x \<Longrightarrow> snocokS C q"
proof (induct C arbitrary: pre rule: length_induct)
  case (1 C)
  note IH = 1(1) and host = 1(2) and ne = 1(3) and INV = 1(4) and INV2 = 1(5)
  obtain p rest where C: "C = p # rest" using ne by (cases C) auto
  have stepsC: "stepsok (p # rest)"
  proof -
    have "blockok 0 (pre @ (p # rest) @ [q])"
      using blockok_ST_PS host[unfolded C] by blast
    hence "stepsok (pre @ (p # rest) @ [q])" by (rule blockok_stepsok)
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
        have host2: "(pre @ [p]) @ rest @ [q] \<in> ST_PS"
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
        show ?thesis by (rule projE[OF E2 PV])
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
    have host': "(pre @ [p] @ takeWhile (\<lambda>r. fst p < fst r) rest) @ ?T @ [q] \<in> ST_PS"
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
  assumes H: "pre @ (p # rest) @ [q] \<in> ST_PS"
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
    using ST_snocokS_gen[of pre "p # rest" q] H hd0 inv2 by simp
  have unfA: "snocokS (p # rest) q \<longleftrightarrow>
        Einc (proj (snd p) (nrm (translate rest)))
             (proj (snd p) (nrm (translate (rest @ [q]))))"
    by (simp only: snocokS.simps if_P[OF T] if_P[OF Q])
  show ?thesis using S unfolding unfA using Einc_olt by blast
qed

lemma ST_snocok_gen:
  "pre @ C @ [q] \<in> ST_PS \<Longrightarrow> C \<noteq> [] \<Longrightarrow> snocok C q"
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
    have host': "(pre @ [p] @ takeWhile (\<lambda>r. fst p < fst r) rest) @ ?T @ [q] \<in> ST_PS"
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

lemma ST_snocok:
  assumes "C @ [q] \<in> ST_PS" and "C \<noteq> []"
  shows "snocok C q"
  using ST_snocok_gen[of "[]" C q] assms by simp

theorem nrm_snoc:
  assumes "C @ [p] \<in> ST_PS" and "C \<noteq> []"
  shows "olt (nrm (translate C)) (nrm (translate (C @ [p])))"
  by (rule nrm_snoc_seg[OF ST_snocok[OF assms] assms(2)])

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
