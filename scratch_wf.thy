theory scratch_wf
  imports buchholz
begin

text \<open>\<^bold>\<open>Multi-\<open>\<vartheta>\<^sub>n\<close> well-foundedness, corrected hierarchy (memo 続38\<dash>39).\<close>

  The previous \<^const>\<open>Mn\<close>/\<^const>\<open>AccB\<close>/\<^const>\<open>Acc\<close> stratified by \<^const>\<open>gnd\<close>, which
  uses the convention \<open>FCset = {} \<Longrightarrow> 0\<close>.  That collapses Towsner's countable
  base level \<open>-\<infinity>\<close> into level \<open>0\<close> (\<open>\<Omega>\<^sub>0\<close>), making the hierarchy \<^emph>\<open>degenerate on the
  \<open>\<Omega>\<close>-free fragment\<close> (every \<open>\<Omega>\<close>-free term lands at level \<open>0\<close> with only \<open>K\<^sub>0\<close> control,
  no real stratification).

  Here we keep the countable terms (\<open>FCset = {}\<close>) as a genuine separate base
  \<^const>\<open>cntbl\<close> (Towsner \<open>M\<^bsub>-\<infinity>\<^esub>\<close>), and stratify the \<^emph>\<open>cardinal\<close> terms by the ground.

  This is a development scratch (not in \<^file>\<open>ROOT\<close>); the hard closure lemmas
  (Towsner 3.8\<dash>3.12, multi-\<open>\<vartheta>\<^sub>n\<close>) are built incrementally and verified by build
  before integration into \<^theory>\<open>YAPSS.buchholz\<close>.\<close>

subsection \<open>The countable base (Towsner \<open>M\<^bsub>-\<infinity>\<^esub>\<close>)\<close>

text \<open>\<open>cntbl a\<close>: no free cardinal occurs (\<open>FCset a = {}\<close>).  This is broader than
  \<^const>\<open>omfree\<close> (e.g. \<open>\<vartheta>\<^bsub>3\<^esub> \<Omega>\<^bsub>5\<^esub>\<close> is countable but not \<open>\<Omega>\<close>-free), but on the
  \<^emph>\<open>well-formed nonnegative\<close> target the two coincide on the embedding image.\<close>

definition cntbl :: "ot \<Rightarrow> bool" where
  "cntbl a \<longleftrightarrow> FCset a = {}"

lemma cntbl_omfree: "omfree a \<Longrightarrow> cntbl a"
  by (simp add: cntbl_def)

lemma cntbl_Su_iff: "cntbl (Su xs) \<longleftrightarrow> (\<forall>x \<in> set xs. cntbl x)"
  by (auto simp: cntbl_def)

lemma cntbl_Th: "cntbl (Th n a) \<longleftrightarrow> {m \<in> FCset a. m < n} = {}"
  by (simp add: cntbl_def)

text \<open>The countable base set and its accessible part (Towsner \<open>Acc\<^bsub>-\<infinity>\<^esub>\<close>).\<close>

definition Mbot :: "ot set" where
  "Mbot = {a. wfo a \<and> nneg a \<and> omfree a}"

text \<open>The order restricted to \<^const>\<open>Mbot\<close> is exactly \<^const>\<open>oltRwF\<close>: \<^const>\<open>omfree\<close> is
  preserved downward, so the accessible part of the base \<^emph>\<open>is\<close> the genuine
  accessibility we want.  (The base level alone is therefore tautological; the
  well-foundedness content lives in the \<open>\<Omega>\<close>-scaffolded higher levels and the
  master/closure lemmas that place every \<open>\<Omega>\<close>-free term into the base.)\<close>

lemma R_Mbot_eq_oltRwF: "{(x,y). x <\<^sub>o y \<and> x \<in> Mbot \<and> y \<in> Mbot} = oltRwF"
  by (auto simp: Mbot_def)

lemma Abot_subset_acc: "Awf Mbot \<subseteq> Wellfounded.acc oltRwF"
  using Awf_acc by (auto simp: Awf_def R_Mbot_eq_oltRwF)

subsection \<open>Sanity: the base reduction is tautological (documents the gap)\<close>

text \<open>Membership \<open>a \<in> Awf Mbot\<close> is \<^emph>\<open>equivalent\<close> to \<open>a \<in> acc oltRwF\<close> for \<open>\<Omega>\<close>-free
  \<open>a\<close> \<dash> so the base gives no new accessibility.  This makes precise why the
  hard work cannot be avoided at the base level.\<close>

lemma Abot_iff_acc:
  assumes "wfo a" "nneg a" "omfree a"
  shows "a \<in> Awf Mbot \<longleftrightarrow> a \<in> Wellfounded.acc oltRwF"
proof
  assume "a \<in> Awf Mbot" thus "a \<in> Wellfounded.acc oltRwF" using Abot_subset_acc by blast
next
  assume acc: "a \<in> Wellfounded.acc oltRwF"
  have "a \<in> Mbot" using assms by (simp add: Mbot_def)
  moreover have "a \<in> Wellfounded.acc {(x,y). x <\<^sub>o y \<and> x \<in> Mbot \<and> y \<in> Mbot}"
    using acc by (simp add: R_Mbot_eq_oltRwF)
  ultimately show "a \<in> Awf Mbot" by (simp add: Awf_def)
qed


section \<open>Implementation plan for the multi-\<open>\<vartheta>\<^sub>n\<close> collapsing WF (next phase)\<close>

text \<open>\<^bold>\<open>Established facts (this session, memo 続38\<dash>39), to avoid re-deriving:\<close>

  \<^enum> The residual of @{thm [source] buchholz.L_ThF} \<dash>
    \<open>r \<ge> n, h \<in> acc, omfree/wfo/nneg h, p < r, Kn p h \<subseteq> acc \<Longrightarrow> Th r h \<in> acc\<close> \<dash>
    is the \<^emph>\<open>irreducible core\<close> of Buchholz's \<open>\<psi>\<^sub>n\<close> well-ordering theorem.  It is a
    recursive instance of \<open>L_ThF\<close> at level \<open>r \<ge> n\<close> with a \<^emph>\<open>buried\<close> argument \<open>h\<close>
    unrelated to \<open>d\<close> by \<open><\<^sub>o\<close>.  \<^bold>\<open>No\<close> elementary induction (on level \<open>k\<close>, on
    \<open>acc\<close>-rank of the argument, on \<^const>\<open>size\<close>, on term structure, or any lexicographic
    combination) bounds it \<dash> all refuted this session.  Concrete witness that
    predecessors carry unbounded subscripts: \<open>\<vartheta>\<^bsub>0\<^esub>(\<vartheta>\<^bsub>100\<^esub> 0) <\<^sub>o \<vartheta>\<^bsub>1\<^esub> 0\<close>.

  \<^enum> \<^bold>\<open>Downward-closure is FALSE\<close>: the critical-subterm control set is not
    \<open><\<^sub>o\<close>-downward closed.  Witness \<open>\<vartheta>\<^bsub>0\<^esub> 0 <\<^sub>o \<vartheta>\<^bsub>5\<^esub> 0\<close> with \<open>Kn 0 (\<vartheta>\<^bsub>0\<^esub> 0) = {\<vartheta>\<^bsub>0\<^esub> 0}\<close>
    but \<open>Kn 0 (\<vartheta>\<^bsub>5\<^esub> 0) = {}\<close>.  So the naive "connection via downward closure" route
    (for both the old \<^const>\<open>Mn\<close> and any \<open>Th\<close>-subscript variant) is dead.

  \<^enum> \<^bold>\<open>The \<open>\<Omega>\<close> (\<^const>\<open>Om\<close>) scaffolding is essential.\<close>  The pure-\<open>\<vartheta>\<close> (\<open>\<Omega>\<close>-free)
    construction is circular at the base: a principal \<open>\<vartheta>\<^bsub>j\<^esub> g\<close> has
    \<open>Kn n (\<vartheta>\<^bsub>j\<^esub> g) = {\<vartheta>\<^bsub>j\<^esub> g}\<close> for \<open>n \<ge> j\<close>, so it can never be "controlled by lower
    levels" \<dash> it would require itself.  Towsner/Buchholz break this by stratifying
    by the \<^emph>\<open>cardinal ground\<close>, with \<open>\<Omega>\<^sub>n\<close> as genuine scaffolding terms.

  \<^enum> \<^bold>\<open>Actionable bug\<close>: @{const FC}/@{const gnd} use \<open>FCset = {} \<Longrightarrow> 0\<close>, collapsing
    Towsner's countable base \<open>-\<infinity>\<close> into level \<open>0\<close> (\<open>\<Omega>\<^sub>0\<close>).  The corrected hierarchy
    needs a genuine \<open>-\<infinity>\<close> (e.g. \<^typ>\<open>int option\<close> ground, \<open>None = -\<infinity>\<close>), so that
    \<open>\<Omega>\<close>-free terms sit at the base \<^const>\<open>Mbot\<close> and the \<open>\<Omega>\<^sub>n\<close>-levels stratify the rest.\<close>

text \<open>\<^bold>\<open>Lemma sequence to implement (Towsner \<section>3.2, absolute multi-\<open>\<vartheta>\<^sub>n\<close>):\<close>

  Work in the \<^emph>\<open>full\<close> order \<^const>\<open>oltRw\<close> (where @{thm [source] shift_olt} /
  @{thm [source] acc_shift} are clean automorphisms \<dash> the \<open>\<Omega>\<close>-scaffolding lives
  here), extracting the \<^const>\<open>nneg\<close>/\<open>\<Omega>\<close>-free target only at the end.

  \<^enum> \<^bold>\<open>Ground with \<open>-\<infinity>\<close>\<close>: \<open>grd a :: int option\<close>, \<open>grd a = (if FCset a = {} then None
     else Some (Min (FCset a)))\<close>; reorder \<open>None < Some _\<close>.  Re-prove \<open>grd_shift\<close>.

  \<^enum> \<^bold>\<open>Corrected level family\<close> (\<open>n :: nat\<close>, plus the base \<^const>\<open>Mbot\<close>):
     \<open>Mlv n prev = {a. isH a \<and> wfo a \<and> normd a \<and> (grd a = None \<or> - int n \<le> the (grd a))
                      \<and> (\<forall>\<gamma> \<in> Klt a. norm \<gamma> \<in> prev)}\<close>, with
     \<open>prev = Bst n = Awf Mbot \<union> (\<Union>i<n. Acc i)\<close>.  \<^bold>\<open>Key fix vs. old \<^const>\<open>Mn\<close>\<close>: the
     critical-subterm control allows landing in \<^const>\<open>Mbot\<close>'s accessible part
     (countable criticals), not only the \<open>\<Omega>\<close>-levels.

  \<^enum> \<^bold>\<open>3.8 sum closure\<close>: \<open>m \<le> n \<Longrightarrow> \<alpha> \<in> Acc m \<Longrightarrow> \<beta> \<in> Acc n \<Longrightarrow> shift\<dots>\<alpha> # \<beta> \<in> Acc n\<close>.
     (Most of this is already free via @{thm [source] acc_of_bag_elemsF} once the
     membership side-conditions are discharged.)

  \<^enum> \<^bold>\<open>3.10 collapse, same level\<close>: \<open>\<alpha> \<in> Acc n \<Longrightarrow> \<vartheta> (shift\<dots>\<alpha>) \<in> Acc n\<close>.  Main
     induction on \<open>\<alpha> \<in> Acc n\<close>; inner structural induction on the predecessor \<open>\<gamma>\<close>.
     The two predecessor sub-cases are exactly the already-green \<open>dom_acc\<close> (Towsner
     Case 2) and \<open>p = r \<and> e <\<^sub>o d\<close> (Case 1, via \<open>accIH\<close>).

  \<^enum> \<^bold>\<open>3.11 level drop\<close>: \<open>\<alpha> \<in> Acc n \<Longrightarrow> (\<vartheta>\<alpha>)* \<in> (\<Union>m<n. Acc m)\<close>.  \<^bold>\<open>This is where the
     multi-\<open>\<vartheta>\<^sub>n\<close> \<open>p < r\<close> cross-subscript case is discharged\<close> \<dash> the buried high
     collapse is shifted (\<open>\<Omega>\<close>-scaffold) to a lower ground and lands in a lower
     \<open>Acc m\<close>, available by the main induction on the level.  This is the genuine
     content absent from the single-\<open>\<vartheta>\<close> \<section>3.2 proof.

  \<^enum> \<^bold>\<open>3.12 master\<close>: structural induction on the term \<dash> \<open>Su\<close> via 3.8,
     \<open>Th\<close> via 3.10/3.11, \<open>Om\<close> as base \<dash> giving \<open>a* \<in> Acc (G a*)\<close> for all \<open>a\<close>.

  \<^enum> \<^bold>\<open>Connection\<close>: every \<open>\<Omega>\<close>-free \<open>a\<close> has \<open>grd = None\<close> (base), so master places it in
     \<^const>\<open>Mbot\<close>'s accessible part; with @{thm [source] Abot_iff_acc} this yields
     \<open>a \<in> acc oltRwF\<close>, i.e. @{thm [source] buchholz.masterF} without the residual.
     Then @{thm [source] buchholz.wf_oltRwF} stands, and \<open>op_NF\<close>/\<open>olt_trans\<close> (the
     "already-solved" lex/standard-form parts) finish \<open>wf Rnf\<close>.\<close>

end
