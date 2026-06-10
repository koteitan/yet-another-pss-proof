theory nrmstep
  imports nrm
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

lemma ST_snoc_C:
  assumes "pre @ (p # rest) @ [q] \<in> ST_PS"
    and "dropWhile (\<lambda>r. fst p < fst r) rest = []"
    and "fst p < fst q"
  shows "olt (proj (snd p) (nrm (translate rest)))
             (proj (snd p) (nrm (translate (rest @ [q]))))"
  sorry

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
