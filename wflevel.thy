theory wflevel
  imports wo
begin

section \<open>Well-foundedness on principal terms: the distinguished-set hierarchy\<close>

text \<open>
  This is the remaining core obligation \<^prop>\<open>wf principalR\<close> (Towsner,
  \<^emph>\<open>Polymorphic Ordinal Notations\<close> \<section>3.2, Lemmas 3.8\<dash>3.12), rendered for the
  absolute (non-polymorphic) system of \<^theory>\<open>YAPSS.wo\<close>.

  Towsner stratifies terms by cardinality \<^const>\<open>FC\<close> and builds, level by level,
  an \<^emph>\<open>accessible\<close> family.  Critical subterms \<^const>\<open>Kn\<close> always drop the cardinality
  strictly (every \<open>b \<in> Kn n a\<close> has \<open>FC b < n\<close>), so a term of cardinality \<open>n\<close> is
  accessible once its critical subterms are accessible at lower levels.

  We render this with a cumulative level function:
  \<^item> \<^term>\<open>wfpart S\<close> \<dash> the part of \<open>S\<close> on which \<open><\<^sub>o\<close> (restricted to \<open>S\<close>) is
    well-founded (the accessible part);
  \<^item> \<^term>\<open>AAlevel n prev\<close> \<dash> the well-founded part of the level-\<open>n\<close> terms whose
    critical subterms already lie in \<open>prev\<close>;
  \<^item> \<^term>\<open>accUpto n\<close> \<dash> \<open>\<Union>\<^bsub>i<n\<^esub> AAlevel i (accUpto i)\<close>, accumulated structurally.
\<close>

definition wfpart :: "ot set \<Rightarrow> ot set" where
  "wfpart S = S \<inter> Wellfounded.acc {(x,y). x <\<^sub>o y \<and> x \<in> S \<and> y \<in> S}"

definition AAlevel :: "nat \<Rightarrow> ot set \<Rightarrow> ot set" where
  "AAlevel n prev = wfpart {a. FC a \<le> n \<and> (\<forall>b \<in> Kn n a. b \<in> prev)}"

fun accUpto :: "nat \<Rightarrow> ot set" where
  "accUpto 0 = {}"
| "accUpto (Suc n) = accUpto n \<union> AAlevel n (accUpto n)"

text \<open>Basic facts about the accessible part.\<close>

lemma wfpart_subset: "wfpart S \<subseteq> S"
  by (auto simp: wfpart_def)

lemma wfpart_acc:
  "a \<in> wfpart S \<Longrightarrow> a \<in> Wellfounded.acc {(x,y). x <\<^sub>o y \<and> x \<in> S \<and> y \<in> S}"
  by (simp add: wfpart_def)

text \<open>The order restricted to \<^term>\<open>wfpart S\<close> is well-founded.\<close>

lemma wf_on_wfpart:
  "wf {(x,y). x <\<^sub>o y \<and> x \<in> wfpart S \<and> y \<in> wfpart S}"
proof -
  have sub: "{(x,y). x <\<^sub>o y \<and> x \<in> wfpart S \<and> y \<in> wfpart S}
             \<subseteq> {(x,y). x <\<^sub>o y \<and> x \<in> S \<and> y \<in> S}"
    by (auto simp: wfpart_def)
  have "\<And>x. x \<in> Wellfounded.acc {(x,y). x <\<^sub>o y \<and> x \<in> wfpart S \<and> y \<in> wfpart S}"
  proof -
    fix x
    show "x \<in> Wellfounded.acc {(x,y). x <\<^sub>o y \<and> x \<in> wfpart S \<and> y \<in> wfpart S}"
    proof (cases "x \<in> wfpart S")
      case True
      hence "x \<in> Wellfounded.acc {(x,y). x <\<^sub>o y \<and> x \<in> S \<and> y \<in> S}" by (rule wfpart_acc)
      thus ?thesis using acc_subset[OF sub] by (rule rev_subsetD)
    next
      case False
      hence "\<And>y. (y, x) \<in> {(x,y). x <\<^sub>o y \<and> x \<in> wfpart S \<and> y \<in> wfpart S}
              \<Longrightarrow> y \<in> Wellfounded.acc {(x,y). x <\<^sub>o y \<and> x \<in> wfpart S \<and> y \<in> wfpart S}"
        by auto
      thus ?thesis by (rule accI)
    qed
  qed
  thus ?thesis by (subst wf_iff_acc) blast
qed

text \<open>The cumulative level family is monotone.\<close>

lemma accUpto_Suc_supset: "accUpto n \<subseteq> accUpto (Suc n)"
  by simp

lemma accUpto_mono: "m \<le> n \<Longrightarrow> accUpto m \<subseteq> accUpto n"
proof (induction n)
  case 0 thus ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "m = Suc n")
    case True thus ?thesis by simp
  next
    case False
    with Suc.prems have "m \<le> n" by simp
    with Suc.IH have "accUpto m \<subseteq> accUpto n" .
    thus ?thesis by (rule subset_trans[OF _ accUpto_Suc_supset])
  qed
qed

end
