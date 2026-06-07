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

end
