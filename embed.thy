theory embed
  imports wf wo
begin

section \<open>Embedding the PSS notation into the well-foundedness core\<close>

text \<open>
  The PSS notation \<^typ>\<open>three\<close> (\<open>p\<^sub>a(b)+c\<close>, with the naive subscript-first order
  \<open>olt\<close> = \<open><o\<close> from \<^theory>\<open>YAPSS.mechanized\<close>) is mapped into Towsner's well-founded
  ordinal terms \<^typ>\<open>ot\<close> (\<^theory>\<open>YAPSS.wo\<close>) by reading each principal \<open>p\<^sub>a(b)\<close> as the
  collapsing term \<open>\<vartheta>\<^sub>a b\<close> (\<^const>\<open>Th\<close>) and the \<open>+\<close>-chain as the natural sum
  (\<^const>\<open>Su\<close>).  The plan: prove this map is order-preserving on \<open>NF\<close> (where the
  naive order coincides with the true collapsing order), so well-foundedness of
  \<open><\<^sub>o\<close> transfers to \<open>NF\<close>, discharging the remaining obligation of @{thm [source]
  wf_Rnf_from_within_level} / the diagonal accessibility.
\<close>

text \<open>\<open>princs t\<close> is the list of principal summands of \<open>t\<close> read off its top-level
  \<open>+\<close>-chain; \<open>embed t = Su (princs t)\<close>.\<close>

fun princs :: "three \<Rightarrow> ot list" where
  "princs Z = []"
| "princs (P a b c) = Th a (Su (princs b)) # princs c"

definition embed :: "three \<Rightarrow> ot" where
  "embed t = Su (princs t)"

lemma embed_Z [simp]: "embed Z = Zero"
  by (simp add: embed_def)

lemma princs_P [simp]:
  "princs (P a b c) = Th a (embed b) # princs c"
  by (simp add: embed_def)

lemma embed_P:
  "embed (P a b c) = Su (Th a (embed b) # princs c)"
  by (simp add: embed_def)

text \<open>Every summand produced by the embedding is a principal \<vartheta>-term.\<close>

lemma princs_all_Th: "x \<in> set (princs t) \<Longrightarrow> \<exists>a b. x = Th a (embed b)"
  by (induction t) (auto simp: embed_def)

lemma isH_princs: "x \<in> set (princs t) \<Longrightarrow> isH x"
  using princs_all_Th by fastforce

end
