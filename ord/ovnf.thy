theory ovnf
  imports otembed "YAPSS.wf" "YAPSS.proofs"
begin

text \<open>
  \<^bold>\<open>Value-semantics route to \<open>wf Rnf\<close> (\<open>oV_mono_NF\<close>)\<close>.

  This theory assembles PSS termination through the order-embedding value map
  \<open>oV\<close>, \<^emph>\<open>bypassing\<close> the syntactic normalization \<open>nrm\<close> and its open obligation
  \<open>nrm_order_pres\<close> (nrm.thy).  The keystone is

    \<open>oV_mono_NF\<close>:  \<open>v \<in> NF \<Longrightarrow> u \<in> NF \<Longrightarrow> v <o u \<Longrightarrow> oV v < oV u\<close>

  i.e. the value map is strictly monotone on the standard-form fragment
  \<open>NF = translate ` ST_PS\<close>.  From it, \<open>wf Rnf\<close> and PSS termination follow with
  \<^emph>\<open>green\<close> plumbing (\<open>wf_Rnf_oV\<close>, \<open>PSS_terminates_oV\<close> below), via \<open>inv_image VWF oV\<close>
  and \<open>step_terminates_cond[OF m_step_decreases]\<close> \<dash> no mention of \<open>nrm\<close>.

  \<^bold>\<open>Why \<open>oV_mono_NF\<close> is irreducible (recorded honestly).\<close>  A structural recursion
  on the term \<open>v\<close> (mirroring \<open>oV_order_pres\<close>) splits \<open>v <o u\<close> into \<open>sub\<close>
  (subscript jump), \<open>arg\<close> (same subscript, \<open>b <o f\<close>) and \<open>tail\<close>.  The \<open>sub\<close> case
  is green from \<open>cnf_spinesub_le\<close> (the OT2 property of \<open>NF\<close>, proved below).  But
  the \<open>arg\<close> and \<open>tail\<close> cases recurse into the \<^emph>\<open>arguments\<close> \<open>b, f\<close> and \<^emph>\<open>tails\<close>
  \<open>c, g\<close>, which are \<^bold>\<open>not in \<open>NF\<close>\<close> (a sub-term of a translate is not a translate),
  so the induction hypothesis is unavailable.  Weakening the carried invariant
  to \<open>cnf\<close> (which \<^emph>\<open>does\<close> descend to args and tails) makes the statement
  \<^bold>\<open>FALSE\<close>: \<open>y\<^sub>2 = p\<^bsub>0\<^esub>(p\<^bsub>1\<^esub>(y\<^sub>1)) <o y\<^sub>1 = p\<^bsub>0\<^esub>(p\<^bsub>1\<^esub>(p\<^bsub>1\<^esub>(0)))\<close> are both \<open>cnf\<close>,
  yet \<open>oV y\<^sub>2 = oV y\<^sub>1\<close> (here \<open>y\<^sub>1 \<in> NF\<close> but \<open>y\<^sub>2 \<notin> NF\<close>; its pair sequence
  \<open>(0,0)(1,1)(2,0)(3,1)(4,1)\<close> is non-standard).  Hence the standard-form
  (\<open>blockok\<close>, row-1 parenthood) discipline of \<open>NF\<close> is genuinely essential and
  does \<^emph>\<open>not\<close> reduce to a clean term-level invariant; this is the same Buchholz
  \<section>1 / \<open>nrm_order_pres\<close> core (memo 続78,89(4'),(6)).  \<open>oV_mono_NF\<close> is therefore
  kept as a \<^bold>\<open>single localized \<open>sorry\<close>\<close>, empirically TRUE (zero violations on
  749{,}525 arg-case \<open>NF\<close>-pairs at closure+5; memo 続89(1) 1{,}124{,}250/0).
\<close>

subsection \<open>OT2 for \<open>cnf\<close>: the spine subscripts are dominated by the lead (green)\<close>

text \<open>A \<open>cnf\<close> term has weakly-decreasing spine heads (subscript-first), so every
  spine subscript is \<open>\<le>\<close> the leading one.  This is the (green) OT2 ingredient the
  subscript-jump case needs on \<open>NF\<close>; it does \<^emph>\<open>not\<close> require \<open>wf3\<close>.  Reusable.\<close>

lemma cnf_spine_le_head:
  "cnf (P a b c) \<Longrightarrow> spinesub_le a c"
proof (induction c arbitrary: a b)
  case Z thus ?case by simp
next
  case (P e f g)
  have ncmp: "\<not> (P a b Z <o P e f Z)" and cnfg: "cnf (P e f g)"
    using P.prems by auto
  have "e \<le> a"
  proof (rule ccontr)
    assume "\<not> e \<le> a" hence "a < e" by simp
    hence "P a b Z <o P e f Z" by simp
    with ncmp show False by simp
  qed
  moreover have "spinesub_le e g" by (rule P.IH(2)[OF cnfg])
  ultimately show ?case using spinesub_le_mono by auto
qed

lemma cnf_spinesub_le: "cnf t \<Longrightarrow> spinesub_le (lead t) t"
proof (cases t)
  case Z thus ?thesis by simp
next
  case (P a b c)
  assume "cnf t"
  hence "spinesub_le a c" using P by (simp add: cnf_spine_le_head)
  thus ?thesis using P by simp
qed

text \<open>The \<open>cnf\<close> head comparison propagates down the spine: every spine principal
  has head \<open>\<le>\<close> the leading principal (\<open>headle_all\<close>).  Also green; reusable for the
  \<open>arg\<close>-case spine bound once the leading inequality is available.\<close>

lemma headle_all_mono:
  "headle_all y c \<Longrightarrow> hdle y z \<Longrightarrow> headle_all z c"
proof (induction c)
  case Z thus ?case by simp
next
  case (P a b c')
  have "hdle (P a b Z) y" and "headle_all y c'" using P.prems(1) by auto
  thus ?case using P.IH P.prems(2) hdle_trans by auto
qed

lemma cnf_headle_all:
  "cnf (P a b c) \<Longrightarrow> headle_all (P a b Z) c"
proof (induction c arbitrary: a b)
  case Z thus ?case by simp
next
  case (P e f g)
  have ncmp: "\<not> (P a b Z <o P e f Z)" and cnfg: "cnf (P e f g)"
    using P.prems by auto
  have hd: "hdle (P e f Z) (P a b Z)"
  proof -
    from ncmp have "\<not> (a < e \<or> (a = e \<and> olt b f))" by simp
    hence na: "\<not> a < e" and nb: "a = e \<longrightarrow> \<not> olt b f" by auto
    have "e < a \<or> e = a" using na by arith
    moreover have "e = a \<Longrightarrow> olt f b \<or> f = b" using nb olt_total by blast
    ultimately show ?thesis by auto
  qed
  have "headle_all (P e f Z) g" by (rule P.IH(2)[OF cnfg])
  hence htail: "headle_all (P a b Z) g" by (rule headle_all_mono[OF _ hd])
  show ?case using hd htail by simp
qed

text \<open>\<open>cnf\<close> is inherited by the \<^emph>\<open>arguments\<close> and by spine \<^emph>\<open>suffixes\<close> (green,
  structural).  These record that \<open>cnf\<close> descends \<dash> the property that makes the
  \<open>cnf\<close>-weakening tempting, and exactly why its failure (the \<open>y\<^sub>1,y\<^sub>2\<close>
  counterexample) pins the irreducibility on the \<^emph>\<open>OT3 / canonicity\<close> content
  rather than on OT2.\<close>

lemma cnf_arg: "cnf (P a b c) \<Longrightarrow> cnf b"
  by (cases c) auto

lemma cnf_tail_suffix: "cnf (P a b c) \<Longrightarrow> cnf c"
  by (cases c) auto

subsection \<open>The keystone (single localized \<open>sorry\<close>)\<close>

text \<open>\<^bold>\<open>\<open>oV\<close> is strictly monotone on \<open>NF\<close>\<close>.  The irreducible standard-form core
  (Buchholz \<section>1 at the sequence level); see the theory header for why it does not
  decompose by term recursion.  Empirically TRUE.\<close>

theorem oV_mono_NF:
  assumes "v \<in> NF" and "u \<in> NF" and "olt v u"
  shows "oV v < oV u"
  sorry

subsection \<open>\<open>wf Rnf\<close> and PSS termination via \<open>oV\<close> (green, no \<open>nrm\<close>)\<close>

text \<open>\<^bold>\<open>Well-foundedness of \<open><o\<close> on \<open>NF\<close>\<close>, obtained by pulling back the
  well-ordering \<open>VWF\<close> on the ordinals along \<open>oV\<close>; \<open>oV_mono_NF\<close> embeds \<open>Rnf\<close> into
  \<open>inv_image VWF oV\<close>.  Independent of \<open>nrm\<close> and \<open>nrm_order_pres\<close>.\<close>

theorem wf_Rnf_oV: "wf Rnf"
proof (rule wf_subset[OF wf_inv_image[OF wf_VWF, of oV]])
  show "Rnf \<subseteq> inv_image VWF oV"
  proof (rule subrelI)
    fix v u assume "(v,u) \<in> Rnf"
    hence vu: "olt v u" and uNF: "u \<in> NF" and vNF: "v \<in> NF" by auto
    have "oV v < oV u" by (rule oV_mono_NF[OF vNF uNF vu])
    thus "(v,u) \<in> inv_image VWF oV"
      by (simp add: inv_image_def VWF_iff_Ord_less)
  qed
qed

text \<open>\<^bold>\<open>PSS termination\<close> through the value measure \<open>oV \<circ> translate\<close>.  Assembled from
  \<open>m_step_decreases\<close> (the green expansion-step decrease) and \<open>wf_Rnf_oV\<close> via the
  generic \<open>step_terminates_cond\<close> \<dash> the entire route avoids \<open>nrm\<close>, resting solely
  on the single \<open>oV_mono_NF\<close> obligation.\<close>

theorem PSS_terminates_oV: "wf {(T,M). M \<in> ST_PS \<and> step M T}"
proof (rule step_terminates_cond)
  fix M :: pairseq and n :: nat
  assume "M \<in> ST_PS" and L: "1 < Lng M" and n: "1 \<le> n"
  show "olt (translate (M[n])) (translate M)" by (rule m_step_decreases[OF L n])
next
  show "wf {(v,u). olt v u \<and> u \<in> NF \<and> v \<in> NF}" by (rule wf_Rnf_oV)
qed

end
