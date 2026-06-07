theory buchholz
  imports wflevel
begin

section \<open>The Buchholz well-foundedness core: \<open>wf pR\<close> via distinguished sets\<close>

text \<open>
  \<^bold>\<open>Under reconstruction (2026-06-08).\<close>  The previous content stratified the
  distinguished sets by the \<^emph>\<open>top\<close> cardinality \<^const>\<open>FC\<close>; that stratification was
  found to be unprovable (it concentrates the entire difficulty at level \<open>0\<close> with no
  inductive help, see \<^file>\<open>memo.md\<close>).  Following Towsner \<^emph>\<open>Polymorphic Ordinal
  Notations\<close> \<section>3.2 (transcribed to the absolute system with \<^typ>\<open>int\<close> levels), the
  well-foundedness proof is being rebuilt to stratify by the \<^emph>\<open>ground\<close>
  \<open>G(\<alpha>) = min (FCset \<alpha>)\<close> (Def 3.6\<dash>3.7), with an explicit shift on the cardinal
  levels (Def 3.3) needed to discharge the cross-subscript predecessor case
  (\<open>\<vartheta>\<^bsub>p\<^esub> e <\<^sub>o \<vartheta>\<^bsub>s\<^esub> d\<close> with \<open>p < s\<close>).

  The reduction \<^prop>\<open>wf pR \<Longrightarrow> wf oltRw\<close> (\<^theory>\<open>YAPSS.wflevel\<close>) and the generic
  accessibility infrastructure (\<^theory>\<open>YAPSS.accinfra\<close>) are unaffected and reused.
\<close>

end
