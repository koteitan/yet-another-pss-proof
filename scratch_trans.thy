theory scratch_trans
  imports wo
begin

text \<open>Scratch: validate the multp-HO-bridge route for the Su/Su transitivity case
  of olt-trans (line 997).  From Su as < Su bs and Su bs < Su zs derive multp-HO both
  ways (forward bridge, unconditional), compose via library transp-on-multp-HO on the
  carrier, then multp-HO-imp-olt-Su back.  Carrier hyps (asymp-on, transp-on, mnlcong on
  set as Un set bs Un set zs) are ASSUMED here; in the real proof they come from a
  combined trans+asym+mnlcong size-induction.\<close>

lemma transp_on_multp\<^sub>H\<^sub>O':
  assumes "asymp_on A (<\<^sub>o)" "transp_on A (<\<^sub>o)"
  shows "transp_on {M. set_mset M \<subseteq> A} (multp\<^sub>H\<^sub>O (<\<^sub>o))"
  by (rule transp_on_multp\<^sub>H\<^sub>O[OF assms]) auto

lemma su_su_trans_via_bridge:
  assumes ab: "Su as <\<^sub>o Su bs"
    and bc: "Su bs <\<^sub>o Su zs"
    and asym: "asymp_on (set as \<union> set bs \<union> set zs) (<\<^sub>o)"
    and trans: "transp_on (set as \<union> set bs \<union> set zs) (<\<^sub>o)"
    and mnl: "\<And>k x m. k \<in> set as \<Longrightarrow> x \<in> set zs \<Longrightarrow> m \<in> set zs \<Longrightarrow>
                k <\<^sub>o x \<Longrightarrow> \<not> x <\<^sub>o m \<Longrightarrow> \<not> m <\<^sub>o x \<Longrightarrow> k <\<^sub>o m"
  shows "Su as <\<^sub>o Su zs"
proof -
  have hab: "multp\<^sub>H\<^sub>O (<\<^sub>o) (mset as) (mset bs)" by (rule olt_Su_imp_multp\<^sub>H\<^sub>O[OF ab])
  have hbc: "multp\<^sub>H\<^sub>O (<\<^sub>o) (mset bs) (mset zs)" by (rule olt_Su_imp_multp\<^sub>H\<^sub>O[OF bc])
  let ?A = "set as \<union> set bs \<union> set zs"
  have tA: "transp_on {M. set_mset M \<subseteq> ?A} (multp\<^sub>H\<^sub>O (<\<^sub>o))"
    by (rule transp_on_multp\<^sub>H\<^sub>O'[OF asym trans])
  have a_in: "mset as \<in> {M. set_mset M \<subseteq> ?A}" by auto
  have b_in: "mset bs \<in> {M. set_mset M \<subseteq> ?A}" by auto
  have z_in: "mset zs \<in> {M. set_mset M \<subseteq> ?A}" by auto
  have hac: "multp\<^sub>H\<^sub>O (<\<^sub>o) (mset as) (mset zs)"
    using transp_onD[OF tA a_in b_in z_in hab hbc] .
  have subAZ: "set as \<union> set zs \<subseteq> ?A" by auto
  have asym': "asymp_on (set as \<union> set zs) (<\<^sub>o)" by (rule asymp_on_subset[OF asym subAZ])
  have trans': "transp_on (set as \<union> set zs) (<\<^sub>o)" by (rule transp_on_subset[OF trans subAZ])
  show ?thesis by (rule multp\<^sub>H\<^sub>O_imp_olt_Su[OF hac asym' trans' mnl])
qed

end
