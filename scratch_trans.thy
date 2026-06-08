theory scratch_trans
  imports wflevel
begin

text \<open>Validated reusable pieces for the olt_trans (wfo-restricted) proof, via the
  midH decomposition (see memo 続25):
  olt_trans_midH (principal middle, self-contained) \<rightarrow> olt_asym \<rightarrow> mnlcong (wfo)
  \<rightarrow> full olt_trans (Su/Su: b principal via midH, b=Su via the multp-HO bridge).

  This file holds: (1) the multp-HO bridge wiring for the Su/Su case, and
  (2) the distinct-summand size bounds needed for the bridge's carrier transp_on.\<close>

subsection \<open>multp-HO bridge (Su/Su transitivity given carrier asym/trans/mnlcong)\<close>

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
  have hac: "multp\<^sub>H\<^sub>O (<\<^sub>o) (mset as) (mset zs)"
    using transp_onD[OF tA, of "mset as" "mset bs" "mset zs"] hab hbc by auto
  have subAZ: "set as \<union> set zs \<subseteq> ?A" by auto
  have asym': "asymp_on (set as \<union> set zs) (<\<^sub>o)" by (rule asymp_on_subset[OF asym subAZ])
  have trans': "transp_on (set as \<union> set zs) (<\<^sub>o)" by (rule transp_on_subset[OF trans subAZ])
  show ?thesis by (rule multp\<^sub>H\<^sub>O_imp_olt_Su[OF hac asym' trans' mnl])
qed

subsection \<open>Distinct-summand size bounds (for the carrier transp_on in the bridge)\<close>

lemma sum_set_size_lt_Su: "(\<Sum>t\<in>set xs. size (t::ot)) < size (Su xs)"
proof (induction xs)
  case Nil thus ?case by simp
next
  case (Cons a xs)
  show ?case
  proof (cases "a \<in> set xs")
    case True hence "set (a # xs) = set xs" by auto
    thus ?thesis using Cons.IH by simp
  next
    case False
    have "(\<Sum>t\<in>set (a # xs). size t) = size a + (\<Sum>t\<in>set xs. size t)"
      using False by simp
    also have "\<dots> < size a + size (Su xs)" using Cons.IH by simp
    also have "\<dots> \<le> size (Su (a # xs))" by simp
    finally show ?thesis .
  qed
qed

lemma sum_Un_le_ot: "finite A \<Longrightarrow> finite B \<Longrightarrow> (\<Sum>t\<in>A \<union> B. size (t::ot)) \<le> (\<Sum>t\<in>A. size t) + (\<Sum>t\<in>B. size t)"
  using sum.union_inter[of A B size] by (simp add: add.commute add.left_commute)

lemma carrier_sum_lt:
  assumes T: "T \<subseteq> set as \<union> set bs \<union> set zs"
  shows "(\<Sum>t\<in>T. size (t::ot)) < size (Su as) + size (Su bs) + size (Su zs)"
proof -
  have "(\<Sum>t\<in>T. size t) \<le> (\<Sum>t\<in>set as \<union> set bs \<union> set zs. size t)"
    by (rule sum_mono2[OF _ T]) auto
  also have "\<dots> \<le> (\<Sum>t\<in>set as \<union> set bs. size t) + (\<Sum>t\<in>set zs. size t)"
    by (rule sum_Un_le_ot) auto
  also have "(\<Sum>t\<in>set as \<union> set bs. size t) \<le> (\<Sum>t\<in>set as. size t) + (\<Sum>t\<in>set bs. size t)"
    by (rule sum_Un_le_ot) auto
  finally have "(\<Sum>t\<in>T. size t)
        \<le> (\<Sum>t\<in>set as. size t) + (\<Sum>t\<in>set bs. size t) + (\<Sum>t\<in>set zs. size t)" by simp
  also have "\<dots> < size (Su as) + size (Su bs) + size (Su zs)"
    using sum_set_size_lt_Su[of as] sum_set_size_lt_Su[of bs] sum_set_size_lt_Su[of zs] by simp
  finally show ?thesis .
qed

text \<open>Two/three distinct summands: total size below the three sums' sizes.\<close>

lemma size2_distinct:
  assumes "p \<in> set as \<union> set bs \<union> set zs" "q \<in> set as \<union> set bs \<union> set zs" "p \<noteq> q"
  shows "size p + size q < size (Su as) + size (Su bs) + size (Su zs)"
proof -
  have "{p, q} \<subseteq> set as \<union> set bs \<union> set zs" using assms by simp
  from carrier_sum_lt[OF this] assms(3) show ?thesis by simp
qed

lemma size3_distinct:
  assumes "p \<in> set as \<union> set bs \<union> set zs" "q \<in> set as \<union> set bs \<union> set zs" "r \<in> set as \<union> set bs \<union> set zs"
    and "p \<noteq> q" "q \<noteq> r" "p \<noteq> r"
  shows "size p + size q + size r < size (Su as) + size (Su bs) + size (Su zs)"
proof -
  have "{p, q, r} \<subseteq> set as \<union> set bs \<union> set zs" using assms by simp
  from carrier_sum_lt[OF this] assms(4,5,6) show ?thesis by simp
qed

end
