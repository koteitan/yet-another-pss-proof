theory scratch_trans
  imports wflevel
begin

text \<open>Combined linearity (wfo-restricted): transitivity, asymmetry, and the
  incomparability-congruence mnlcong, proved simultaneously by induction on a
  size bound N.  This closes the Su/Su transitivity case via the multp-HO bridge,
  whose carrier hypotheses (asym/trans/mnlcong on the summands) come from the
  combined IH at strictly smaller sizes.\<close>

lemma transp_on_multp\<^sub>H\<^sub>O':
  assumes "asymp_on A (<\<^sub>o)" "transp_on A (<\<^sub>o)"
  shows "transp_on {M. set_mset M \<subseteq> A} (multp\<^sub>H\<^sub>O (<\<^sub>o))"
  by (rule transp_on_multp\<^sub>H\<^sub>O[OF assms]) auto

text \<open>Distinct summands of a sum have total size strictly below the sum's size.\<close>

lemma sum_set_size_lt_Su: "(\<Sum>t\<in>set xs. size (t::ot)) < size (Su xs)"
  by (induction xs) (auto simp: insert_absorb add_strict_mono trans_less_add2)

lemma carrier_sum_lt:
  assumes T: "T \<subseteq> set as \<union> set bs \<union> set zs" and fT: "finite T"
  shows "(\<Sum>t\<in>T. size (t::ot)) < size (Su as) + size (Su bs) + size (Su zs)"
proof -
  have "(\<Sum>t\<in>T. size t) \<le> (\<Sum>t\<in>set as \<union> set bs \<union> set zs. size t)"
    by (rule sum_mono2[OF _ T]) auto
  also have "\<dots> \<le> (\<Sum>t\<in>set as. size t) + (\<Sum>t\<in>set bs \<union> set zs. size t)"
    by (rule sum_Un_le) auto
  also have "\<dots> \<le> (\<Sum>t\<in>set as. size t) + ((\<Sum>t\<in>set bs. size t) + (\<Sum>t\<in>set zs. size t))"
    using sum_Un_le[of "set bs" "set zs" size] by simp
  also have "\<dots> < size (Su as) + size (Su bs) + size (Su zs)"
    using sum_set_size_lt_Su[of as] sum_set_size_lt_Su[of bs] sum_set_size_lt_Su[of zs] by simp
  finally show ?thesis .
qed

lemma olt_lin:
  "(\<forall>a b c. size a + size b + size c \<le> N \<longrightarrow> wfo a \<longrightarrow> wfo b \<longrightarrow> wfo c \<longrightarrow> a <\<^sub>o b \<longrightarrow> b <\<^sub>o c \<longrightarrow> a <\<^sub>o c)
 \<and> (\<forall>a b. size a + size b \<le> N \<longrightarrow> wfo a \<longrightarrow> wfo b \<longrightarrow> a <\<^sub>o b \<longrightarrow> \<not> b <\<^sub>o a)
 \<and> (\<forall>k x m. size k + size x + size m \<le> N \<longrightarrow> wfo k \<longrightarrow> wfo x \<longrightarrow> wfo m
            \<longrightarrow> k <\<^sub>o x \<longrightarrow> \<not> x <\<^sub>o m \<longrightarrow> \<not> m <\<^sub>o x \<longrightarrow> k <\<^sub>o m)"
proof (induction N rule: less_induct)
  case (less N)
  have IHtrans: "x <\<^sub>o z"
    if "size x + size y + size z < N" "wfo x" "wfo y" "wfo z" "x <\<^sub>o y" "y <\<^sub>o z" for x y z
    using less.IH[of "size x + size y + size z"] that by blast
  have IHasym: "\<not> y <\<^sub>o x"
    if "size x + size y < N" "wfo x" "wfo y" "x <\<^sub>o y" for x y
    using less.IH[of "size x + size y"] that by blast
  have IHmnl: "k <\<^sub>o m"
    if "size k + size x + size m < N" "wfo k" "wfo x" "wfo m" "k <\<^sub>o x" "\<not> x <\<^sub>o m" "\<not> m <\<^sub>o x" for k x m
    using less.IH[of "size k + size x + size m"] that by blast
  \<comment> \<open>===================== TRANSITIVITY =====================\<close>
  have TRANS: "a <\<^sub>o c"
    if szabc: "size a + size b + size c \<le> N" and wa: "wfo a" and wb: "wfo b" and wc: "wfo c"
       and ab: "a <\<^sub>o b" and bc: "b <\<^sub>o c" for a b c
  proof -
    have IH: "x <\<^sub>o z" if h: "size x + size y + size z < size a + size b + size c"
                          "wfo x" "wfo y" "wfo z" "x <\<^sub>o y" "y <\<^sub>o z" for x y z
    proof -
      have "size x + size y + size z < N" using h(1) szabc by linarith
      thus ?thesis using IHtrans[of x y z] h by blast
    qed
    show "a <\<^sub>o c"
    proof (cases c)
      case c_Om: (Om n)
      show ?thesis
      proof (cases a)
        case a_Om: (Om q)
        show ?thesis
        proof (cases b)
          case (Om p) thus ?thesis using ab bc a_Om c_Om by simp
        next
          case (Th p f)
          from ab a_Om Th obtain g where g: "g \<in> Kn p f" "Om q \<le>\<^sub>o g" by auto
          have wg: "wfo g" using wfo_Kn[OF _ g(1)] wb Th by simp
          have gn: "g <\<^sub>o Om n" using bc Th c_Om g(1) by simp
          show ?thesis
          proof (cases "Om q = g")
            case True thus ?thesis using gn a_Om c_Om by simp
          next
            case False
            have "size (Om q) + size g + size (Om n) < size a + size b + size c"
              using a_Om Th c_Om Kn_size[OF g(1)] by simp
            moreover have "Om q <\<^sub>o g" using g(2) False by simp
            ultimately have "Om q <\<^sub>o Om n" using gn IH[of "Om q" g "Om n"] wa a_Om wg c_Om wc by simp
            thus ?thesis using a_Om c_Om by simp
          qed
        next
          case (Su bs)
          from ab a_Om Su obtain z where z: "z \<in> set bs" "Om q \<le>\<^sub>o z" by auto
          have wz: "wfo z" using wb Su z(1) by simp
          have zn: "z <\<^sub>o Om n" using bc Su c_Om z(1) by simp
          show ?thesis
          proof (cases "Om q = z")
            case True thus ?thesis using zn a_Om c_Om by simp
          next
            case False
            have "size (Om q) + size z + size (Om n) < size a + size b + size c"
              using a_Om Su c_Om size_lt_Su[OF z(1)] by simp
            moreover have "Om q <\<^sub>o z" using z(2) False by simp
            ultimately have "Om q <\<^sub>o Om n" using zn IH[of "Om q" z "Om n"] wa a_Om wz c_Om wc by simp
            thus ?thesis using a_Om c_Om by simp
          qed
        qed
      next
        case a_Th: (Th q e)
        have "Th q e <\<^sub>o Om n"
        proof (cases b)
          case (Om p)
          have "Th q e <\<^sub>o Om p" using ab a_Th Om by simp
          moreover have "p \<le> n" using bc Om c_Om by simp
          ultimately show ?thesis by (rule olt_Om_mono)
        next
          case (Th p f)
          from ab a_Th Th
          consider (dom) "\<exists>\<delta>\<in>Kn p f. Th q e \<le>\<^sub>o \<delta>"
            | (lower) "\<forall>\<gamma>\<in>Kn q e. \<gamma> <\<^sub>o Th p f" by auto
          thus ?thesis
          proof cases
            case dom
            then obtain \<delta> where d: "\<delta> \<in> Kn p f" "Th q e \<le>\<^sub>o \<delta>" by auto
            have wd: "wfo \<delta>" using wfo_Kn[OF _ d(1)] wb Th by simp
            have dn: "\<delta> <\<^sub>o Om n" using bc Th c_Om d(1) by simp
            show ?thesis
            proof (cases "Th q e = \<delta>")
              case True thus ?thesis using dn by simp
            next
              case False
              have "size (Th q e) + size \<delta> + size (Om n) < size a + size b + size c"
                using a_Th Th c_Om Kn_size[OF d(1)] by simp
              moreover have "Th q e <\<^sub>o \<delta>" using d(2) False by simp
              ultimately show ?thesis using dn IH[of "Th q e" \<delta> "Om n"] wa a_Th wd c_Om wc by simp
            qed
          next
            case lower
            have "\<forall>\<gamma>\<in>Kn q e. \<gamma> <\<^sub>o Om n"
            proof
              fix \<gamma> assume gm: "\<gamma> \<in> Kn q e"
              have wgg: "wfo \<gamma>" using wfo_Kn[OF _ gm] wa a_Th by simp
              have "size \<gamma> + size (Th p f) + size (Om n) < size a + size b + size c"
                using a_Th Th c_Om Kn_size[OF gm] by simp
              moreover have "\<gamma> <\<^sub>o Th p f" using lower gm by simp
              moreover have "Th p f <\<^sub>o Om n" using bc Th c_Om by simp
              ultimately show "\<gamma> <\<^sub>o Om n" using IH[of \<gamma> "Th p f" "Om n"] wgg wb Th c_Om wc by simp
            qed
            thus ?thesis using a_Th by simp
          qed
        next
          case (Su bs)
          from ab a_Th Su obtain z where z: "z \<in> set bs" "Th q e \<le>\<^sub>o z" by auto
          have wz: "wfo z" using wb Su z(1) by simp
          have zn: "z <\<^sub>o Om n" using bc Su c_Om z(1) by simp
          show ?thesis
          proof (cases "Th q e = z")
            case True thus ?thesis using zn by simp
          next
            case False
            have "size (Th q e) + size z + size (Om n) < size a + size b + size c"
              using a_Th Su c_Om size_lt_Su[OF z(1)] by simp
            moreover have "Th q e <\<^sub>o z" using z(2) False by simp
            ultimately show ?thesis using zn IH[of "Th q e" z "Om n"] wa a_Th wz c_Om wc by simp
          qed
        qed
        thus ?thesis using a_Th c_Om by simp
      next
        case a_Su: (Su as)
        have "\<forall>v\<in>set as. v <\<^sub>o Om n"
        proof
          fix v assume v: "v \<in> set as"
          have wv: "wfo v" using wa a_Su v by simp
          have szv: "size v < size a" using a_Su size_lt_Su[OF v] by simp
          show "v <\<^sub>o Om n"
          proof (cases b)
            case (Om p)
            have "v <\<^sub>o Om p" using ab a_Su Om v by simp
            moreover have "p \<le> n" using bc Om c_Om by simp
            ultimately show ?thesis by (rule olt_Om_mono)
          next
            case (Th p f)
            have "v <\<^sub>o Th p f" using ab a_Su Th v by simp
            moreover have "Th p f <\<^sub>o Om n" using bc Th c_Om by simp
            moreover have "size v + size (Th p f) + size (Om n) < size a + size b + size c"
              using Th c_Om szv by simp
            ultimately show ?thesis using IH[of v "Th p f" "Om n"] wv wb Th c_Om wc by simp
          next
            case (Su bs)
            show ?thesis
            proof (cases "v \<in># mset as - mset bs")
              case True
              from ab a_Su Su obtain w where w: "w \<in># mset bs - mset as"
                and wdom: "\<forall>u \<in># mset as - mset bs. u <\<^sub>o w" by auto
              have vw: "v <\<^sub>o w" using wdom True by simp
              have wbs: "w \<in> set bs" using w by (meson in_diffD in_multiset_in_set)
              have ww: "wfo w" using wb Su wbs by simp
              have wn: "w <\<^sub>o Om n" using bc Su c_Om wbs by simp
              have "size v + size w + size (Om n) < size a + size b + size c"
                using a_Su Su c_Om szv size_lt_Su[OF wbs] by simp
              thus ?thesis using vw wn IH[of v w "Om n"] wv ww c_Om wc by simp
            next
              case False
              have "0 < count (mset as) v" using v by (simp add: count_greater_zero_iff)
              moreover have "\<not> count (mset bs) v < count (mset as) v"
                using False by (simp add: in_diff_count)
              ultimately have "0 < count (mset bs) v" by linarith
              hence vbs: "v \<in> set bs" by (simp add: count_greater_zero_iff in_multiset_in_set)
              have "Su bs <\<^sub>o Om n" using bc Su c_Om by simp
              thus ?thesis using vbs by simp
            qed
          qed
        qed
        thus ?thesis using a_Su c_Om by simp
      qed
    next
      case c_Su: (Su zs)
      show ?thesis
      proof (cases "isH a")
        case True
        have "\<exists>z\<in>set zs. a \<le>\<^sub>o z"
        proof (cases "isH b")
          case bH: True
          from bc c_Su bH obtain z where z: "z \<in> set zs" "b \<le>\<^sub>o z" by (cases b) auto
          have wz: "wfo z" using wc c_Su z(1) by simp
          have "a <\<^sub>o z"
          proof (cases "b = z")
            case True thus ?thesis using ab by simp
          next
            case False
            have "size a + size b + size z < size a + size b + size c"
              using c_Su size_lt_Su[OF z(1)] by simp
            moreover have "b <\<^sub>o z" using z(2) False by simp
            ultimately show ?thesis using ab IH[of a b z] wa wb wz by simp
          qed
          thus ?thesis using z(1) by auto
        next
          case bSu: False
          then obtain bs where bbs: "b = Su bs" by (cases b) auto
          from ab True bbs obtain y where y: "y \<in> set bs" "a \<le>\<^sub>o y" by (cases a) auto
          have wy: "wfo y" using wb bbs y(1) by simp
          have "\<exists>z\<in>set zs. y \<le>\<^sub>o z"
          proof (cases "y \<in># mset zs")
            case True thus ?thesis by (auto simp: in_multiset_in_set)
          next
            case False
            have "count (mset zs) y = 0" using False by (simp add: not_in_iff)
            moreover have "0 < count (mset bs) y"
              using y(1) by (simp add: count_greater_zero_iff in_multiset_in_set)
            ultimately have "count (mset zs) y < count (mset bs) y" by linarith
            hence ybz: "y \<in># mset bs - mset zs" by (simp add: in_diff_count)
            from bc[unfolded bbs c_Su] obtain w where w: "w \<in># mset zs - mset bs"
                and wdom: "\<forall>u \<in># mset bs - mset zs. u <\<^sub>o w" by auto
            have "y <\<^sub>o w" using wdom ybz by simp
            moreover have "w \<in> set zs" using w by (meson in_diffD in_multiset_in_set)
            ultimately show ?thesis by auto
          qed
          then obtain z where z: "z \<in> set zs" "y \<le>\<^sub>o z" by auto
          have wz: "wfo z" using wc c_Su z(1) by simp
          have "a \<le>\<^sub>o z"
          proof (cases "y = z")
            case True thus ?thesis using y(2) by simp
          next
            case yz: False
            hence yzlt: "y <\<^sub>o z" using z(2) by simp
            show ?thesis
            proof (cases "a = y")
              case True thus ?thesis using yzlt by auto
            next
              case False
              have "size y < size b" using bbs size_lt_Su[OF y(1)] by simp
              moreover have "size z < size c" using c_Su size_lt_Su[OF z(1)] by simp
              ultimately have "size a + size y + size z < size a + size b + size c" by simp
              moreover have "a <\<^sub>o y" using y(2) False by simp
              ultimately have "a <\<^sub>o z" using yzlt IH[of a y z] wa wy wz by simp
              thus ?thesis by simp
            qed
          qed
          thus ?thesis using z(1) by auto
        qed
        thus ?thesis using True c_Su by (cases a) auto
      next
        case False
        \<comment> \<open>a = Su as, c = Su zs: multiset transitivity via the multp-HO bridge\<close>
        then obtain as where a_Su: "a = Su as" by (cases a) auto
        show ?thesis
        proof (cases b)
          case b_Om: (Om p)
          \<comment> \<open>Su as <o Om p <o Su zs: but Om p <o Su zs needs a dominator; handle via summands\<close>
          have allz: "\<forall>v\<in>set as. \<exists>z\<in>set zs. v \<le>\<^sub>o z"
          proof
            fix v assume v: "v \<in> set as"
            have wv: "wfo v" using wa a_Su v by simp
            have "v <\<^sub>o Om p" using ab a_Su b_Om v by simp
            \<comment> \<open>Om p <o Su zs : exists z, Om p <= z\<close>
            from bc b_Om c_Su obtain z where z: "z \<in> set zs" "Om p \<le>\<^sub>o z" by auto
            have wz: "wfo z" using wc c_Su z(1) by simp
            have "v <\<^sub>o z"
            proof (cases "Om p = z")
              case True thus ?thesis using \<open>v <\<^sub>o Om p\<close> by simp
            next
              case False
              have "size v + size (Om p) + size z < size a + size b + size c"
                using a_Su b_Om c_Su size_lt_Su[OF v] size_lt_Su[OF z(1)] by simp
              moreover have "Om p <\<^sub>o z" using z(2) False by simp
              ultimately show ?thesis using \<open>v <\<^sub>o Om p\<close> IH[of v "Om p" z] wv wb b_Om wz by simp
            qed
            thus "\<exists>z\<in>set zs. v \<le>\<^sub>o z" using z(1) by auto
          qed
          show ?thesis sorry
        next
          case b_Th: (Th p f)
          show ?thesis sorry
        next
          case b_Su: (Su bs)
          have wbs: "wfo (Su bs)" using wb b_Su by simp
          let ?carrier = "set as \<union> set bs \<union> set zs"
          have wfocar: "\<forall>t\<in>?carrier. wfo t"
            using wa wb wc a_Su b_Su c_Su by auto
          have asymC: "asymp_on ?carrier (<\<^sub>o)"
          proof (rule asymp_onI)
            fix p q assume p: "p \<in> ?carrier" and q: "q \<in> ?carrier" and pq: "p <\<^sub>o q"
            have wp: "wfo p" using wfocar p by simp
            have wq: "wfo q" using wfocar q by simp
            have "size p < size a \<or> size p < size b \<or> size p < size c"
              using p a_Su b_Su c_Su size_lt_Su by auto
            moreover have "size q < size a \<or> size q < size b \<or> size q < size c"
              using q a_Su b_Su c_Su size_lt_Su by auto
            ultimately have "size p + size q < N" sorry
            thus "\<not> q <\<^sub>o p" using IHasym[of p q] wp wq pq by simp
          qed
          have transC: "transp_on ?carrier (<\<^sub>o)"
          proof (rule transp_onI)
            fix p q r assume p: "p\<in>?carrier" and q: "q\<in>?carrier" and r: "r\<in>?carrier"
              and pq: "p<\<^sub>o q" and qr: "q<\<^sub>o r"
            have wp: "wfo p" and wq: "wfo q" and wr: "wfo r" using wfocar p q r by auto
            have "size p < size a \<or> size p < size b \<or> size p < size c"
              using p a_Su b_Su c_Su size_lt_Su by auto
            moreover have "size q < size a \<or> size q < size b \<or> size q < size c"
              using q a_Su b_Su c_Su size_lt_Su by auto
            moreover have "size r < size a \<or> size r < size b \<or> size r < size c"
              using r a_Su b_Su c_Su size_lt_Su by auto
            ultimately have "size p + size q + size r < N" sorry
            thus "p <\<^sub>o r" using IHtrans[of p q r] wp wq wr pq qr by simp
          qed
          have mnlC: "\<And>k x m. k \<in> set as \<Longrightarrow> x \<in> set zs \<Longrightarrow> m \<in> set zs \<Longrightarrow>
                k <\<^sub>o x \<Longrightarrow> \<not> x <\<^sub>o m \<Longrightarrow> \<not> m <\<^sub>o x \<Longrightarrow> k <\<^sub>o m"
          proof -
            fix k x m assume k: "k\<in>set as" and x: "x\<in>set zs" and m: "m\<in>set zs"
              and kx: "k<\<^sub>o x" and nxm: "\<not>x<\<^sub>o m" and nmx: "\<not>m<\<^sub>o x"
            have wk: "wfo k" using wa a_Su k by simp
            have wx: "wfo x" using wc c_Su x by simp
            have wm: "wfo m" using wc c_Su m by simp
            have "size k < size a" "size x < size c" "size m < size c"
              using k x m a_Su c_Su size_lt_Su by auto
            hence "size k + size x + size m < N" sorry
            thus "k <\<^sub>o m" using IHmnl[of k x m] wk wx wm kx nxm nmx by simp
          qed
          have ab': "Su as <\<^sub>o Su bs" using ab a_Su b_Su by simp
          have bc': "Su bs <\<^sub>o Su zs" using bc b_Su c_Su by simp
          \<comment> \<open>now the bridge\<close>
          have hab: "multp\<^sub>H\<^sub>O (<\<^sub>o) (mset as) (mset bs)" by (rule olt_Su_imp_multp\<^sub>H\<^sub>O[OF ab'])
          have hbc: "multp\<^sub>H\<^sub>O (<\<^sub>o) (mset bs) (mset zs)" by (rule olt_Su_imp_multp\<^sub>H\<^sub>O[OF bc'])
          have tA: "transp_on {M. set_mset M \<subseteq> ?carrier} (multp\<^sub>H\<^sub>O (<\<^sub>o))"
            by (rule transp_on_multp\<^sub>H\<^sub>O'[OF asymC transC])
          have hac: "multp\<^sub>H\<^sub>O (<\<^sub>o) (mset as) (mset zs)"
            using transp_onD[OF tA, of "mset as" "mset bs" "mset zs"] hab hbc by auto
          have asymAZ: "asymp_on (set as \<union> set zs) (<\<^sub>o)"
            using asymC by (rule asymp_on_subset) auto
          have transAZ: "transp_on (set as \<union> set zs) (<\<^sub>o)"
            using transC by (rule transp_on_subset) auto
          have "Su as <\<^sub>o Su zs"
            by (rule multp\<^sub>H\<^sub>O_imp_olt_Su[OF hac asymAZ transAZ mnlC])
          thus ?thesis using a_Su c_Su by simp
        qed
      qed
    next
      case c_Th: (Th n d)
      show ?thesis sorry
    qed
  qed
  \<comment> \<open>===================== ASYMMETRY =====================\<close>
  have ASYM: "\<not> b0 <\<^sub>o a0"
    if "size a0 + size b0 \<le> N" "wfo a0" "wfo b0" "a0 <\<^sub>o b0" for a0 b0
    sorry
  \<comment> \<open>===================== MNLCONG =====================\<close>
  have MNL: "k0 <\<^sub>o m0"
    if "size k0 + size x0 + size m0 \<le> N" "wfo k0" "wfo x0" "wfo m0"
       "k0 <\<^sub>o x0" "\<not> x0 <\<^sub>o m0" "\<not> m0 <\<^sub>o x0" for k0 x0 m0
    sorry
  show ?case
    using TRANS ASYM MNL by blast
qed

end
