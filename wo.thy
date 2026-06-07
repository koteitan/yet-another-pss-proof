theory wo
  imports "HOL-Library.Multiset"
begin

section \<open>The well-foundedness core: Towsner's Buchholz ordinal notation\<close>

text \<open>
  This theory ports the \<^emph>\<open>distinguished-set\<close> well-foundedness proof of the
  Buchholz ordinal notation from

    H. Towsner, \<^emph>\<open>Polymorphic Ordinal Notations\<close> (arXiv:2504.02131v2), \<section>2 and \<section>3.2.

  We use the non-polymorphic system \<open>OT\<^bsub>\<Omega>\<^sub>\<omega>\<^esub>\<close> of \<section>2 (absolute cardinal indices
  \<open>\<Omega>\<^sub>n\<close>, \<open>\<vartheta>\<^sub>n\<close>, \<open>n \<in> \<nat>\<close>), which fits the finite subscripts produced by PSS, and
  prove well-foundedness by the \<open>Acc\<^sub>n \<subseteq> M\<^sub>n\<close> hierarchy of \<section>3.2 (Lemmas 3.8\<dash>3.12).

  The terms:
  \<^item> \<open>Om n\<close>       \<open>= \<Omega>\<^sub>n\<close>            (a cardinal; scaffolding for the proof)
  \<^item> \<open>Th n a\<close>     \<open>= \<vartheta>\<^sub>n a\<close>           (the collapsing function)
  \<^item> \<open>Su xs\<close>      \<open>= #{x\<^sub>0,\<dots>,x\<^bsub>k-1\<^esub>}\<close>  (natural/commutative sum; \<open>Su [] = 0\<close>)

  Towsner's \<open>\<omega>\<^bsup>a\<^esup>\<close> constructor is omitted: the order-embedding of the PSS notation
  \<open>p\<^sub>a(b)+c\<close> uses only \<open>Th\<close> (principals \<open>p\<^sub>a(b) = \<vartheta>\<^sub>a b\<close>) and \<open>Su\<close> (the \<open>+\<close> chain);
  \<open>Om\<close> occurs only inside critical-subterm sets as proof scaffolding.

  The \<^emph>\<open>principal\<close> (Buchholz: \<open>H\<close>) terms are \<open>Om\<close>, \<open>Th\<close>; \<open>Su\<close> is the sum.
\<close>

datatype ot =
    Om nat            \<comment> \<open>\<open>\<Omega>\<^sub>n\<close>\<close>
  | Th nat ot         \<comment> \<open>\<open>\<vartheta>\<^sub>n a\<close>\<close>
  | Su "ot list"      \<comment> \<open>\<open>#{x\<^sub>0,\<dots>}\<close>, summands principal, length \<open>\<noteq> 1\<close>; \<open>Su [] = 0\<close>\<close>

abbreviation Zero :: ot where "Zero \<equiv> Su []"

text \<open>The principal (Buchholz \<open>H\<close>) terms.\<close>

fun isH :: "ot \<Rightarrow> bool" where
  "isH (Om _) = True"
| "isH (Th _ _) = True"
| "isH (Su _) = False"

subsection \<open>Formal cardinalities (Towsner Def 2.4)\<close>

text \<open>\<open>FCset a\<close> is the set of cardinal levels occurring free in \<open>a\<close>;
  \<open>FC\<^bsub>n\<^esub>(\<vartheta>\<^sub>n a) = FC(a) \<setminus> {m. m \<ge> n}\<close>.\<close>

fun FCset :: "ot \<Rightarrow> nat set" where
  "FCset (Om n) = {n}"
| "FCset (Th n a) = {m \<in> FCset a. m < n}"
| "FCset (Su xs) = (\<Union>x \<in> set xs. FCset x)"

lemma finite_FCset [simp]: "finite (FCset a)"
  by (induction a) auto

definition FC :: "ot \<Rightarrow> nat" where
  "FC a = (if FCset a = {} then 0 else Max (FCset a))"

subsection \<open>Critical subterms (Towsner Def 2.2)\<close>

text \<open>\<open>Kn n a\<close> collects the maximal subterms of \<open>a\<close> of cardinality \<open>\<le> n\<close>:
  \<open>K\<^sub>n \<Omega>\<^sub>m = {\<Omega>\<^sub>m}\<close> iff \<open>m < n\<close>, and \<open>K\<^sub>n \<vartheta>\<^sub>m a = {\<vartheta>\<^sub>m a}\<close> iff \<open>m \<le> n\<close> (else recurse).\<close>

fun Kn :: "nat \<Rightarrow> ot \<Rightarrow> ot set" where
  "Kn n (Om m) = (if m < n then {Om m} else {})"
| "Kn n (Th m a) = (if n < m then Kn n a else {Th m a})"
| "Kn n (Su xs) = (\<Union>x \<in> set xs. Kn n x)"

lemma finite_Kn [simp]: "finite (Kn n a)"
  by (induction a) auto

text \<open>A list element is strictly smaller than its sum (for termination below).\<close>

lemma size_lt_Su: "x \<in> set xs \<Longrightarrow> size x < size (Su xs)"
  by (induction xs) auto

text \<open>Critical subterms never exceed the size of their host (needed for the
  termination of the ordering below).\<close>

lemma Kn_size: "\<gamma> \<in> Kn n a \<Longrightarrow> size \<gamma> \<le> size a"
proof (induction a arbitrary: \<gamma>)
  case (Om m) thus ?case by (auto split: if_splits)
next
  case (Th m a)
  show ?case
  proof (cases "n < m")
    case True
    with Th.prems have "\<gamma> \<in> Kn n a" by simp
    with Th.IH have "size \<gamma> \<le> size a" by simp
    thus ?thesis by simp
  next
    case False
    with Th.prems have "\<gamma> = Th m a" by simp
    thus ?thesis by simp
  qed
next
  case (Su xs)
  then obtain x where "x \<in> set xs" "\<gamma> \<in> Kn n x" by auto
  with Su.IH have "size \<gamma> \<le> size x" by simp
  moreover have "size x < size (Su xs)" using \<open>x \<in> set xs\<close> by (rule size_lt_Su)
  ultimately show ?case by simp
qed

subsection \<open>The ordering (Towsner Def 2.3)\<close>

text \<open>The strict order \<open>a <\<^sub>o b\<close>.  Sums compare by the one-step multiset order;
  the principal/sum cases by domination; principals \<open>\<Omega>\<close>, \<open>\<vartheta>\<close> by the
  critical-subterm conditions that make the order well-founded.  We inline the
  reflexive closure \<open>\<le>\<^sub>o\<close> as \<open>x <\<^sub>o y \<or> x = y\<close>.\<close>

function (sequential) olt :: "ot \<Rightarrow> ot \<Rightarrow> bool" (infix "<\<^sub>o" 50) where
  "olt (Su xs) (Su ys) =
     (\<exists>b \<in># mset ys - mset xs. \<forall>a \<in># mset xs - mset ys. olt a b)"
| "olt (Su xs) (Om n) = (\<forall>a \<in> set xs. olt a (Om n))"
| "olt (Su xs) (Th n b) = (\<forall>a \<in> set xs. olt a (Th n b))"
| "olt (Om m) (Su ys) = (\<exists>b \<in> set ys. olt (Om m) b \<or> Om m = b)"
| "olt (Th m a) (Su ys) = (\<exists>b \<in> set ys. olt (Th m a) b \<or> Th m a = b)"
| "olt (Om m) (Om n) = (m < n)"
| "olt (Om m) (Th n b) = (\<exists>\<gamma> \<in> Kn n b. olt (Om m) \<gamma> \<or> Om m = \<gamma>)"
| "olt (Th m a) (Om n) = (\<forall>\<gamma> \<in> Kn m a. olt \<gamma> (Om n))"
| "olt (Th m a) (Th n b) =
     ((\<exists>\<gamma> \<in> Kn n b. olt (Th m a) \<gamma> \<or> Th m a = \<gamma>)
      \<or> ((\<forall>\<gamma> \<in> Kn m a. olt \<gamma> (Th n b)) \<and> (m < n \<or> (m = n \<and> olt a b))))"
  by pat_completeness auto

termination
proof (relation "measure (\<lambda>(x,y). size x + size y)")
  show "wf (measure (\<lambda>(x,y). size x + size y))" by simp
next
  fix xs ys :: "ot list" and a b
  assume "b \<in># mset ys - mset xs" "a \<in># mset xs - mset ys"
  hence ab: "a \<in> set xs" "b \<in> set ys"
    by (auto dest!: in_diffD)
  show "((a, b), Su xs, Su ys) \<in> measure (\<lambda>(x,y). size x + size y)"
    using size_lt_Su[OF ab(1)] size_lt_Su[OF ab(2)] by simp
next
  fix xs :: "ot list" and n a
  assume a: "a \<in> set xs"
  show "((a, Om n), Su xs, Om n) \<in> measure (\<lambda>(x,y). size x + size y)"
    using size_lt_Su[OF a] by simp
next
  fix xs :: "ot list" and n b a
  assume a: "a \<in> set xs"
  show "((a, Th n b), Su xs, Th n b) \<in> measure (\<lambda>(x,y). size x + size y)"
    using size_lt_Su[OF a] by simp
next
  fix m :: nat and ys :: "ot list" and b
  assume b: "b \<in> set ys"
  show "((Om m, b), Om m, Su ys) \<in> measure (\<lambda>(x,y). size x + size y)"
    using size_lt_Su[OF b] by simp
next
  fix m :: nat and a and ys :: "ot list" and b
  assume b: "b \<in> set ys"
  show "((Th m a, b), Th m a, Su ys) \<in> measure (\<lambda>(x,y). size x + size y)"
    using size_lt_Su[OF b] by simp
next
  fix m :: nat and n b \<gamma>
  assume "\<gamma> \<in> Kn n b"
  hence "size \<gamma> \<le> size b" by (rule Kn_size)
  thus "((Om m, \<gamma>), Om m, Th n b) \<in> measure (\<lambda>(x,y). size x + size y)"
    by simp
next
  fix m :: nat and a n \<gamma>
  assume "\<gamma> \<in> Kn m a"
  hence "size \<gamma> \<le> size a" by (rule Kn_size)
  thus "((\<gamma>, Om n), Th m a, Om n) \<in> measure (\<lambda>(x,y). size x + size y)"
    by simp
next
  fix m :: nat and a n b \<gamma>
  assume "\<gamma> \<in> Kn n b"
  hence "size \<gamma> \<le> size b" by (rule Kn_size)
  thus "((Th m a, \<gamma>), Th m a, Th n b) \<in> measure (\<lambda>(x,y). size x + size y)"
    by simp
next
  fix m :: nat and a n b \<gamma>
  assume "\<gamma> \<in> Kn m a"
  hence "size \<gamma> \<le> size a" by (rule Kn_size)
  thus "((\<gamma>, Th n b), Th m a, Th n b) \<in> measure (\<lambda>(x,y). size x + size y)"
    by simp
next
  fix m :: nat and a n b
  show "((a, b), Th m a, Th n b) \<in> measure (\<lambda>(x,y). size x + size y)"
    by simp
qed

abbreviation ole :: "ot \<Rightarrow> ot \<Rightarrow> bool" (infix "\<le>\<^sub>o" 50) where
  "x \<le>\<^sub>o y \<equiv> (x <\<^sub>o y \<or> x = y)"

subsection \<open>Basic order facts\<close>

text \<open>\<open>Zero\<close> (the empty sum) is the least term, and nothing is below it.\<close>

lemma not_olt_Zero [simp]: "\<not> (x <\<^sub>o Zero)"
  by (cases x) auto

lemma olt_Zero_iff: "Zero <\<^sub>o x \<longleftrightarrow> x \<noteq> Zero"
  by (cases x) (auto simp: ex_in_conv)

lemma olt_ZeroI: "x \<noteq> Zero \<Longrightarrow> Zero <\<^sub>o x"
  by (simp add: olt_Zero_iff)

subsection \<open>Sums compare by the multiset extension\<close>

abbreviation oltR :: "(ot \<times> ot) set" where
  "oltR \<equiv> {(a,b). a <\<^sub>o b}"

text \<open>Towsner's one-step sum order (Def 2.3, first clause) is contained in the
  Dershowitz\<dash>Manna multiset extension of \<open><\<^sub>o\<close>.  Hence (via @{thm [source]
  wf_mult}) well-foundedness on summands lifts to well-foundedness on sums,
  without first establishing linearity.\<close>

lemma olt_Su_imp_mult:
  assumes "Su xs <\<^sub>o Su ys"
  shows "(mset xs, mset ys) \<in> mult oltR"
proof -
  from assms obtain b where b: "b \<in># mset ys - mset xs"
      and dom: "\<forall>a \<in># mset xs - mset ys. a <\<^sub>o b" by auto
  let ?I = "mset xs \<inter># mset ys"
  have x: "mset xs = ?I + (mset xs - mset ys)"
    by (simp add: multiset_eq_iff min_def)
  have y: "mset ys = ?I + (mset ys - mset xs)"
    by (simp add: multiset_eq_iff min_def)
  have ne: "mset ys - mset xs \<noteq> {#}" using b by auto
  have step: "\<forall>k \<in># mset xs - mset ys. \<exists>j \<in># mset ys - mset xs. (k, j) \<in> oltR"
    using dom b by auto
  have "(?I + (mset xs - mset ys), ?I + (mset ys - mset xs)) \<in> mult oltR"
    by (rule one_step_implies_mult[OF ne step])
  thus ?thesis using x y by simp
qed

subsection \<open>Reducing well-foundedness of \<open><\<^sub>o\<close> to the principal terms\<close>

text \<open>A well-formed term: sums contain only principal summands and are never a
  singleton (Towsner's \<open>n \<noteq> 1\<close> condition).  The PSS embedding lands here.\<close>

fun wfo :: "ot \<Rightarrow> bool" where
  "wfo (Om n) = True"
| "wfo (Th n a) = wfo a"
| "wfo (Su xs) = (length xs \<noteq> 1 \<and> (\<forall>x \<in> set xs. isH x \<and> wfo x))"

text \<open>The multiset of principal summands of a term.\<close>

fun bag :: "ot \<Rightarrow> ot multiset" where
  "bag (Om n) = {# Om n #}"
| "bag (Th n a) = {# Th n a #}"
| "bag (Su xs) = mset xs"

abbreviation principalR :: "(ot \<times> ot) set" where
  "principalR \<equiv> {(a,b). a <\<^sub>o b \<and> isH a \<and> isH b}"

lemma mult_single_dom: "\<forall>k \<in># K. (k, j) \<in> r \<Longrightarrow> (K, {# j #}) \<in> mult r"
  using one_step_implies_mult[of "{# j #}" K r "{#}"] by simp

lemma mult_add: "N \<noteq> {#} \<Longrightarrow> (M, M + N) \<in> mult r"
  using one_step_implies_mult[of N "{#}" r M] by simp

lemma mult_dom_set:
  assumes "j \<in># J" "(a, j) \<in> r" shows "({# a #}, J) \<in> mult r"
proof -
  have "J \<noteq> {#}" using assms(1) by auto
  moreover have "\<forall>k \<in># {# a #}. \<exists>j' \<in># J. (k, j') \<in> r" using assms by auto
  ultimately show ?thesis using one_step_implies_mult[of J "{# a #}" r "{#}"] by simp
qed

text \<open>The \<open>bag\<close> map sends \<open><\<^sub>o\<close> on well-formed terms into the multiset extension
  of the principal order.\<close>

lemma bag_mono:
  assumes "wfo a" "wfo b" "a <\<^sub>o b"
  shows "(bag a, bag b) \<in> mult principalR"
  using assms
proof (cases a)
  case a_Su: (Su xs)
  show ?thesis
  proof (cases b)
    case b_Su: (Su ys)
    \<comment> \<open>sum vs sum: reuse the one-step construction with principal witnesses\<close>
    from \<open>a <\<^sub>o b\<close> a_Su b_Su obtain c
      where c: "c \<in># mset ys - mset xs"
        and dom: "\<forall>z \<in># mset xs - mset ys. z <\<^sub>o c" by auto
    let ?I = "mset xs \<inter># mset ys"
    have x: "mset xs = ?I + (mset xs - mset ys)" by (simp add: multiset_eq_iff min_def)
    have y: "mset ys = ?I + (mset ys - mset xs)" by (simp add: multiset_eq_iff min_def)
    have ne: "mset ys - mset xs \<noteq> {#}" using c by auto
    have "\<forall>k \<in># mset xs - mset ys. \<exists>j \<in># mset ys - mset xs. (k, j) \<in> principalR"
    proof
      fix k assume k: "k \<in># mset xs - mset ys"
      hence "k \<in> set xs" by (meson in_diffD set_mset_mset in_multiset_in_set)
      with a_Su \<open>wfo a\<close> have "isH k" by auto
      moreover have "c \<in> set ys" using c by (meson in_diffD set_mset_mset in_multiset_in_set)
      with b_Su \<open>wfo b\<close> have "isH c" by auto
      moreover have "k <\<^sub>o c" using dom k by auto
      ultimately show "\<exists>j \<in># mset ys - mset xs. (k, j) \<in> principalR" using c by auto
    qed
    hence "(?I + (mset xs - mset ys), ?I + (mset ys - mset xs)) \<in> mult principalR"
      by (rule one_step_implies_mult[OF ne])
    thus ?thesis using a_Su b_Su x y by simp
  next
    case b_Om: (Om n)
    have "\<forall>k \<in># mset xs. (k, Om n) \<in> principalR"
      using a_Su b_Om \<open>a <\<^sub>o b\<close> \<open>wfo a\<close> by auto
    hence "(mset xs, {# Om n #}) \<in> mult principalR" by (rule mult_single_dom)
    thus ?thesis using a_Su b_Om by simp
  next
    case b_Th: (Th n d)
    have "\<forall>k \<in># mset xs. (k, Th n d) \<in> principalR"
      using a_Su b_Th \<open>a <\<^sub>o b\<close> \<open>wfo a\<close> by auto
    hence "(mset xs, {# Th n d #}) \<in> mult principalR" by (rule mult_single_dom)
    thus ?thesis using a_Su b_Th by simp
  qed
next
  case a_pr: (Om m)
  show ?thesis
  proof (cases b)
    case (Su ys)
    \<comment> \<open>principal vs sum: a \<le> some summand y\<close>
    from \<open>a <\<^sub>o b\<close> a_pr Su obtain y where y: "y \<in> set ys" and le: "a <\<^sub>o y \<or> a = y"
      using a_pr by auto
    show ?thesis
    proof (cases "a <\<^sub>o y")
      case True
      have hy: "isH y" using y Su \<open>wfo b\<close> by auto
      have "y \<in># mset ys" using y by simp
      moreover have "(a, y) \<in> principalR" using True hy a_pr by auto
      ultimately have "({# a #}, mset ys) \<in> mult principalR" by (rule mult_dom_set)
      thus ?thesis using a_pr Su by simp
    next
      case False
      with le have ay: "a = y" by simp
      have ain: "a \<in># mset ys" using y ay by simp
      have eq: "mset ys = {# a #} + (mset ys - {# a #})"
        using ain by (metis insert_DiffM add_mset_add_single add.commute)
      have "ys \<noteq> []" using y by auto
      hence "1 \<le> length ys" by (simp add: Suc_le_eq)
      moreover have "length ys \<noteq> 1" using Su \<open>wfo b\<close> by simp
      ultimately have "2 \<le> length ys" by linarith
      hence "1 \<le> size (mset ys - {# a #})" using ain by (simp add: size_Diff_singleton)
      hence ne: "mset ys - {# a #} \<noteq> {#}" by auto
      have "({# a #}, mset ys) \<in> mult principalR"
        using mult_add[of "mset ys - {# a #}" "{# a #}" principalR, OF ne] eq by simp
      thus ?thesis using a_pr Su by simp
    qed
  next
    case (Om n)
    hence "(a, b) \<in> principalR" using a_pr \<open>a <\<^sub>o b\<close> by auto
    hence "({# a #}, {# b #}) \<in> mult principalR" using mult_single_dom[of "{# a #}" b] by simp
    thus ?thesis using a_pr Om by simp
  next
    case (Th n d)
    hence "(a, b) \<in> principalR" using a_pr \<open>a <\<^sub>o b\<close> by auto
    hence "({# a #}, {# b #}) \<in> mult principalR" using mult_single_dom[of "{# a #}" b] by simp
    thus ?thesis using a_pr Th by simp
  qed
next
  case a_pr: (Th m e)
  show ?thesis
  proof (cases b)
    case (Su ys)
    from \<open>a <\<^sub>o b\<close> a_pr Su obtain y where y: "y \<in> set ys" and le: "a <\<^sub>o y \<or> a = y"
      using a_pr by auto
    show ?thesis
    proof (cases "a <\<^sub>o y")
      case True
      have hy: "isH y" using y Su \<open>wfo b\<close> by auto
      have "y \<in># mset ys" using y by simp
      moreover have "(a, y) \<in> principalR" using True hy a_pr by auto
      ultimately have "({# a #}, mset ys) \<in> mult principalR" by (rule mult_dom_set)
      thus ?thesis using a_pr Su by simp
    next
      case False
      with le have ay: "a = y" by simp
      have ain: "a \<in># mset ys" using y ay by simp
      have eq: "mset ys = {# a #} + (mset ys - {# a #})"
        using ain by (metis insert_DiffM add_mset_add_single add.commute)
      have "ys \<noteq> []" using y by auto
      hence "1 \<le> length ys" by (simp add: Suc_le_eq)
      moreover have "length ys \<noteq> 1" using Su \<open>wfo b\<close> by simp
      ultimately have "2 \<le> length ys" by linarith
      hence "1 \<le> size (mset ys - {# a #})" using ain by (simp add: size_Diff_singleton)
      hence ne: "mset ys - {# a #} \<noteq> {#}" by auto
      have "({# a #}, mset ys) \<in> mult principalR"
        using mult_add[of "mset ys - {# a #}" "{# a #}" principalR, OF ne] eq by simp
      thus ?thesis using a_pr Su by simp
    qed
  next
    case (Om n)
    hence "(a, b) \<in> principalR" using a_pr \<open>a <\<^sub>o b\<close> by auto
    hence "({# a #}, {# b #}) \<in> mult principalR" using mult_single_dom[of "{# a #}" b] by simp
    thus ?thesis using a_pr Om by simp
  next
    case (Th n d)
    hence "(a, b) \<in> principalR" using a_pr \<open>a <\<^sub>o b\<close> by auto
    hence "({# a #}, {# b #}) \<in> mult principalR" using mult_single_dom[of "{# a #}" b] by simp
    thus ?thesis using a_pr Th by simp
  qed
qed

text \<open>Hence well-foundedness on principal terms lifts to all well-formed terms.\<close>

theorem wf_olt_of_principal:
  assumes "wf principalR"
  shows "wf {(a,b). a <\<^sub>o b \<and> wfo a \<and> wfo b}"
proof (rule wf_subset)
  show "wf (inv_image (mult principalR) bag)"
    by (rule wf_inv_image[OF wf_mult[OF assms]])
  show "{(a,b). a <\<^sub>o b \<and> wfo a \<and> wfo b} \<subseteq> inv_image (mult principalR) bag"
  proof (rule subsetI, clarify)
    fix a b assume "a <\<^sub>o b" "wfo a" "wfo b"
    thus "(a, b) \<in> inv_image (mult principalR) bag"
      using bag_mono[OF \<open>wfo a\<close> \<open>wfo b\<close> \<open>a <\<^sub>o b\<close>] by (simp add: inv_image_def)
  qed
qed

end
