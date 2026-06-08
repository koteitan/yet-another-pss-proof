theory wo
  imports "HOL-Library.Multiset" "HOL-Library.Multiset_Order"
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
    Om int            \<comment> \<open>\<open>\<Omega>\<^bsub>J\<^esub>\<close>, \<open>J \<in> \<int>\<close> (de Bruijn-style levels; the WF proof shifts these)\<close>
  | Th int ot         \<comment> \<open>\<open>\<vartheta>\<^bsub>J\<^esub> a\<close>\<close>
  | Su "ot list"      \<comment> \<open>\<open>#{x\<^sub>0,\<dots>}\<close>, summands principal, length \<open>\<noteq> 1\<close>; \<open>Su [] = 0\<close>\<close>

abbreviation Zero :: ot where "Zero \<equiv> Su []"

text \<open>The principal (Buchholz \<open>H\<close>) terms.\<close>

fun isH :: "ot \<Rightarrow> bool" where
  "isH (Om _) = True"
| "isH (Th _ _) = True"
| "isH (Su _) = False"

text \<open>\<open>\<Omega>\<close>-free terms (no \<^const>\<open>Om\<close> anywhere): the PSS embedding lands here, and the
  well-foundedness target is restricted to these (the \<open>\<Omega>\<^bsub>n\<^esub>\<close> are only proof
  scaffolding, and the full \<^typ>\<open>int\<close>-level order is ill-founded via \<open>\<Omega>\<^bsub>-k\<^esub>\<close>).\<close>

fun omfree :: "ot \<Rightarrow> bool" where
  "omfree (Om _) = False"
| "omfree (Th _ a) = omfree a"
| "omfree (Su xs) = (\<forall>x \<in> set xs. omfree x)"

subsection \<open>Formal cardinalities (Towsner Def 2.4)\<close>

text \<open>\<open>FCset a\<close> is the set of cardinal levels occurring free in \<open>a\<close>;
  \<open>FC\<^bsub>n\<^esub>(\<vartheta>\<^sub>n a) = FC(a) \<setminus> {m. m \<ge> n}\<close>.\<close>

fun FCset :: "ot \<Rightarrow> int set" where
  "FCset (Om n) = {n}"
| "FCset (Th n a) = {m \<in> FCset a. m < n}"
| "FCset (Su xs) = (\<Union>x \<in> set xs. FCset x)"

lemma finite_FCset [simp]: "finite (FCset a)"
  by (induction a) auto

definition FC :: "ot \<Rightarrow> int" where
  "FC a = (if FCset a = {} then 0 else Max (FCset a))"

subsection \<open>Critical subterms (Towsner Def 2.2)\<close>

text \<open>\<open>Kn n a\<close> collects the maximal subterms of \<open>a\<close> of cardinality \<open>\<le> n\<close>:
  \<open>K\<^sub>n \<Omega>\<^sub>m = {\<Omega>\<^sub>m}\<close> iff \<open>m < n\<close>, and \<open>K\<^sub>n \<vartheta>\<^sub>m a = {\<vartheta>\<^sub>m a}\<close> iff \<open>m \<le> n\<close> (else recurse).\<close>

fun Kn :: "int \<Rightarrow> ot \<Rightarrow> ot set" where
  "Kn n (Om m) = (if m < n then {Om m} else {})"
| "Kn n (Th m a) = (if n < m then Kn n a else {Th m a})"
| "Kn n (Su xs) = (\<Union>x \<in> set xs. Kn n x)"

lemma finite_Kn [simp]: "finite (Kn n a)"
  by (induction a) auto

lemma Kn_isH: "\<gamma> \<in> Kn n a \<Longrightarrow> isH \<gamma>"
  by (induction a) (auto split: if_splits)

text \<open>The cardinalities of a critical subterm \<open>\<gamma> \<in> Kn n a\<close> are exactly the
  cardinalities of \<open>a\<close> below \<open>n\<close>; hence \<open>FC \<gamma> \<le> FC (\<vartheta>\<^sub>n a)\<close>.\<close>

lemma FCset_Kn: "\<gamma> \<in> Kn n a \<Longrightarrow> FCset \<gamma> \<subseteq> {k \<in> FCset a. k < n}"
proof (induction a arbitrary: \<gamma>)
  case (Om m) thus ?case by (auto split: if_splits)
next
  case (Th p e)
  show ?case
  proof (cases "n < p")
    case True
    with Th.prems have "\<gamma> \<in> Kn n e" by simp
    with Th.IH have "FCset \<gamma> \<subseteq> {k \<in> FCset e. k < n}" by simp
    thus ?thesis using True by auto
  next
    case False
    with Th.prems have "\<gamma> = Th p e" by simp
    thus ?thesis using False by auto
  qed
next
  case (Su xs)
  then obtain x where x: "x \<in> set xs" "\<gamma> \<in> Kn n x" by auto
  with Su.IH have hsub: "FCset \<gamma> \<subseteq> {k \<in> FCset x. k < n}" by simp
  show ?case
  proof
    fix xa assume "xa \<in> FCset \<gamma>"
    with hsub have "xa \<in> FCset x" "xa < n" by auto
    with x(1) show "xa \<in> {k \<in> FCset (Su xs). k < n}" by auto
  qed
qed

lemma FCset_Th_eq_Kn: "FCset (Th n a) = (\<Union>\<gamma> \<in> Kn n a. FCset \<gamma>)"
proof (induction a)
  case (Om m) thus ?case by auto
next
  case (Th p e)
  show ?case
  proof (cases "n < p")
    case True
    have "FCset (Th n (Th p e)) = {k \<in> FCset e. k < n}" using True by auto
    also have "\<dots> = (\<Union>\<gamma>\<in>Kn n e. FCset \<gamma>)" using Th.IH by simp
    also have "\<dots> = (\<Union>\<gamma>\<in>Kn n (Th p e). FCset \<gamma>)" using True by simp
    finally show ?thesis .
  next
    case False
    have "FCset (Th n (Th p e)) = {k \<in> FCset e. k < p}" using False by auto
    also have "\<dots> = FCset (Th p e)" by simp
    also have "\<dots> = (\<Union>\<gamma>\<in>Kn n (Th p e). FCset \<gamma>)" using False by simp
    finally show ?thesis .
  qed
next
  case (Su xs) thus ?case by auto
qed

lemma FC_nonempty: "FCset t \<noteq> {} \<Longrightarrow> FC t = Max (FCset t)"
  by (simp add: FC_def)

text \<open>(The old \<open>FC\<close>-stratification lemmas \<open>FC_Th_le\<close>/\<open>FC_Kn\<close>/\<open>FC_mono_pr\<close> are dropped:
  with \<^typ>\<open>int\<close> levels they no longer hold under the \<open>FC \<emptyset> = 0\<close> convention, and the
  well-foundedness proof now stratifies by the \<^emph>\<open>ground\<close> \<open>G\<close> (Towsner Def 3.6\<dash>3.7),
  not by the top cardinality \<open>FC\<close>.)\<close>

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
  fix m :: int and ys :: "ot list" and b
  assume b: "b \<in> set ys"
  show "((Om m, b), Om m, Su ys) \<in> measure (\<lambda>(x,y). size x + size y)"
    using size_lt_Su[OF b] by simp
next
  fix m :: int and a and ys :: "ot list" and b
  assume b: "b \<in> set ys"
  show "((Th m a, b), Th m a, Su ys) \<in> measure (\<lambda>(x,y). size x + size y)"
    using size_lt_Su[OF b] by simp
next
  fix m :: int and n b \<gamma>
  assume "\<gamma> \<in> Kn n b"
  hence "size \<gamma> \<le> size b" by (rule Kn_size)
  thus "((Om m, \<gamma>), Om m, Th n b) \<in> measure (\<lambda>(x,y). size x + size y)"
    by simp
next
  fix m :: int and a n \<gamma>
  assume "\<gamma> \<in> Kn m a"
  hence "size \<gamma> \<le> size a" by (rule Kn_size)
  thus "((\<gamma>, Om n), Th m a, Om n) \<in> measure (\<lambda>(x,y). size x + size y)"
    by simp
next
  fix m :: int and a n b \<gamma>
  assume "\<gamma> \<in> Kn n b"
  hence "size \<gamma> \<le> size b" by (rule Kn_size)
  thus "((Th m a, \<gamma>), Th m a, Th n b) \<in> measure (\<lambda>(x,y). size x + size y)"
    by simp
next
  fix m :: int and a n b \<gamma>
  assume "\<gamma> \<in> Kn m a"
  hence "size \<gamma> \<le> size a" by (rule Kn_size)
  thus "((\<gamma>, Th n b), Th m a, Th n b) \<in> measure (\<lambda>(x,y). size x + size y)"
    by simp
next
  fix m :: int and a n b
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

text \<open>Each critical subterm is strictly below the collapse (it is its own witness).\<close>

lemma Kn_lt_Th:
  assumes "\<gamma> \<in> Kn n a" shows "\<gamma> <\<^sub>o Th n a"
proof (cases \<gamma>)
  case (Om p) thus ?thesis using assms by auto
next
  case (Th p e) thus ?thesis using assms by auto
next
  case (Su xs)
  with assms Kn_isH[OF assms] show ?thesis by simp
qed

text \<open>A principal dominated by a critical subterm of \<open>Th q b\<close> is below \<open>Th q b\<close>
  (the critical-subterm clause of the ordering provides the witness; no
  transitivity needed).\<close>

lemma olt_Th_of_le_Kn:
  assumes "isH \<gamma>" "\<delta> \<in> Kn q b" "\<gamma> \<le>\<^sub>o \<delta>"
  shows "\<gamma> <\<^sub>o Th q b"
  using assms by (cases \<gamma>) auto

text \<open>Critical subterms only coarsen as the level rises: a level-\<open>n\<close> critical
  subterm is dominated by a level-\<open>r\<close> one (for \<open>n \<le> r\<close>).  Proved directly by
  recursion on the host term, using @{thm [source] olt_Th_of_le_Kn} \<dash> crucially
  \<^emph>\<open>without\<close> general transitivity of \<open><\<^sub>o\<close>.\<close>

lemma Kn_mono_le:
  "\<gamma> \<in> Kn n a \<Longrightarrow> n \<le> r \<Longrightarrow> \<exists>\<delta> \<in> Kn r a. \<gamma> \<le>\<^sub>o \<delta>"
proof (induction a arbitrary: \<gamma> n r)
  case (Om m) thus ?case by (auto split: if_splits)
next
  case (Th q b)
  show ?case
  proof (cases "n < q")
    case True
    with Th.prems have gb: "\<gamma> \<in> Kn n b" by simp
    show ?thesis
    proof (cases "r < q")
      case True
      with gb Th.IH[OF gb \<open>n \<le> r\<close>] show ?thesis by simp
    next
      case False
      hence kr: "Kn r (Th q b) = {Th q b}" by simp
      from Th.IH[OF gb, of q] \<open>n < q\<close>
      obtain \<delta> where d: "\<delta> \<in> Kn q b" "\<gamma> \<le>\<^sub>o \<delta>" by auto
      have "isH \<gamma>" using gb by (rule Kn_isH)
      hence "\<gamma> <\<^sub>o Th q b" using olt_Th_of_le_Kn[OF _ d] by simp
      thus ?thesis using kr by auto
    qed
  next
    case False
    with Th.prems have "\<gamma> = Th q b" by simp
    moreover from False \<open>n \<le> r\<close> have "Kn r (Th q b) = {Th q b}" by simp
    ultimately show ?thesis by auto
  qed
next
  case (Su xs)
  then obtain x where x: "x \<in> set xs" "\<gamma> \<in> Kn n x" by auto
  from Su.IH[OF x(1) x(2) \<open>n \<le> r\<close>] obtain \<delta> where "\<delta> \<in> Kn r x" "\<gamma> \<le>\<^sub>o \<delta>" by auto
  thus ?case using x(1) by auto
qed

text \<open>Hence a level-\<open>n\<close> critical subterm is below \<open>Th r a\<close> for any \<open>r \<ge> n\<close>.\<close>

lemma KnTh:
  assumes "\<gamma> \<in> Kn n a" "n \<le> r" shows "\<gamma> <\<^sub>o Th r a"
proof -
  from Kn_mono_le[OF assms] obtain \<delta> where "\<delta> \<in> Kn r a" "\<gamma> \<le>\<^sub>o \<delta>" by auto
  thus ?thesis using olt_Th_of_le_Kn[OF Kn_isH[OF assms(1)]] by simp
qed

text \<open>\<^bold>\<open>Critical-subterm domination by a higher collapse.\<close>  A level-\<open>a\<close> critical
  subterm of an \<open>\<Omega>\<close>-free term is strictly below \<open>\<vartheta>\<^bsub>e\<^esub> D\<close> for \<^emph>\<open>any\<close> argument \<open>D\<close>,
  provided \<open>a < e\<close>.  This is the \<open>K\<close>-condition powering the embedding's
  order-preservation in the \<open>a < e\<close> case (theory \<open>embed\<close>): the subscript drop
  alone dominates, irrespective of the arguments.  (\<open>\<Omega>\<close>-freeness is essential \<dash>
  \<open>\<Omega>\<^bsub>m\<^esub> \<in> K\<^bsub>a\<^esub> \<Omega>\<^bsub>m\<^esub>\<close> is \<^emph>\<open>not\<close> below \<open>\<vartheta>\<^bsub>e\<^esub> 0\<close>.)  Proved by induction on the host \<open>c\<close>,
  mirroring \<^const>\<open>Kn\<close>'s recursion.\<close>

lemma Kn_dom:
  "omfree c \<Longrightarrow> \<gamma> \<in> Kn a c \<Longrightarrow> a < e \<Longrightarrow> \<gamma> <\<^sub>o Th e D"
proof (induction c arbitrary: \<gamma> a e D)
  case (Om m) thus ?case by simp
next
  case (Th m b)
  show ?case
  proof (cases "a < m")
    case True
    with Th.prems(2) have "\<gamma> \<in> Kn a b" by simp
    moreover have "omfree b" using Th.prems(1) by simp
    ultimately show ?thesis using Th.IH Th.prems(3) by blast
  next
    case False
    with Th.prems(2) have g: "\<gamma> = Th m b" by simp
    have me: "m < e" using False Th.prems(3) by simp
    have "\<forall>\<delta> \<in> Kn m b. \<delta> <\<^sub>o Th e D"
    proof
      fix \<delta> assume d: "\<delta> \<in> Kn m b"
      have "omfree b" using Th.prems(1) by simp
      thus "\<delta> <\<^sub>o Th e D" using Th.IH[OF _ d me] by blast
    qed
    thus ?thesis using g me by simp
  qed
next
  case (Su xs)
  then obtain x where x: "x \<in> set xs" "\<gamma> \<in> Kn a x" by auto
  have ox: "omfree x" using Su.prems(1) x(1) by simp
  show ?case using Su.IH[OF x(1) ox x(2) Su.prems(3)] .
qed

text \<open>A strictly smaller subscript makes a collapse strictly smaller, \<^emph>\<open>regardless\<close>
  of the arguments (for \<open>\<Omega>\<close>-free left argument): \<open>\<vartheta>\<^bsub>m\<^esub> g <\<^sub>o \<vartheta>\<^bsub>n\<^esub> h\<close> whenever \<open>m < n\<close>.
  Immediate from @{thm [source] Kn_dom}.  This is the leading-subscript clause of
  the embedding's order-preservation.\<close>

lemma Th_lt_of_sub_lt:
  assumes "omfree g" "m < n" shows "Th m g <\<^sub>o Th n h"
proof -
  have "\<forall>\<gamma>\<in>Kn m g. \<gamma> <\<^sub>o Th n h" using Kn_dom[OF assms(1) _ assms(2)] by blast
  thus ?thesis using assms(2) by simp
qed

text \<open>Every critical subterm is \<open>\<le>\<^sub>o\<close> its host (again without transitivity).\<close>

lemma Kn_le_self: "\<gamma> \<in> Kn n d \<Longrightarrow> \<gamma> \<le>\<^sub>o d"
proof (induction d arbitrary: \<gamma> n)
  case (Om m) thus ?case by (auto split: if_splits)
next
  case (Th q b)
  show ?case
  proof (cases "n < q")
    case True
    with Th.prems have "\<gamma> \<in> Kn n b" by simp
    hence "\<gamma> <\<^sub>o Th q b" using KnTh[of \<gamma> n b q] True by simp
    thus ?thesis by simp
  next
    case False
    with Th.prems have "\<gamma> = Th q b" by simp
    thus ?thesis by simp
  qed
next
  case (Su xs)
  then obtain x where x: "x \<in> set xs" "\<gamma> \<in> Kn n x" by auto
  from Su.IH[OF x(1) x(2)] have "\<gamma> \<le>\<^sub>o x" .
  moreover have "isH \<gamma>" using x(2) by (rule Kn_isH)
  ultimately show ?case using x(1) by (cases \<gamma>) auto
qed

subsection \<open>The countable fragment (\<open>M\<^bsub>-\<infinity>\<^esub>\<close>) is downward closed\<close>

text \<open>A term is \<^emph>\<open>countable\<close> (Towsner's formal cardinality \<open>-\<infinity>\<close>, the bottom level
  \<open>M\<^bsub>-\<infinity>\<^esub>\<close> of Def 3.7) when it has no \<^emph>\<open>free\<close> \<open>\<Omega>\<close> at all, i.e.\ \<^term>\<open>FCset t = {}\<close>.
  This is the genuine well-foundedness target: it is strictly larger than the
  \<^const>\<open>omfree\<close> terms (e.g.\ \<open>\<vartheta>\<^bsub>0\<^esub> \<Omega>\<^bsub>5\<^esub>\<close> is countable but not \<open>\<Omega>\<close>-free \<dash> the \<open>\<Omega>\<^bsub>5\<^esub>\<close> is
  \<^emph>\<open>bound\<close> by the collapse), and that extra \<open>\<Omega>\<close>-scaffolding is exactly what the
  collapse accessibility argument needs as predecessors.  The embedding image is
  \<open>\<Omega>\<close>-free, hence countable.\<close>

abbreviation cntbl :: "ot \<Rightarrow> bool" where
  "cntbl t \<equiv> FCset t = {}"

lemma omfree_imp_cntbl: "omfree t \<Longrightarrow> cntbl t"
  by (induction t) auto

text \<open>Countability is preserved downward by \<open><\<^sub>o\<close>: a predecessor of a countable
  term is countable.  Hence the countable terms form a \<open><\<^sub>o\<close>-downward-closed set,
  and accessibility within them is genuine accessibility.  Proved by induction on
  \<open>size x + size y\<close> (mirroring \<^const>\<open>olt\<close>'s own recursion), using @{thm [source]
  FCset_Kn} and @{thm [source] FCset_Th_eq_Kn}.\<close>

lemma cntbl_downclosed:
  assumes "x <\<^sub>o y" "cntbl y" shows "cntbl x"
proof -
  have "x <\<^sub>o y \<longrightarrow> cntbl y \<longrightarrow> cntbl x"
  proof (induction "size x + size y" arbitrary: x y rule: less_induct)
    case less
    have IH: "cntbl x'" if "size x' + size y' < size x + size y" "x' <\<^sub>o y'" "cntbl y'"
      for x' y' using less.hyps[OF that(1)] that(2,3) by blast
    show ?case
    proof (intro impI)
      assume xy: "x <\<^sub>o y" and cy: "cntbl y"
      show "cntbl x"
      proof (cases x)
        case (Om m)
        \<comment> \<open>\<open>\<Omega>\<^bsub>m\<^esub>\<close> has \<open>FCset = {m} \<noteq> {}\<close>; we derive a contradiction from \<open>cy\<close>\<close>
        have False
        proof (cases y)
          case (Om n) thus False using cy by simp
        next
          case (Su ys)
          from xy Om Su obtain b where b: "b \<in> set ys" "Om m \<le>\<^sub>o b" by auto
          have cb: "cntbl b" using cy Su b(1) by auto
          show False using b(2)
          proof
            assume "Om m <\<^sub>o b"
            moreover have "size (Om m) + size b < size x + size y"
              using Om Su size_lt_Su[OF b(1)] by simp
            ultimately have "cntbl (Om m)" using cb IH by blast
            thus False by simp
          next
            assume "Om m = b" hence "b = Om m" by simp
            thus False using cb by simp
          qed
        next
          case (Th n c)
          from xy Om Th obtain \<gamma> where g: "\<gamma> \<in> Kn n c" "Om m \<le>\<^sub>o \<gamma>" by auto
          have cg: "cntbl \<gamma>" using FCset_Kn[OF g(1)] cy Th by auto
          show False using g(2)
          proof
            assume "Om m <\<^sub>o \<gamma>"
            moreover have "size (Om m) + size \<gamma> < size x + size y"
              using Om Th Kn_size[OF g(1)] by simp
            ultimately have "cntbl (Om m)" using cg IH by blast
            thus False by simp
          next
            assume "Om m = \<gamma>" hence "\<gamma> = Om m" by simp
            thus False using cg by simp
          qed
        qed
        thus ?thesis ..
      next
        case (Su xs)
        note xSu = Su
        have "\<forall>v \<in> set xs. cntbl v"
        proof
          fix v assume v: "v \<in> set xs"
          show "cntbl v"
          proof (cases y)
            case (Om n) thus ?thesis using cy by simp
          next
            case (Th n c)
            have "v <\<^sub>o Th n c" using xy xSu Th v by auto
            moreover have "size v + size (Th n c) < size x + size y"
              using xSu Th size_lt_Su[OF v] by simp
            ultimately show ?thesis using cy Th IH by blast
          next
            case (Su ys)
            show ?thesis
            proof (cases "v \<in> set ys")
              case True thus ?thesis using cy Su by auto
            next
              case False
              \<comment> \<open>\<open>v\<close> survives the multiset difference, so it is dominated by the witness\<close>
              from xy xSu Su obtain b
                where b: "b \<in># mset ys - mset xs"
                  and dom: "\<forall>a \<in># mset xs - mset ys. a <\<^sub>o b" by auto
              have vdiff: "v \<in># mset xs - mset ys"
              proof -
                have c1: "0 < count (mset xs) v" using v by (simp add: count_greater_zero_iff)
                have c2: "count (mset ys) v = 0" using False by (simp add: count_eq_zero_iff)
                have "count (mset ys) v < count (mset xs) v" using c1 c2 by linarith
                thus ?thesis by (simp add: in_diff_count)
              qed
              have vb: "v <\<^sub>o b" using dom vdiff by blast
              have bset: "b \<in> set ys" using b by (auto dest: in_diffD)
              have cb: "cntbl b" using cy Su bset by auto
              have "size v + size b < size x + size y"
                using xSu Su size_lt_Su[OF v] size_lt_Su[OF bset] by simp
              thus ?thesis using vb cb IH by blast
            qed
          qed
        qed
        thus ?thesis using xSu by auto
      next
        case (Th m a)
        note xTh = Th
        show ?thesis
        proof (cases y)
          case (Om n) thus ?thesis using cy by simp
        next
          case (Su ys)
          from xy xTh Su obtain b where b: "b \<in> set ys" "Th m a \<le>\<^sub>o b" by auto
          have cb: "cntbl b" using cy Su b(1) by auto
          show ?thesis using b(2)
          proof
            assume "Th m a <\<^sub>o b"
            moreover have "size (Th m a) + size b < size x + size y"
              using xTh Su size_lt_Su[OF b(1)] by simp
            ultimately show ?thesis using xTh cb IH by blast
          next
            assume "Th m a = b" hence "b = Th m a" by simp
            thus ?thesis using cb xTh by simp
          qed
        next
          case (Th n b)
          have cthb: "cntbl (Th n b)" using cy Th by simp
          from xy xTh Th
          have disj: "(\<exists>\<gamma>\<in>Kn n b. Th m a \<le>\<^sub>o \<gamma>)
              \<or> ((\<forall>\<gamma>\<in>Kn m a. \<gamma> <\<^sub>o Th n b) \<and> (m < n \<or> (m = n \<and> a <\<^sub>o b)))" by simp
          from disj show ?thesis
          proof
            assume "\<exists>\<gamma>\<in>Kn n b. Th m a \<le>\<^sub>o \<gamma>"
            then obtain \<gamma> where g: "\<gamma> \<in> Kn n b" "Th m a \<le>\<^sub>o \<gamma>" by auto
            have cg: "cntbl \<gamma>" using FCset_Kn[OF g(1)] cthb by auto
            show ?thesis using g(2)
            proof
              assume "Th m a <\<^sub>o \<gamma>"
              moreover have "size (Th m a) + size \<gamma> < size x + size y"
                using xTh Th Kn_size[OF g(1)] by simp
              ultimately show ?thesis using xTh cg IH by blast
            next
              assume "Th m a = \<gamma>" hence "\<gamma> = Th m a" by simp
              thus ?thesis using cg xTh by simp
            qed
          next
            assume A: "(\<forall>\<gamma>\<in>Kn m a. \<gamma> <\<^sub>o Th n b) \<and> (m < n \<or> (m = n \<and> a <\<^sub>o b))"
            have "FCset (Th m a) = (\<Union>\<gamma>\<in>Kn m a. FCset \<gamma>)" by (rule FCset_Th_eq_Kn)
            also have "\<dots> = {}"
            proof -
              have "FCset \<gamma> = {}" if g: "\<gamma> \<in> Kn m a" for \<gamma>
              proof -
                have "\<gamma> <\<^sub>o Th n b" using A g by blast
                moreover have "size \<gamma> + size (Th n b) < size x + size y"
                  using xTh Th Kn_size[OF g] by simp
                ultimately show ?thesis using cthb IH by blast
              qed
              thus ?thesis by simp
            qed
            finally show ?thesis using xTh by simp
          qed
        qed
      qed
    qed
  qed
  with assms show ?thesis by blast
qed

subsection \<open>Monotonicity in an \<open>\<Omega>\<close> upper bound\<close>

text \<open>Raising the cardinal of an \<open>\<Omega>\<close> upper bound preserves \<open><\<^sub>o\<close> below it.
  A clean structural induction on the smaller term (no transitivity needed).\<close>

lemma olt_Om_mono: "a <\<^sub>o Om p \<Longrightarrow> p \<le> q \<Longrightarrow> a <\<^sub>o Om q"
proof (induction "size a" arbitrary: a rule: less_induct)
  case less
  have IH: "a' <\<^sub>o Om q" if "size a' < size a" "a' <\<^sub>o Om p" for a'
    using less.hyps that less.prems(2) by blast
  show ?case
  proof (cases a)
    case (Om r) thus ?thesis using less.prems by simp
  next
    case (Th r e)
    have "\<forall>\<gamma>\<in>Kn r e. \<gamma> <\<^sub>o Om q"
    proof
      fix \<gamma> assume g: "\<gamma> \<in> Kn r e"
      have "size \<gamma> < size a" using Th Kn_size[OF g] by simp
      moreover have "\<gamma> <\<^sub>o Om p" using less.prems(1) Th g by simp
      ultimately show "\<gamma> <\<^sub>o Om q" by (rule IH)
    qed
    thus ?thesis using Th by simp
  next
    case (Su xs)
    have "\<forall>v\<in>set xs. v <\<^sub>o Om q"
    proof
      fix v assume v: "v \<in> set xs"
      have "size v < size a" using Su size_lt_Su[OF v] by simp
      moreover have "v <\<^sub>o Om p" using less.prems(1) Su v by simp
      ultimately show "v <\<^sub>o Om q" by (rule IH)
    qed
    thus ?thesis using Su by simp
  qed
qed

subsection \<open>Transitivity of the ordering (order meta-theory, Towsner Lemma 2.1)\<close>

text \<open>\<^bold>\<open>Transitivity (sorry):\<close> the Key-Lemma-level order meta-theory.  A genuine
  case analysis on the nine shape combinations with a size induction; the
  principal/principal case is intricate (the critical-subterm conditions chain
  through the middle term).  Declared here so the asymmetry proof and the
  well-foundedness core can use it; to be discharged together with the other
  order meta-theory.\<close>

text \<open>\<^bold>\<open>Bridge to the library multiset order (easy direction).\<close>  The single-dominator
  \<open>Su\<close>-clause implies the Dershowitz\<dash>Manna multiset order @{const multp\<^sub>D\<^sub>M}: the
  single witness \<open>b\<close> dominates every removed element, so it witnesses the (weaker)
  per-element domination.  (The converse needs linearity of the components and is
  obtained mod the incomparability equivalence.)\<close>

lemma olt_Su_imp_multp\<^sub>D\<^sub>M:
  assumes "Su xs <\<^sub>o Su ys"
  shows "multp\<^sub>D\<^sub>M (<\<^sub>o) (mset xs) (mset ys)"
proof -
  from assms obtain b where b: "b \<in># mset ys - mset xs"
    and dom: "\<forall>a \<in># mset xs - mset ys. a <\<^sub>o b" by auto
  let ?X = "mset ys - mset xs" and ?Y = "mset xs - mset ys"
  have x1: "?X \<noteq> {#}" using b by auto
  have x2: "?X \<subseteq># mset ys" by simp
  have x3: "mset xs = (mset ys - ?X) + ?Y"
  proof (rule multiset_eqI)
    fix a
    have "count ((mset ys - ?X) + ?Y) a
          = (count (mset ys) a - (count (mset ys) a - count (mset xs) a))
            + (count (mset xs) a - count (mset ys) a)"
      by (simp add: count_diff count_union)
    also have "\<dots> = count (mset xs) a" by linarith
    finally show "count (mset xs) a = count ((mset ys - ?X) + ?Y) a" by simp
  qed
  have x4: "\<forall>k. k \<in># ?Y \<longrightarrow> (\<exists>a. a \<in># ?X \<and> k <\<^sub>o a)" using b dom by blast
  show ?thesis unfolding multp\<^sub>D\<^sub>M_def using x1 x2 x3 x4 by blast
qed

text \<open>Forward bridge: the \<open>Su\<close>-clause implies the library multiset order @{const multp}
  (via @{thm [source] multp\<^sub>D\<^sub>M_imp_multp}).  Unconditional.  The reverse holds on the
  totally-ordered (mod incomparability) component carrier and recovers the single
  dominator by the maximum-element argument; together they give \<open>Su\<close>-transitivity by
  inheritance from @{thm [source] transp_on_multp\<^sub>H\<^sub>O}.\<close>

lemma olt_Su_imp_multp:
  "Su xs <\<^sub>o Su ys \<Longrightarrow> multp (<\<^sub>o) (mset xs) (mset ys)"
  using olt_Su_imp_multp\<^sub>D\<^sub>M multp\<^sub>D\<^sub>M_imp_multp by blast

lemma olt_trans: "a <\<^sub>o b \<Longrightarrow> b <\<^sub>o c \<Longrightarrow> a <\<^sub>o c"
proof (induction "size a + size b + size c" arbitrary: a b c rule: less_induct)
  case less
  have ab: "a <\<^sub>o b" and bc: "b <\<^sub>o c" using less.prems by auto
  have IH: "x <\<^sub>o z" if "size x + size y + size z < size a + size b + size c"
                          "x <\<^sub>o y" "y <\<^sub>o z" for x y z
    using less.hyps that by blast
  show "a <\<^sub>o c"
  proof (cases c)
    case c_Om: (Om n)
    show ?thesis
    proof (cases a)
      case a_Om: (Om q)
      \<comment> \<open>conclusion \<open>Om q <\<^sub>o Om n\<close>, i.e. \<open>q < n\<close>\<close>
      show ?thesis
      proof (cases b)
        case (Om p)
        thus ?thesis using ab bc a_Om c_Om by simp
      next
        case (Th p f)
        from ab a_Om Th obtain g where g: "g \<in> Kn p f" "Om q \<le>\<^sub>o g" by auto
        have gn: "g <\<^sub>o Om n" using bc Th c_Om g(1) by simp
        show ?thesis
        proof (cases "Om q = g")
          case True thus ?thesis using gn a_Om c_Om by simp
        next
          case False
          have "size (Om q) + size g + size (Om n) < size a + size b + size c"
            using a_Om Th c_Om Kn_size[OF g(1)] by simp
          moreover have "Om q <\<^sub>o g" using g(2) False by simp
          ultimately have "Om q <\<^sub>o Om n" using gn IH by blast
          thus ?thesis using a_Om c_Om by simp
        qed
      next
        case (Su bs)
        from ab a_Om Su obtain z where z: "z \<in> set bs" "Om q \<le>\<^sub>o z" by auto
        have zn: "z <\<^sub>o Om n" using bc Su c_Om z(1) by simp
        show ?thesis
        proof (cases "Om q = z")
          case True thus ?thesis using zn a_Om c_Om by simp
        next
          case False
          have "size (Om q) + size z + size (Om n) < size a + size b + size c"
            using a_Om Su c_Om size_lt_Su[OF z(1)] by simp
          moreover have "Om q <\<^sub>o z" using z(2) False by simp
          ultimately have "Om q <\<^sub>o Om n" using zn IH by blast
          thus ?thesis using a_Om c_Om by simp
        qed
      qed
    next
      case a_Th: (Th q e)
      \<comment> \<open>goal is exactly \<open>Th q e <\<^sub>o Om n\<close> = \<open>\<forall>\<gamma>\<in>Kn q e. \<gamma> <\<^sub>o Om n\<close>\<close>
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
          have dn: "\<delta> <\<^sub>o Om n" using bc Th c_Om d(1) by simp
          show ?thesis
          proof (cases "Th q e = \<delta>")
            case True thus ?thesis using dn by simp
          next
            case False
            have sz: "size (Th q e) + size \<delta> + size (Om n) < size a + size b + size c"
              using a_Th Th c_Om Kn_size[OF d(1)] by simp
            have "Th q e <\<^sub>o \<delta>" using d(2) False by simp
            thus ?thesis using sz dn IH by blast
          qed
        next
          case lower
          have "\<forall>\<gamma>\<in>Kn q e. \<gamma> <\<^sub>o Om n"
          proof
            fix \<gamma> assume g: "\<gamma> \<in> Kn q e"
            have "size \<gamma> + size (Th p f) + size (Om n) < size a + size b + size c"
              using a_Th Th c_Om Kn_size[OF g] by simp
            moreover have "\<gamma> <\<^sub>o Th p f" using lower g by simp
            moreover have "Th p f <\<^sub>o Om n" using bc Th c_Om by simp
            ultimately show "\<gamma> <\<^sub>o Om n" using IH by blast
          qed
          thus ?thesis using a_Th by simp
        qed
      next
        case (Su bs)
        from ab a_Th Su obtain z where z: "z \<in> set bs" "Th q e \<le>\<^sub>o z" by auto
        have zn: "z <\<^sub>o Om n" using bc Su c_Om z(1) by simp
        show ?thesis
        proof (cases "Th q e = z")
          case True thus ?thesis using zn by simp
        next
          case False
          have sz: "size (Th q e) + size z + size (Om n) < size a + size b + size c"
            using a_Th Su c_Om size_lt_Su[OF z(1)] by simp
          have "Th q e <\<^sub>o z" using z(2) False by simp
          thus ?thesis using sz zn IH by blast
        qed
      qed
      thus ?thesis using a_Th c_Om by simp
    next
      case a_Su: (Su as)
      have "\<forall>v\<in>set as. v <\<^sub>o Om n"
      proof
        fix v assume v: "v \<in> set as"
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
          ultimately show ?thesis using IH by blast
        next
          case (Su bs)
          show ?thesis
          proof (cases "v \<in># mset as - mset bs")
            case True
            from ab a_Su Su obtain w where w: "w \<in># mset bs - mset as"
              and wdom: "\<forall>u \<in># mset as - mset bs. u <\<^sub>o w" by auto
            have vw: "v <\<^sub>o w" using wdom True by simp
            have "w \<in> set bs" using w by (meson in_diffD in_multiset_in_set)
            hence wn: "w <\<^sub>o Om n" using bc Su c_Om by simp
            have "size v + size w + size (Om n) < size a + size b + size c"
              using a_Su Su c_Om szv size_lt_Su[OF \<open>w \<in> set bs\<close>] by simp
            thus ?thesis using vw wn IH by blast
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
      \<comment> \<open>principal \<open>a\<close>: find \<open>z \<in> zs\<close> with \<open>a \<le>\<^sub>o z\<close>\<close>
      have "\<exists>z\<in>set zs. a \<le>\<^sub>o z"
      proof (cases "isH b")
        case bH: True
        \<comment> \<open>\<open>b\<close> principal: \<open>b \<le>\<^sub>o z\<close> for some \<open>z\<in>zs\<close>; then \<open>a <\<^sub>o z\<close>\<close>
        from bc c_Su bH obtain z where z: "z \<in> set zs" "b \<le>\<^sub>o z"
          by (cases b) auto
        have "a <\<^sub>o z"
        proof (cases "b = z")
          case True thus ?thesis using ab by simp
        next
          case False
          have "size a + size b + size z < size a + size b + size c"
            using c_Su size_lt_Su[OF z(1)] by simp
          moreover have "b <\<^sub>o z" using z(2) False by simp
          ultimately show ?thesis using ab IH by blast
        qed
        thus ?thesis using z(1) by auto
      next
        case bSu: False
        then obtain bs where bbs: "b = Su bs" by (cases b) auto
        from ab True bbs obtain y where y: "y \<in> set bs" "a \<le>\<^sub>o y"
          by (cases a) auto
        \<comment> \<open>\<open>y\<close> is a summand of \<open>b\<close>; locate a \<open>z\<in>zs\<close> dominating it\<close>
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
            ultimately have "a <\<^sub>o z" using yzlt IH by blast
            thus ?thesis by simp
          qed
        qed
        thus ?thesis using z(1) by auto
      qed
      thus ?thesis using True c_Su by (cases a) auto
    next
      case False
      \<comment> \<open>\<open>a = Su as\<close>: multiset transitivity\<close>
      show ?thesis sorry
    qed
  next
    case c_Th: (Th n d)
    show ?thesis
    proof (cases a)
      case a_Om: (Om q)
      \<comment> \<open>goal \<open>Om q <\<^sub>o Th n d\<close> = \<open>\<exists>\<gamma>\<in>Kn n d. Om q \<le>\<^sub>o \<gamma>\<close>\<close>
      have "\<exists>\<gamma>\<in>Kn n d. Om q \<le>\<^sub>o \<gamma>"
      proof (cases b)
        case (Om p)
        from bc Om c_Th obtain g where g: "g \<in> Kn n d" "Om p \<le>\<^sub>o g" by auto
        have "Om q <\<^sub>o Om p" using ab a_Om Om by simp
        have "Om q <\<^sub>o g"
        proof (cases "Om p = g")
          case True thus ?thesis using \<open>Om q <\<^sub>o Om p\<close> by simp
        next
          case False
          have "size (Om q) + size (Om p) + size g < size a + size b + size c"
            using a_Om Om c_Th Kn_size[OF g(1)] by simp
          moreover have "Om p <\<^sub>o g" using g(2) False by simp
          ultimately show ?thesis using \<open>Om q <\<^sub>o Om p\<close> IH by blast
        qed
        thus ?thesis using g(1) by auto
      next
        case (Th p f)
        from ab a_Om Th obtain dlt where dl: "dlt \<in> Kn p f" "Om q \<le>\<^sub>o dlt" by auto
        from bc[unfolded Th c_Th]
        consider (fst) "\<exists>g\<in>Kn n d. Th p f \<le>\<^sub>o g"
          | (snd) "\<forall>\<delta>\<in>Kn p f. \<delta> <\<^sub>o Th n d" by auto
        thus ?thesis
        proof cases
          case fst
          then obtain g where g: "g \<in> Kn n d" "Th p f \<le>\<^sub>o g" by auto
          have "Om q <\<^sub>o g"
          proof (cases "Th p f = g")
            case True
            have "size (Om q) + size (Th p f) + size g < size a + size b + size c"
              using a_Om Th c_Th Kn_size[OF g(1)] by simp
            moreover have "Om q <\<^sub>o Th p f" using ab a_Om Th by simp
            ultimately show ?thesis using True by simp
          next
            case False
            have "size (Om q) + size (Th p f) + size g < size a + size b + size c"
              using a_Om Th c_Th Kn_size[OF g(1)] by simp
            moreover have "Om q <\<^sub>o Th p f" using ab a_Om Th by simp
            moreover have "Th p f <\<^sub>o g" using g(2) False by simp
            ultimately show ?thesis using IH by blast
          qed
          thus ?thesis using g(1) by auto
        next
          case snd
          have dn: "dlt <\<^sub>o Th n d" using snd dl(1) by simp
          have "Om q <\<^sub>o Th n d"
          proof (cases "Om q = dlt")
            case True thus ?thesis using dn by simp
          next
            case False
            have "size (Om q) + size dlt + size (Th n d) < size a + size b + size c"
              using a_Om Th c_Th Kn_size[OF dl(1)] by simp
            moreover have "Om q <\<^sub>o dlt" using dl(2) False by simp
            ultimately show ?thesis using dn IH by blast
          qed
          thus ?thesis using a_Om c_Th by simp
        qed
      next
        case (Su bs)
        from ab a_Om Su obtain y where y: "y \<in> set bs" "Om q \<le>\<^sub>o y" by auto
        have yn: "y <\<^sub>o Th n d" using bc Su c_Th y(1) by simp
        have "Om q <\<^sub>o Th n d"
        proof (cases "Om q = y")
          case True thus ?thesis using yn by simp
        next
          case False
          have "size (Om q) + size y + size (Th n d) < size a + size b + size c"
            using a_Om Su c_Th size_lt_Su[OF y(1)] by simp
          moreover have "Om q <\<^sub>o y" using y(2) False by simp
          ultimately show ?thesis using yn IH by blast
        qed
        thus ?thesis using a_Om c_Th by simp
      qed
      thus ?thesis using a_Om c_Th by simp
    next
      case a_Th: (Th q e)
      \<comment> \<open>the \<open>\<vartheta>/\<vartheta>/\<vartheta>\<close> transitivity core; uses @{thm [source] olt_Th_of_le_Kn} for
        domination and the IH on \<open>(e,f,d)\<close> for the subscript argument\<close>
      have isHa: "isH (Th q e)" by simp
      have "Th q e <\<^sub>o Th n d"
      proof (cases b)
        case (Om p)
        from bc Om c_Th obtain g where g: "g \<in> Kn n d" "Om p \<le>\<^sub>o g" by auto
        have "Th q e <\<^sub>o g"
        proof (cases "Om p = g")
          case True thus ?thesis using ab a_Th Om by simp
        next
          case False
          have "size (Th q e) + size (Om p) + size g < size a + size b + size c"
            using a_Th Om c_Th Kn_size[OF g(1)] by simp
          moreover have "Th q e <\<^sub>o Om p" using ab a_Th Om by simp
          moreover have "Om p <\<^sub>o g" using g(2) False by simp
          ultimately show ?thesis using IH by blast
        qed
        thus ?thesis using olt_Th_of_le_Kn[OF isHa g(1)] by simp
      next
        case (Su bs)
        from ab a_Th Su obtain y where y: "y \<in> set bs" "Th q e \<le>\<^sub>o y" by auto
        have yn: "y <\<^sub>o Th n d" using bc Su c_Th y(1) by simp
        show ?thesis
        proof (cases "Th q e = y")
          case True thus ?thesis using yn by simp
        next
          case False
          have "size (Th q e) + size y + size (Th n d) < size a + size b + size c"
            using a_Th Su c_Th size_lt_Su[OF y(1)] by simp
          moreover have "Th q e <\<^sub>o y" using y(2) False by simp
          ultimately show ?thesis using yn IH by blast
        qed
      next
        case (Th p f)
        from bc[unfolded Th c_Th]
        consider (bfst) "\<exists>g\<in>Kn n d. Th p f \<le>\<^sub>o g"
          | (bsnd) "(\<forall>\<delta>\<in>Kn p f. \<delta> <\<^sub>o Th n d) \<and> (p < n \<or> (p = n \<and> f <\<^sub>o d))" by auto
        thus ?thesis
        proof cases
          case bfst
          then obtain g where g: "g \<in> Kn n d" "Th p f \<le>\<^sub>o g" by auto
          have "Th q e <\<^sub>o g"
          proof (cases "Th p f = g")
            case True
            have "size (Th q e) + size (Th p f) + size g < size a + size b + size c"
              using a_Th Th c_Th Kn_size[OF g(1)] by simp
            moreover have "Th q e <\<^sub>o Th p f" using ab a_Th Th by simp
            ultimately show ?thesis using True by simp
          next
            case False
            have "size (Th q e) + size (Th p f) + size g < size a + size b + size c"
              using a_Th Th c_Th Kn_size[OF g(1)] by simp
            moreover have "Th q e <\<^sub>o Th p f" using ab a_Th Th by simp
            moreover have "Th p f <\<^sub>o g" using g(2) False by simp
            ultimately show ?thesis using IH by blast
          qed
          thus ?thesis using olt_Th_of_le_Kn[OF isHa g(1)] by simp
        next
          case bsnd
          hence ball_pf: "\<forall>\<delta>\<in>Kn p f. \<delta> <\<^sub>o Th n d" and sub_pn: "p < n \<or> (p = n \<and> f <\<^sub>o d)"
            by auto
          from ab[unfolded a_Th Th]
          consider (afst) "\<exists>\<delta>\<in>Kn p f. Th q e \<le>\<^sub>o \<delta>"
            | (asnd) "(\<forall>\<gamma>\<in>Kn q e. \<gamma> <\<^sub>o Th p f) \<and> (q < p \<or> (q = p \<and> e <\<^sub>o f))" by auto
          thus ?thesis
          proof cases
            case afst
            then obtain dd where dd: "dd \<in> Kn p f" "Th q e \<le>\<^sub>o dd" by auto
            have dn: "dd <\<^sub>o Th n d" using ball_pf dd(1) by simp
            show ?thesis
            proof (cases "Th q e = dd")
              case True thus ?thesis using dn by simp
            next
              case False
              have "size (Th q e) + size dd + size (Th n d) < size a + size b + size c"
                using a_Th Th c_Th Kn_size[OF dd(1)] by simp
              moreover have "Th q e <\<^sub>o dd" using dd(2) False by simp
              ultimately show ?thesis using dn IH by blast
            qed
          next
            case asnd
            hence ball_qe: "\<forall>\<gamma>\<in>Kn q e. \<gamma> <\<^sub>o Th p f"
              and sub_qp: "q < p \<or> (q = p \<and> e <\<^sub>o f)" by auto
            have c1: "\<forall>\<gamma>\<in>Kn q e. \<gamma> <\<^sub>o Th n d"
            proof
              fix \<gamma> assume gqe: "\<gamma> \<in> Kn q e"
              have "size \<gamma> + size (Th p f) + size (Th n d) < size a + size b + size c"
                using a_Th Th c_Th Kn_size[OF gqe] by simp
              moreover have "\<gamma> <\<^sub>o Th p f" using ball_qe gqe by simp
              moreover have "Th p f <\<^sub>o Th n d" using bc Th c_Th by simp
              ultimately show "\<gamma> <\<^sub>o Th n d" using IH by blast
            qed
            have c2: "q < n \<or> (q = n \<and> e <\<^sub>o d)"
            proof (cases "q < p")
              case True thus ?thesis using sub_pn by auto
            next
              case False
              hence qp: "q = p" "e <\<^sub>o f" using sub_qp by auto
              show ?thesis
              proof (cases "p < n")
                case True thus ?thesis using qp by simp
              next
                case False
                hence pn: "p = n" "f <\<^sub>o d" using sub_pn by auto
                have "size e + size f + size d < size a + size b + size c"
                  using a_Th Th c_Th by simp
                hence "e <\<^sub>o d" using qp(2) pn(2) IH by blast
                thus ?thesis using qp(1) pn(1) by simp
              qed
            qed
            show ?thesis using c1 c2 by simp
          qed
        qed
      qed
      thus ?thesis using a_Th c_Th by simp
    next
      case a_Su: (Su as)
      have "\<forall>v\<in>set as. v <\<^sub>o Th n d"
      proof
        fix v assume v: "v \<in> set as"
        have szv: "size v < size a" using a_Su size_lt_Su[OF v] by simp
        show "v <\<^sub>o Th n d"
        proof (cases b)
          case (Om p)
          have "v <\<^sub>o Om p" using ab a_Su Om v by simp
          moreover have "Om p <\<^sub>o Th n d" using bc Om c_Th by simp
          moreover have "size v + size (Om p) + size (Th n d) < size a + size b + size c"
            using Om c_Th szv by simp
          ultimately show ?thesis using IH by blast
        next
          case (Th p f)
          have "v <\<^sub>o Th p f" using ab a_Su Th v by simp
          moreover have "Th p f <\<^sub>o Th n d" using bc Th c_Th by simp
          moreover have "size v + size (Th p f) + size (Th n d) < size a + size b + size c"
            using Th c_Th szv by simp
          ultimately show ?thesis using IH by blast
        next
          case (Su bs)
          show ?thesis
          proof (cases "v \<in># mset as - mset bs")
            case True
            from ab a_Su Su obtain w where w: "w \<in># mset bs - mset as"
              and wdom: "\<forall>u \<in># mset as - mset bs. u <\<^sub>o w" by auto
            have vw: "v <\<^sub>o w" using wdom True by simp
            have wbs: "w \<in> set bs" using w by (meson in_diffD in_multiset_in_set)
            have wn: "w <\<^sub>o Th n d" using bc Su c_Th wbs by simp
            have "size v + size w + size (Th n d) < size a + size b + size c"
              using a_Su Su c_Th szv size_lt_Su[OF wbs] by simp
            thus ?thesis using vw wn IH by blast
          next
            case False
            have "count (mset bs) v = 0 \<Longrightarrow> False"
            proof -
              assume "count (mset bs) v = 0"
              moreover have "0 < count (mset as) v"
                using v by (simp add: count_greater_zero_iff in_multiset_in_set)
              ultimately have "count (mset bs) v < count (mset as) v" by linarith
              hence "v \<in># mset as - mset bs" by (simp add: in_diff_count)
              thus False using False by simp
            qed
            hence "0 < count (mset bs) v" by auto
            hence "v \<in> set bs" by (simp add: count_greater_zero_iff in_multiset_in_set)
            thus ?thesis using bc Su c_Th by simp
          qed
        qed
      qed
      thus ?thesis using a_Su c_Th by simp
    qed
  qed
qed

lemma olt_ole_trans: "a <\<^sub>o b \<Longrightarrow> b \<le>\<^sub>o c \<Longrightarrow> a <\<^sub>o c"
  using olt_trans by blast

lemma ole_olt_trans: "a \<le>\<^sub>o b \<Longrightarrow> b <\<^sub>o c \<Longrightarrow> a <\<^sub>o c"
  using olt_trans by blast

subsection \<open>Asymmetry of the ordering (hence irreflexivity)\<close>

text \<open>\<open><\<^sub>o\<close> has no 2-cycles.  Proof by induction on \<open>size x + size y\<close>: from
  \<open>x <\<^sub>o y\<close> and \<open>y <\<^sub>o x\<close> one always extracts a \<^emph>\<open>strictly smaller\<close> 2-cycle
  (between a witness of one side and a witness of the other), contradicting the
  inductive hypothesis.\<close>

lemma olt_asym: "\<not> (x <\<^sub>o y \<and> y <\<^sub>o x)"
proof (induction "size x + size y" arbitrary: x y rule: less_induct)
  case less
  have key: "\<not> (u <\<^sub>o v \<and> v <\<^sub>o u)" if "size u + size v < size x + size y" for u v
    using less.hyps that by blast
  show ?case
  proof (rule notI)
    assume "x <\<^sub>o y \<and> y <\<^sub>o x"
    hence xy: "x <\<^sub>o y" and yx: "y <\<^sub>o x" by auto
    show False
    proof (cases x)
      case x_Su: (Su xs)
      show False
      proof (cases y)
        case y_Su: (Su ys)
        from xy x_Su y_Su obtain b where b: "b \<in># mset ys - mset xs"
          and bdom: "\<forall>a \<in># mset xs - mset ys. a <\<^sub>o b" by auto
        from yx x_Su y_Su obtain b' where b': "b' \<in># mset xs - mset ys"
          and b'dom: "\<forall>a \<in># mset ys - mset xs. a <\<^sub>o b'" by auto
        have "b' <\<^sub>o b" using bdom b' by simp
        moreover have "b <\<^sub>o b'" using b'dom b by simp
        moreover have "size b + size b' < size x + size y"
        proof -
          have "b \<in> set ys" using b by (meson in_diffD in_multiset_in_set)
          hence "size b < size y" using y_Su size_lt_Su by simp
          moreover have "b' \<in> set xs" using b' by (meson in_diffD in_multiset_in_set)
          hence "size b' < size x" using x_Su size_lt_Su by simp
          ultimately show ?thesis by linarith
        qed
        ultimately show False using key by blast
      next
        case y_Om: (Om n)
        from yx x_Su y_Om obtain b where b: "b \<in> set xs" "Om n \<le>\<^sub>o b" by auto
        have "b <\<^sub>o Om n" using xy x_Su y_Om b(1) by simp
        moreover have "size b + size (Om n) < size x + size y"
          using x_Su y_Om b(1) size_lt_Su by fastforce
        ultimately show False using b(2) key by force
      next
        case y_Th: (Th n d)
        from yx x_Su y_Th obtain b where b: "b \<in> set xs" "Th n d \<le>\<^sub>o b" by auto
        have "b <\<^sub>o Th n d" using xy x_Su y_Th b(1) by simp
        moreover have "size b + size (Th n d) < size x + size y"
          using x_Su y_Th b(1) size_lt_Su by fastforce
        ultimately show False using b(2) key by force
      qed
    next
      case x_Om: (Om m)
      show False
      proof (cases y)
        case y_Su: (Su ys)
        from xy x_Om y_Su obtain b where b: "b \<in> set ys" "Om m \<le>\<^sub>o b" by auto
        have "b <\<^sub>o Om m" using yx x_Om y_Su b(1) by simp
        moreover have "size b + size (Om m) < size x + size y"
          using x_Om y_Su b(1) size_lt_Su by fastforce
        ultimately show False using b(2) key by force
      next
        case y_Om: (Om n) thus False using xy yx x_Om by simp
      next
        case y_Th: (Th n d)
        from xy x_Om y_Th obtain g where g: "g \<in> Kn n d" "Om m \<le>\<^sub>o g" by auto
        have "g <\<^sub>o Om m" using yx x_Om y_Th g(1) by simp
        moreover have "size (Om m) + size g < size x + size y"
          using x_Om y_Th Kn_size[OF g(1)] by simp
        ultimately show False using g(2) key by force
      qed
    next
      case x_Th: (Th m c)
      show False
      proof (cases y)
        case y_Su: (Su ys)
        from xy x_Th y_Su obtain b where b: "b \<in> set ys" "Th m c \<le>\<^sub>o b" by auto
        have "b <\<^sub>o Th m c" using yx x_Th y_Su b(1) by simp
        moreover have "size b + size (Th m c) < size x + size y"
          using x_Th y_Su b(1) size_lt_Su by fastforce
        ultimately show False using b(2) key by force
      next
        case y_Om: (Om n)
        from yx x_Th y_Om obtain g where g: "g \<in> Kn m c" "Om n \<le>\<^sub>o g" by auto
        have "g <\<^sub>o Om n" using xy x_Th y_Om g(1) by simp
        moreover have "size (Om n) + size g < size x + size y"
          using x_Th y_Om Kn_size[OF g(1)] by simp
        ultimately show False using g(2) key by force
      next
        case y_Th: (Th n d)
        have XX: "(\<exists>\<gamma>\<in>Kn n d. Th m c \<le>\<^sub>o \<gamma>)
                  \<or> ((\<forall>\<gamma>\<in>Kn m c. \<gamma> <\<^sub>o Th n d) \<and> (m < n \<or> (m = n \<and> c <\<^sub>o d)))"
          using xy x_Th y_Th by simp
        have YY: "(\<exists>\<gamma>\<in>Kn m c. Th n d \<le>\<^sub>o \<gamma>)
                  \<or> ((\<forall>\<gamma>\<in>Kn n d. \<gamma> <\<^sub>o Th m c) \<and> (n < m \<or> (n = m \<and> d <\<^sub>o c)))"
          using yx x_Th y_Th by simp
        from XX show False
        proof
          assume XA: "\<exists>\<gamma>\<in>Kn n d. Th m c \<le>\<^sub>o \<gamma>"
          then obtain g where g: "g \<in> Kn n d" "Th m c \<le>\<^sub>o g" by auto
          have szg: "size g < size y" using x_Th y_Th Kn_size[OF g(1)] by simp
          from YY show False
          proof
            assume YA: "\<exists>\<gamma>\<in>Kn m c. Th n d \<le>\<^sub>o \<gamma>"
            then obtain g' where g': "g' \<in> Kn m c" "Th n d \<le>\<^sub>o g'" by auto
            \<comment> \<open>both dominated by each other's critical subterms \<dash> chain via transitivity\<close>
            have "g <\<^sub>o Th n d" by (rule Kn_lt_Th[OF g(1)])
            hence "g <\<^sub>o g'" using g'(2) by (rule olt_ole_trans)
            moreover have "g' <\<^sub>o Th m c" by (rule Kn_lt_Th[OF g'(1)])
            hence "g' <\<^sub>o g" using g(2) by (rule olt_ole_trans)
            moreover have "size g + size g' < size x + size y"
              using x_Th y_Th Kn_size[OF g(1)] Kn_size[OF g'(1)] by simp
            ultimately show False using key by blast
          next
            assume YB: "(\<forall>\<gamma>\<in>Kn n d. \<gamma> <\<^sub>o Th m c) \<and> (n < m \<or> (n = m \<and> d <\<^sub>o c))"
            have "g <\<^sub>o Th m c" using YB g(1) by simp
            moreover have "size (Th m c) + size g < size x + size y"
              using x_Th szg by simp
            ultimately show False using g(2) key by force
          qed
        next
          assume XB: "(\<forall>\<gamma>\<in>Kn m c. \<gamma> <\<^sub>o Th n d) \<and> (m < n \<or> (m = n \<and> c <\<^sub>o d))"
          from YY show False
          proof
            assume YA: "\<exists>\<gamma>\<in>Kn m c. Th n d \<le>\<^sub>o \<gamma>"
            then obtain g where g: "g \<in> Kn m c" "Th n d \<le>\<^sub>o g" by auto
            have "g <\<^sub>o Th n d" using XB g(1) by simp
            moreover have "size (Th n d) + size g < size x + size y"
              using x_Th y_Th Kn_size[OF g(1)] by simp
            ultimately show False using g(2) key by force
          next
            assume YB: "(\<forall>\<gamma>\<in>Kn n d. \<gamma> <\<^sub>o Th m c) \<and> (n < m \<or> (n = m \<and> d <\<^sub>o c))"
            have "m = n \<and> c <\<^sub>o d \<and> d <\<^sub>o c"
              using XB YB by force
            moreover have "size c + size d < size x + size y"
              using x_Th y_Th by simp
            ultimately show False using key by blast
          qed
        qed
      qed
    qed
  qed
qed

lemma olt_irrefl: "\<not> (x <\<^sub>o x)"
  using olt_asym by blast

subsection \<open>Shifting the cardinal levels (Towsner Def 3.3, global form)\<close>

text \<open>\<open>shift k a\<close> adds \<open>k\<close> to every cardinal level (both \<^const>\<open>Om\<close> indices and
  \<^const>\<open>Th\<close> subscripts).  Because \<open><\<^sub>o\<close> compares levels only \<^emph>\<open>relatively\<close>,
  \<open>shift k\<close> is an order automorphism (lemma \<open>shift_olt\<close> below); this is the engine
  of the ground-normalization in the well-foundedness proof.\<close>

fun shift :: "int \<Rightarrow> ot \<Rightarrow> ot" where
  "shift k (Om m) = Om (m + k)"
| "shift k (Th n a) = Th (n + k) (shift k a)"
| "shift k (Su xs) = Su (map (shift k) xs)"

lemma shift_shift [simp]: "shift k (shift l a) = shift (k + l) a"
  by (induction a) (auto simp: ac_simps)

lemma shift_0 [simp]: "shift 0 a = a"
  by (induction a) (auto simp: map_idI)

lemma shift_inv [simp]: "shift (- k) (shift k a) = a"
  by simp

lemma shift_inj: "inj (shift k)"
  by (rule injI) (metis shift_inv)

lemma shift_isH [simp]: "isH (shift k a) = isH a"
  by (cases a) auto

lemma shift_FCset: "FCset (shift k a) = (\<lambda>m. m + k) ` FCset a"
  by (induction a) (auto simp: image_Un)

lemma shift_Kn: "Kn (n + k) (shift k a) = shift k ` Kn n a"
  by (induction a) (auto simp: image_Un)

text \<open>The critical-subterm clause shifts uniformly, giving order-invariance.\<close>

lemma shift_eq [simp]: "(shift k a = shift k b) = (a = b)"
  using shift_inj by (auto dest: injD)

text \<open>Expanded-form equalities, so the principal-head equations close after
  \<open>shift.simps\<close> has unfolded the outermost \<^const>\<open>Th\<close>/\<^const>\<open>Om\<close>.\<close>

lemma shift_eqTh [simp]: "(Th (m + k) (shift k a) = shift k g) = (Th m a = g)"
  using shift_eq[of k "Th m a" g] by simp

lemma shift_eqOm [simp]: "(Om (m + k) = shift k g) = (Om m = g)"
  using shift_eq[of k "Om m" g] by simp

text \<open>\<open>shift k\<close> is an order automorphism: comparisons depend only on the relative
  cardinal positions, all moved uniformly by \<open>k\<close>.  (Validated in Python
  \<^file>\<open>../work/ot_order.py\<close>: 35280 cases, 0 mismatches.)\<close>

lemma shift_olt [simp]: "(shift k a <\<^sub>o shift k b) = (a <\<^sub>o b)"
proof (induction a b rule: olt.induct)
  case (1 xs ys)                 \<comment> \<open>Su / Su\<close>
  show ?case using 1
    by (auto simp: image_mset_diff_if_inj[OF shift_inj, symmetric] set_image_mset)
qed (auto simp: shift_Kn)

subsection \<open>Ground, normalization, and width (Towsner Def 3.6)\<close>

text \<open>The \<^emph>\<open>ground\<close> \<open>G(a)\<close> is the lowest cardinal level occurring free; the
  \<^emph>\<open>width\<close> is the spread of levels.  \<open>norm a\<close> normalizes by pushing the top level
  to \<open>0\<close> (via the order-automorphism \<^const>\<open>shift\<close>), so the width becomes \<open>- gnd\<close>.
  (For countable terms, \<open>FCset = {}\<close>; we keep these as a separate base case.)\<close>

definition gnd :: "ot \<Rightarrow> int" where
  "gnd a = (if FCset a = {} then 0 else Min (FCset a))"

definition wdt :: "ot \<Rightarrow> int" where
  "wdt a = FC a - gnd a"

definition norm :: "ot \<Rightarrow> ot" where
  "norm a = shift (- FC a) a"

lemma FC_shift: "FCset a \<noteq> {} \<Longrightarrow> FC (shift k a) = FC a + k"
proof -
  assume ne: "FCset a \<noteq> {}"
  have "FC (shift k a) = Max ((\<lambda>m. m + k) ` FCset a)"
    using ne by (simp add: FC_def shift_FCset)
  also have "\<dots> = Max (FCset a) + k"
    using ne by (subst mono_Max_commute) (auto simp: mono_def)
  finally show ?thesis using ne by (simp add: FC_def)
qed

lemma gnd_shift: "FCset a \<noteq> {} \<Longrightarrow> gnd (shift k a) = gnd a + k"
proof -
  assume ne: "FCset a \<noteq> {}"
  have "gnd (shift k a) = Min ((\<lambda>m. m + k) ` FCset a)"
    using ne by (simp add: gnd_def shift_FCset)
  also have "\<dots> = Min (FCset a) + k"
    using ne by (subst mono_Min_commute) (auto simp: mono_def)
  finally show ?thesis using ne by (simp add: gnd_def)
qed

lemma wdt_nonneg: "FCset a \<noteq> {} \<Longrightarrow> 0 \<le> wdt a"
  unfolding wdt_def FC_def gnd_def by simp

lemma wdt_shift [simp]: "wdt (shift k a) = wdt a"
proof (cases "FCset a = {}")
  case True thus ?thesis by (simp add: wdt_def FC_def gnd_def shift_FCset)
next
  case False thus ?thesis by (simp add: wdt_def FC_shift gnd_shift)
qed

lemma FC_norm: "FCset a \<noteq> {} \<Longrightarrow> FC (norm a) = 0"
  by (simp add: norm_def FC_shift)

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

lemma shift_wfo [simp]: "wfo (shift k a) = wfo a"
proof (induction a)
  case (Su xs)
  have "(\<forall>x\<in>set (map (shift k) xs). isH x \<and> wfo x) = (\<forall>x\<in>set xs. isH x \<and> wfo x)"
    using Su.IH by auto
  thus ?case by simp
qed auto

text \<open>\<^bold>\<open>Nonnegative subscripts.\<close>  A term is \<open>nneg\<close> when every \<open>\<vartheta>\<close>-subscript and every
  \<open>\<Omega>\<close>-index is \<open>\<ge> 0\<close>.  This is essential: \<^emph>\<open>negative\<close> subscripts are \<^bold>\<open>invalid\<close>
  notations and break well-foundedness \<dash> \<open>\<vartheta>\<^bsub>-k\<^esub> 0\<close> (\<open>k = 0,1,2,\<dots>\<close>) is an infinite
  \<^emph>\<open>descending\<close> \<open>\<Omega>\<close>-free \<open><\<^sub>o\<close>-chain (\<open>\<vartheta>\<^bsub>-(k+1)\<^esub> 0 <\<^sub>o \<vartheta>\<^bsub>-k\<^esub> 0\<close>, since \<open>K\<^bsub>-(k+1)\<^esub> 0 = {}\<close>
  makes the \<open>\<vartheta>\<close>/\<open>\<vartheta>\<close> subscript clause fire vacuously).  Buchholz/Towsner only admit
  indices \<open>\<ge> 0\<close> (resp.\ \<open>\<le> 0\<close> for the \<^emph>\<open>free\<close> \<open>\<Omega>\<close>); the embedding image is \<open>nneg\<close>
  (it uses \<open>\<vartheta>\<^bsub>int a\<^esub>\<close> with \<open>a : nat\<close>).  The well-foundedness target must therefore be
  restricted to the \<open>nneg\<close> fragment.\<close>

fun nneg :: "ot \<Rightarrow> bool" where
  "nneg (Om n) = (0 \<le> n)"
| "nneg (Th n a) = (0 \<le> n \<and> nneg a)"
| "nneg (Su xs) = (\<forall>x \<in> set xs. nneg x)"

lemma nneg_Kn: "nneg a \<Longrightarrow> \<gamma> \<in> Kn n a \<Longrightarrow> nneg \<gamma>"
  by (induction a arbitrary: \<gamma>) (auto split: if_splits)

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
