theory wo
  imports Main
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
  \<^item> \<open>W a\<close>        \<open>= \<omega>\<^bsup>a\<^esup>\<close>
  \<^item> \<open>Su xs\<close>      \<open>= #{x\<^sub>0,\<dots>,x\<^bsub>k-1\<^esub>}\<close>  (commutative/natural sum; \<open>Su [] = 0\<close>)

  The \<^emph>\<open>principal\<close> (Buchholz: \<open>H\<close>) terms are \<open>Om\<close>, \<open>Th\<close>, \<open>W\<close>; \<open>Su\<close> is the sum.
\<close>

datatype ot =
    Om nat            \<comment> \<open>\<open>\<Omega>\<^sub>n\<close>\<close>
  | Th nat ot         \<comment> \<open>\<open>\<vartheta>\<^sub>n a\<close>\<close>
  | W ot              \<comment> \<open>\<open>\<omega>\<^bsup>a\<^esup>\<close>\<close>
  | Su "ot list"      \<comment> \<open>\<open>#{x\<^sub>0,\<dots>}\<close>, summands principal, length \<open>\<noteq> 1\<close>; \<open>Su [] = 0\<close>\<close>

abbreviation Zero :: ot where "Zero \<equiv> Su []"

text \<open>The principal (Buchholz \<open>H\<close>) terms.\<close>

fun isH :: "ot \<Rightarrow> bool" where
  "isH (Om _) = True"
| "isH (Th _ _) = True"
| "isH (W _) = True"
| "isH (Su _) = False"

subsection \<open>Formal cardinalities (Towsner Def 2.4)\<close>

text \<open>\<open>FCset a\<close> is the set of cardinal levels occurring free in \<open>a\<close>;
  \<open>FC\<^bsub>n\<^esub>(\<vartheta>\<^sub>n a) = FC(a) \<setminus> {m. m \<ge> n}\<close>.\<close>

fun FCset :: "ot \<Rightarrow> nat set" where
  "FCset (Om n) = {n}"
| "FCset (Th n a) = {m \<in> FCset a. m < n}"
| "FCset (W a) = FCset a"
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
| "Kn n (W a) = Kn n a"
| "Kn n (Su xs) = (\<Union>x \<in> set xs. Kn n x)"

lemma finite_Kn [simp]: "finite (Kn n a)"
  by (induction a) auto

end
