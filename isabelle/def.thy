theory def
  imports Main
begin

text \<open>
  PSS definitions, faithful to P進大好きbot's article
  "ペア数列の停止性" (pss-original-paper.html).  This file contains only the
  definitions needed for the termination proof via the p_a(b)+c notation:
  the §5 formulation (pair sequences, parent relations, fundamental sequence
  \<open>M[n]\<close>) and the §6.7 standard form \<open>ST_PS\<close>.  Variable names follow the
  article.  (The §6 reduction machinery \<open>Red\<close>, \<open>Br\<close>, \<dots> used by the Buchholz
  approach is deliberately omitted; it is not needed here.)
\<close>

section \<open>§4 記法 (Notation)\<close>

abbreviation Lng :: "'a list \<Rightarrow> nat" where
  "Lng xs \<equiv> length xs"


section \<open>§5 定式化 (Formulation)\<close>

type_synonym pairseq = "(nat \<times> nat) list"

definition T_PS :: "pairseq set" where
  "T_PS = {M. M \<noteq> []}"

text \<open>\<open>M\<^bsub>i,j\<^esub>\<close>: the \<open>i\<close>-th component (row) of the \<open>j\<close>-th pair.\<close>

definition entry :: "pairseq \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "entry M i j = (if i = 0 then fst (M ! j) else snd (M ! j))"


subsection \<open>§5.1 親子関係 (Parent-child relations)\<close>

definition nextrel0 :: "pairseq \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "nextrel0 M j0 j1 \<longleftrightarrow>
     j0 < Lng M \<and> j1 < Lng M \<and> j0 < j1 \<and>
     entry M 0 j0 < entry M 0 j1 \<and>
     (\<forall>j. j0 < j \<and> j < j1 \<longrightarrow> entry M 0 j \<ge> entry M 0 j1)"

definition le0 :: "pairseq \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "le0 M j0 j1 \<longleftrightarrow> j0 < Lng M \<and> j1 < Lng M \<and> (nextrel0 M)\<^sup>*\<^sup>* j0 j1"

definition nextrel1 :: "pairseq \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "nextrel1 M j0 j1 \<longleftrightarrow>
     j0 < Lng M \<and> j1 < Lng M \<and> j0 < j1 \<and>
     entry M 1 j0 < entry M 1 j1 \<and>
     le0 M j0 j1 \<and>
     (\<forall>j. j0 < j \<and> le0 M j j1 \<longrightarrow> entry M 1 j \<ge> entry M 1 j1)"

definition le1 :: "pairseq \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "le1 M j0 j1 \<longleftrightarrow> j0 < Lng M \<and> j1 < Lng M \<and> (nextrel1 M)\<^sup>*\<^sup>* j0 j1"

definition nextR :: "pairseq \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "nextR M i j0 j1 = (if i = 0 then nextrel0 M j0 j1 else nextrel1 M j0 j1)"

definition leR :: "pairseq \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "leR M i j0 j1 = (if i = 0 then le0 M j0 j1 else le1 M j0 j1)"


subsection \<open>§5.2 前者関数 (Predecessor functions)\<close>

definition Pred :: "pairseq \<Rightarrow> pairseq" where
  "Pred M = (if Lng M \<le> 1 then M else butlast M)"


subsection \<open>§5.3 基本列 (Fundamental sequence, \<open>M[n]\<close>)\<close>

definition idx1 :: "pairseq \<Rightarrow> nat \<Rightarrow> nat" where
  "idx1 M j1 = (if entry M 1 j1 > 0 then 1 else 0)"

definition hasParent :: "pairseq \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "hasParent M i j1 \<longleftrightarrow> (\<exists>!j0. nextR M i j0 j1)"

definition parent :: "pairseq \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "parent M i j1 = (THE j0. nextR M i j0 j1)"

definition oper :: "pairseq \<Rightarrow> nat \<Rightarrow> pairseq"  ("_[_]" [90,0] 91) where
  "M[n] =
     (let j1 = Lng M - 1 in
      if j1 = 0 then M
      else if entry M 0 j1 = 0 \<and> entry M 1 j1 = 0 then Pred M
      else let i1 = idx1 M j1 in
        if \<not> hasParent M i1 j1 then Pred M
        else let j0 = parent M i1 j1;
                 d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0);
                 d1 = (if 1 < i1 then entry M 1 j1 - entry M 1 j0 else 0)
             in take j0 M @
                concat (map (\<lambda>k. map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j + k * d1))
                                      [j0..<j1])
                            [0..<n]))"


subsection \<open>§6.5 / §6.7 standard form\<close>

text \<open>\<open>diagSeq a b\<close>: the diagonal segment \<open>((j,j))\<^bsub>j=a\<^esub>\<^bsup>b\<^esup>\<close> (length \<open>b - a + 1\<close>).\<close>

definition diagSeq :: "nat \<Rightarrow> nat \<Rightarrow> pairseq" where
  "diagSeq a b = map (\<lambda>j. (j, j)) [a..<Suc b]"

text \<open>\<open>ST\<^sub>PS\<close> (標準形): the least set of \<^emph>\<open>standard forms\<close>, i.e. pair sequences
  reachable from the initial diagonal \<open>(0,0)(1,1)\<dots>(v,v) = diagSeq 0 v\<close> by the
  expansion \<open>M \<mapsto> M[n]\<close> (\<open>n \<ge> 1\<close>).  The base diagonals start at \<open>(0,0)\<close> (the
  genuine initial state of a PSS computation); every standard form therefore
  begins with \<open>(0,0)\<close>.  (Using \<open>diagSeq u v\<close> with \<open>u > 0\<close> as a base would admit
  spurious sequences starting at \<open>(u,u)\<close> that are not reachable and break the
  normal-form invariants — CNF sums, subscript-monotone descent.)\<close>

inductive_set ST_PS :: "pairseq set" where
  diag: "diagSeq 0 v \<in> ST_PS"
| oper: "\<lbrakk>M \<in> ST_PS; 1 \<le> n\<rbrakk> \<Longrightarrow> (M::pairseq)[n] \<in> ST_PS"

text \<open>One expansion step of the system: \<open>M \<rightarrow> M[n]\<close> for some copy count \<open>n \<ge> 1\<close>,
  on sequences of length \<open>> 1\<close>.  Termination (independent of the activation
  function) means this relation has no infinite forward chain.\<close>

inductive step :: "pairseq \<Rightarrow> pairseq \<Rightarrow> bool" where
  step_oper: "\<lbrakk>1 < Lng M; 1 \<le> n\<rbrakk> \<Longrightarrow> step M (M[n])"

end
