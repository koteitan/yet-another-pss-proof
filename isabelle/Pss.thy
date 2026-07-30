theory Pss
  imports Main
begin

type_synonym pairseq = "(nat \<times> nat) list"

definition entry :: "pairseq \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "entry M i j =
    (let x = (if j < length M then M ! j else (0, 0))
     in if i = 0 then fst x else snd x)"

definition nextrel0 :: "pairseq \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "nextrel0 M j0 j1 \<longleftrightarrow>
    j0 < length M \<and> j1 < length M \<and> j0 < j1 \<and>
    entry M 0 j0 < entry M 0 j1 \<and>
    (\<forall>j. j0 < j \<and> j < j1 \<longrightarrow> entry M 0 j1 \<le> entry M 0 j)"

definition le0 :: "pairseq \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "le0 M j0 j1 \<longleftrightarrow>
    j0 < length M \<and> j1 < length M \<and> (nextrel0 M)\<^sup>*\<^sup>* j0 j1"

definition nextrel1 :: "pairseq \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "nextrel1 M j0 j1 \<longleftrightarrow>
    j0 < length M \<and> j1 < length M \<and> j0 < j1 \<and>
    entry M 1 j0 < entry M 1 j1 \<and>
    le0 M j0 j1 \<and>
    (\<forall>j. j0 < j \<and> le0 M j j1 \<longrightarrow> entry M 1 j1 \<le> entry M 1 j)"

definition nextR :: "pairseq \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "nextR M i j0 j1 = (if i = 0 then nextrel0 M j0 j1 else nextrel1 M j0 j1)"

definition Pred :: "pairseq \<Rightarrow> pairseq" where
  "Pred M = (if length M \<le> 1 then M else butlast M)"

definition idx1 :: "pairseq \<Rightarrow> nat \<Rightarrow> nat" where
  "idx1 M j1 = (if 0 < entry M 1 j1 then 1 else 0)"

definition hasParent :: "pairseq \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "hasParent M i j1 \<longleftrightarrow> (\<exists>!j0. nextR M i j0 j1)"

definition parent :: "pairseq \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "parent M i j1 = (SOME j0. nextR M i j0 j1)"

definition oper :: "pairseq \<Rightarrow> nat \<Rightarrow> pairseq" where
  "oper M n =
    (let j1 = length M - 1
     in if j1 = 0 then M
        else if entry M 0 j1 = 0 \<and> entry M 1 j1 = 0 then Pred M
        else
          (let i1 = idx1 M j1
           in if \<not> hasParent M i1 j1 then Pred M
              else
                (let j0 = parent M i1 j1;
                     d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0);
                     d1 = (if 1 < i1 then entry M 1 j1 - entry M 1 j0 else 0)
                 in take j0 M @
                    concat
                      (map
                        (\<lambda>k. map
                          (\<lambda>j. (entry M 0 j + k * d0,
                                  entry M 1 j + k * d1))
                          [j0..<j1])
                        [0..<n]))))"

notation oper ("_\<lbrakk>_\<rbrakk>" [90, 0] 91)

definition diagSeq :: "nat \<Rightarrow> nat \<Rightarrow> pairseq" where
  "diagSeq a b = map (\<lambda>j. (j, j)) [a..<Suc b]"

inductive ST_PS :: "pairseq \<Rightarrow> bool" where
  diag: "ST_PS (diagSeq 0 v)"
| oper: "\<lbrakk>ST_PS M; 1 \<le> n\<rbrakk> \<Longrightarrow> ST_PS (M\<lbrakk>n\<rbrakk>)"

inductive step :: "pairseq \<Rightarrow> pairseq \<Rightarrow> bool" where
  step_oper: "\<lbrakk>1 < length M; 1 \<le> n\<rbrakk> \<Longrightarrow> step M (M\<lbrakk>n\<rbrakk>)"

end
