theory Euclid
  imports Main
begin

typedecl Point
typedecl Circle

consts
Congr :: "Point \<Rightarrow> Point \<Rightarrow> Point \<Rightarrow> Point \<Rightarrow> bool"
Bet :: "Point \<Rightarrow> Point \<Rightarrow> Point \<Rightarrow> bool"
PA :: Point
PB :: Point
PC :: Point
CI :: "Circle \<Rightarrow> Point \<Rightarrow> Point \<Rightarrow> Point \<Rightarrow> bool"

definition Col :: "Point \<Rightarrow> Point \<Rightarrow> Point \<Rightarrow> bool" where
"Col A B C \<equiv> (A = B \<or> A = C \<or> B = C \<or> Bet A B C \<or> Bet B C A \<or> Bet C A B)"

definition nCol :: "Point \<Rightarrow> Point \<Rightarrow> Point \<Rightarrow> bool" where
"nCol A B C \<equiv> (A \<noteq> B \<and> A \<noteq> C \<and> B \<noteq> C \<and> \<not> Bet A B C \<and> \<not> Bet B C A \<and> \<not> Bet C A B)" 

definition Triangle :: "Point \<Rightarrow> Point \<Rightarrow> Point \<Rightarrow> bool" where
"Triangle A B C \<equiv> nCol A B C"
