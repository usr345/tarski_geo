theory Out
  imports Col
begin

definition Out :: "Point \<Rightarrow> Point \<Rightarrow> Point \<Rightarrow> bool" where
"Out P A B \<equiv> P \<noteq> A \<and> P \<noteq> B \<and> (Bet P A B \<or> Bet P B A)"

lemma Bet_Out : "Bet A B C \<Longrightarrow> A \<noteq> B \<Longrightarrow> Out A B C"
proof -
  assume H1 : "Bet A B C"
  assume H2 : "A \<noteq> B"

  have L1 : "A \<noteq> C" using H1 H2 by (rule bet_id_neq1)
  have L2 : "Bet A B C \<or> Bet A C B" using H1 by (rule disjI1)
  have L3 : "A \<noteq> C \<and> (Bet A B C \<or> Bet A C B)  " using L1 L2 by (rule conjI)
  have L4 : "A \<noteq> B \<and> A \<noteq> C \<and> (Bet A B C \<or> Bet A C B)" using H2 L3 by (rule conjI)

  show "Out A B C" unfolding Out_def by (fact L4)
qed

