theory Col
  imports BetCongr
begin
definition Col :: "Point \<Rightarrow> Point \<Rightarrow> Point \<Rightarrow> bool" where
  "Col A B C \<equiv> Bet A B C \<or> Bet B C A \<or> Bet C A B"

lemma col_from_bet1:
  fixes A B C :: Point
  shows "Bet A B C \<Longrightarrow> Col A B C"
proof -
  assume ABC: "Bet A B C"

  have disj: "Bet A B C \<or> Bet B C A \<or> Bet C A B" by (rule disjI1 [OF ABC])
  show "Col A B C" unfolding Col_def by (fact disj)
qed

lemma col_from_bet2:
  fixes A B C :: Point
  shows "Bet B C A \<Longrightarrow> Col A B C"
proof -
  assume BCA: "Bet B C A"

  have disj1: "Bet B C A \<or> Bet C A B" by (rule disjI1 [OF BCA])
  have disj2: "Bet A B C \<or> (Bet B C A \<or> Bet C A B)" by (rule disjI2 [OF disj1])

  show "Col A B C" unfolding Col_def by (fact disj2)
qed

lemma col_from_bet3:
  fixes A B C :: Point
  shows "Bet C A B \<Longrightarrow> Col A B C"
proof -
  assume CAB: "Bet C A B"

  have disj1: "Bet B C A \<or> Bet C A B" by (rule disjI2 [OF CAB])
  have disj2: "Bet A B C \<or> (Bet B C A \<or> Bet C A B)" by (rule disjI2 [OF disj1])

  show "Col A B C" unfolding Col_def by (fact disj2)
qed

lemma col_permutation1: 
  fixes A B C :: Point
  shows "Col A B C \<Longrightarrow> Col B C A"
proof -
  assume col_ABC: "Col A B C"

  have disj1: "Bet A B C \<or> Bet B C A \<or> Bet C A B" 
    using col_ABC[unfolded Col_def] by assumption

  then consider (case1) "Bet A B C" | (case2) "Bet B C A" | (case3) "Bet C A B"
    by blast
  then show "Col B C A"
  proof cases
    case case1
    assume ABC: "Bet A B C"

    show "Col B C A" by (rule col_from_bet3 [OF ABC])
  next
    case case2
    assume BCA: "Bet B C A"

    show "Col B C A" by (rule col_from_bet1 [OF BCA])
  next
    case case3
    assume CAB: "Bet C A B"

    show "Col B C A" by (rule col_from_bet2 [OF CAB])
  qed
qed

lemma col_permutation2: 
  fixes A B C :: Point
  shows "Col A B C \<Longrightarrow> Col C A B"
proof -
  assume col_ABC: "Col A B C"

  have disj1: "Bet A B C \<or> Bet B C A \<or> Bet C A B" 
    using col_ABC[unfolded Col_def] by assumption

  then consider (case1) "Bet A B C" | (case2) "Bet B C A" | (case3) "Bet C A B"
    by blast
  then show "Col C A B"
  proof cases
    case case1
    assume ABC: "Bet A B C"

    show "Col C A B" by (rule col_from_bet2 [OF ABC])
  next
    case case2
    assume BCA: "Bet B C A"

    show "Col C A B" by (rule col_from_bet3 [OF BCA])
  next
    case case3
    assume CAB: "Bet C A B"

    show "Col C A B" by (rule col_from_bet1 [OF CAB])
  qed
qed

lemma col_permutation3: 
  fixes A B C :: Point
  shows "Col A B C \<Longrightarrow> Col C B A"
proof -
  assume col_ABC: "Col A B C"

  have disj1: "Bet A B C \<or> Bet B C A \<or> Bet C A B" 
    using col_ABC[unfolded Col_def] by assumption

    then consider (case1) "Bet A B C" | (case2) "Bet B C A" | (case3) "Bet C A B"
    by blast
  then show "Col C B A"
  proof cases
    case case1
    assume ABC: "Bet A B C"

    have CBA: "Bet C B A" by (rule bet_sym [OF ABC])
    show "Col C B A" by (rule col_from_bet1 [OF CBA])
  next
    case case2
    assume BCA: "Bet B C A"

    have ACB: "Bet A C B" by (rule bet_sym [OF BCA])
    show "Col C B A" by (rule col_from_bet3 [OF ACB])
  next
    case case3
    assume CAB: "Bet C A B"

    have BAC: "Bet B A C" by (rule bet_sym [OF CAB])
    show "Col C B A" by (rule col_from_bet2 [OF BAC])
  qed
qed

lemma col_permutation4: 
  fixes A B C :: Point
  shows "Col A B C \<Longrightarrow> Col B A C"
proof -
  assume col_ABC: "Col A B C"

  have disj1: "Bet A B C \<or> Bet B C A \<or> Bet C A B" 
    using col_ABC[unfolded Col_def] by assumption

  then consider (case1) "Bet A B C" | (case2) "Bet B C A" | (case3) "Bet C A B"
    by blast
  then show "Col B A C"
  proof cases
    case case1
    assume ABC: "Bet A B C"

    have CBA: "Bet C B A" by (rule bet_sym [OF ABC])
    show "Col B A C" by (rule col_from_bet3 [OF CBA])
  next
    case case2
    assume BCA: "Bet B C A"

    have ACB: "Bet A C B" by (rule bet_sym [OF BCA])
    show "Col B A C" by (rule col_from_bet2 [OF ACB])
  next
    case case3
    assume CAB: "Bet C A B"

    have BAC: "Bet B A C" by (rule bet_sym [OF CAB])
    show "Col B A C" by (rule col_from_bet1 [OF BAC])
  qed
qed

lemma col_permutation5: 
  fixes A B C :: Point
  shows "Col A B C \<Longrightarrow> Col A C B"
proof -
  assume col_ABC: "Col A B C"

  have disj1: "Bet A B C \<or> Bet B C A \<or> Bet C A B" 
    using col_ABC[unfolded Col_def] by assumption

    then consider (case1) "Bet A B C" | (case2) "Bet B C A" | (case3) "Bet C A B"
    by blast
  then show "Col A C B"
  proof cases
    case case1
    assume ABC: "Bet A B C"

    have CBA: "Bet C B A" by (rule bet_sym [OF ABC])
    show "Col A C B" by (rule col_from_bet2 [OF CBA])
  next
    case case2
    assume BCA: "Bet B C A"

    have ACB: "Bet A C B" by (rule bet_sym [OF BCA])
    show "Col A C B" by (rule col_from_bet1 [OF ACB])
  next
    case case3
    assume CAB: "Bet C A B"

    have BAC: "Bet B A C" by (rule bet_sym [OF CAB])
    show "Col A C B" by (rule col_from_bet3 [OF BAC])
  qed
qed

lemma not_col_permutation1: 
  fixes A B C :: Point
  shows "\<not> Col A B C \<Longrightarrow> \<not> Col B C A"
proof -
  assume not_col_ABC: "\<not> Col A B C"

  show "\<not> Col B C A"
  proof
    assume col_BCA: "Col B C A"

    have col_ABC: "Col A B C" using col_BCA by (rule col_permutation2 [of B C A])
    show "False" using not_col_ABC col_ABC by (rule notE)
  qed
qed

lemma not_col_permutation2: 
  fixes A B C :: Point
  shows "\<not> Col A B C \<Longrightarrow> \<not> Col C A B"
proof -
  assume not_col_ABC: "\<not> Col A B C"

  show "\<not> Col C A B"
  proof
    assume col_CAB: "Col C A B"

    have col_ABC: "Col A B C" using col_CAB by (rule col_permutation1 [of C A B])
    show "False" using not_col_ABC col_ABC by (rule notE)
  qed
qed

lemma not_col_permutation3: 
  fixes A B C :: Point
  shows "\<not> Col A B C \<Longrightarrow> \<not> Col C B A"
proof -
  assume not_col_ABC: "\<not> Col A B C"

  show "\<not> Col C B A"
  proof
    assume col_CBA: "Col C B A"

    have col_ABC: "Col A B C" using col_CBA by (rule col_permutation3 [of C B A])
    show "False" using not_col_ABC col_ABC by (rule notE)
  qed
qed

lemma not_col_permutation4:
  fixes A B C :: Point
  shows "\<not> Col A B C \<Longrightarrow> \<not> Col B A C"
proof -
  assume not_col_ABC: "\<not> Col A B C"

  show "\<not> Col B A C"
  proof
    assume col_BAC: "Col B A C"

    have col_ABC: "Col A B C" using col_BAC by (rule col_permutation4 [of B A C])
    show "False" using not_col_ABC col_ABC by (rule notE)
  qed
qed

lemma not_col_permutation5:
  fixes A B C :: Point
  shows "\<not> Col A B C \<Longrightarrow> \<not> Col A C B"
proof -
  assume not_col_ABC: "\<not> Col A B C"

  show "\<not> Col A C B"
  proof
    assume col_ACB: "Col A C B"

    have col_ABC: "Col A B C" using col_ACB by (rule col_permutation5 [of A C B])
    show "False" using not_col_ABC col_ABC by (rule notE)
  qed
qed

lemma col_left: 
  fixes A B :: Point
  shows "Col A A B"
proof -
  have AAB: "Bet A A B" by (rule bet_left [of A B])
  show "Col A A B" by (rule col_from_bet1 [OF AAB])
qed

lemma col_right: 
  fixes A B :: Point
  shows "Col A B B"
proof -
  have ABB: "Bet A B B" by (rule bet_right [of A B])
  show "Col A B B" by (rule col_from_bet1 [OF ABB])
qed

lemma col_elim: 
  fixes A B C :: Point
  fixes P :: bool
  shows "(Bet A B C \<Longrightarrow> P) \<Longrightarrow> (Bet B C A \<Longrightarrow> P) \<Longrightarrow> (Bet C A B \<Longrightarrow> P) \<Longrightarrow> Col A B C \<Longrightarrow> P"
proof -
  assume H1: "Bet A B C \<Longrightarrow> P"
  assume H2: "Bet B C A \<Longrightarrow> P"
  assume H3: "Bet C A B \<Longrightarrow> P"
  assume col_ABC: "Col A B C"

  from col_ABC[unfolded Col_def] 
  consider (case1) "Bet A B C" | (case2) "Bet B C A" | (case3) "Bet C A B"
    by blast
  then show "P"
  proof cases
    case case1
    assume ABC: "Bet A B C"

    show "P" by (rule H1 [OF ABC])
  next
    case case2
    assume BCA: "Bet B C A"

    show "P" by (rule H2 [OF BCA])
  next
    case case3
    assume CAB: "Bet C A B"

    show "P" by (rule H3 [OF CAB])
  qed
qed
end