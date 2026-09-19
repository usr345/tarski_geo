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

lemma col_ABC_BCA:
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

lemma col_ABC_CAB: 
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

lemma col_ABC_CBA: 
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

lemma col_ABC_BAC: 
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

lemma col_ABC_ACB: 
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

lemma not_col_ABC_BCA: 
  fixes A B C :: Point
  shows "\<not> Col A B C \<Longrightarrow> \<not> Col B C A"
proof -
  assume not_col_ABC: "\<not> Col A B C"

  show "\<not> Col B C A"
  proof
    assume col_BCA: "Col B C A"

    have col_ABC: "Col A B C" using col_BCA by (rule col_ABC_CAB [of B C A])
    show "False" using not_col_ABC col_ABC by (rule notE)
  qed
qed

lemma not_col_ABC_CAB: 
  fixes A B C :: Point
  shows "\<not> Col A B C \<Longrightarrow> \<not> Col C A B"
proof -
  assume not_col_ABC: "\<not> Col A B C"

  show "\<not> Col C A B"
  proof
    assume col_CAB: "Col C A B"

    have col_ABC: "Col A B C" using col_CAB by (rule col_ABC_BCA [of C A B])
    show "False" using not_col_ABC col_ABC by (rule notE)
  qed
qed

lemma not_col_ABC_CBA: 
  fixes A B C :: Point
  shows "\<not> Col A B C \<Longrightarrow> \<not> Col C B A"
proof -
  assume not_col_ABC: "\<not> Col A B C"

  show "\<not> Col C B A"
  proof
    assume col_CBA: "Col C B A"

    have col_ABC: "Col A B C" using col_CBA by (rule col_ABC_CBA [of C B A])
    show "False" using not_col_ABC col_ABC by (rule notE)
  qed
qed

lemma not_col_ABC_BAC:
  fixes A B C :: Point
  shows "\<not> Col A B C \<Longrightarrow> \<not> Col B A C"
proof -
  assume not_col_ABC: "\<not> Col A B C"

  show "\<not> Col B A C"
  proof
    assume col_BAC: "Col B A C"

    have col_ABC: "Col A B C" using col_BAC by (rule col_ABC_BAC [of B A C])
    show "False" using not_col_ABC col_ABC by (rule notE)
  qed
qed

lemma not_col_ABC_ACB:
  fixes A B C :: Point
  shows "\<not> Col A B C \<Longrightarrow> \<not> Col A C B"
proof -
  assume not_col_ABC: "\<not> Col A B C"

  show "\<not> Col A C B"
  proof
    assume col_ACB: "Col A C B"

    have col_ABC: "Col A B C" using col_ACB by (rule col_ABC_ACB [of A C B])
    show "False" using not_col_ABC col_ABC by (rule notE)
  qed
qed

lemma col_AAB: 
  fixes A B :: Point
  shows "Col A A B"
proof -
  have AAB: "Bet A A B" by (rule bet_left [of A B])
  show "Col A A B" by (rule col_from_bet1 [OF AAB])
qed

lemma col_ABB: 
  fixes A B :: Point
  shows "Col A B B"
proof -
  have ABB: "Bet A B B" by (rule bet_right [of A B])
  show "Col A B B" by (rule col_from_bet1 [OF ABB])
qed

lemma col_ABA: 
  fixes A B :: Point
  shows "Col A B A"
proof -
  have AAB: "Bet A A B" by (rule bet_left [of A B])
  show "Col A B A" by (rule col_from_bet3 [OF AAB])
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

lemma l4_13: 
  fixes A B C A' B' C' :: Point
  shows "Col A B C \<Longrightarrow> Congr A B A' B' \<Longrightarrow> Congr B C B' C' \<Longrightarrow> Congr A C A' C' \<Longrightarrow> Col A' B' C'"
proof -
  assume col_ABC: "Col A B C"
  assume AB_AB1: "Congr A B A' B'"
  assume BC_BC1: "Congr B C B' C'"
  assume AC_AC1: "Congr A C A' C'"

  have disj1: "Bet A B C \<or> Bet B C A \<or> Bet C A B" 
    using col_ABC[unfolded Col_def] by assumption

    then consider (case1) "Bet A B C" | (case2) "Bet B C A" | (case3) "Bet C A B"
    by blast
  then show "Col A' B' C'"
  proof cases
    case case1
    assume ABC: "Bet A B C"
    
    have ABC_1: "Bet A' B' C'" by (rule l4_6 [OF ABC AB_AB1 BC_BC1 AC_AC1])
    show "Col A' B' C'" by (rule col_from_bet1 [OF ABC_1])
  next
    case case2
    assume BCA: "Bet B C A"

    have CA_CA1: "Congr C A C' A'" by (rule congr_reverse [OF AC_AC1])
    have BA_BA1: "Congr B A B' A'" by (rule congr_reverse [OF AB_AB1])

    have BCA_1: "Bet B' C' A'" by (rule l4_6 [OF BCA BC_BC1 CA_CA1 BA_BA1])
    show "Col A' B' C'" by (rule col_from_bet2 [OF BCA_1])
  next
    case case3
    assume CAB: "Bet C A B"

    have CA_CA1: "Congr C A C' A'" by (rule congr_reverse [OF AC_AC1])
    have CB_CB1: "Congr C B C' B'" by (rule congr_reverse [OF BC_BC1])
    have CAB_1: "Bet C' A' B'" by (rule l4_6 [OF CAB CA_CA1 AB_AB1 CB_CB1])
    show "Col A' B' C'" by (rule col_from_bet3 [OF CAB_1])
  qed
qed

lemma l4_14: 
  fixes A B C A' C' :: Point
  shows "Col A B C \<Longrightarrow> Congr A C A' C' \<Longrightarrow> \<exists> B' . Col A' B' C' \<and> Congr A B A' B' \<and> Congr B C B' C'"
proof -
  assume col_ABC: "Col A B C"
  assume AC_AC1: "Congr A C A' C'"

  have disj1: "Bet A B C \<or> Bet B C A \<or> Bet C A B" 
    using col_ABC[unfolded Col_def] by assumption

    then consider (case1) "Bet A B C" | (case2) "Bet B C A" | (case3) "Bet C A B"
    by blast
  then show "\<exists> B' . Col A' B' C' \<and> Congr A B A' B' \<and> Congr B C B' C'"
  proof cases
    case case1
    assume ABC: "Bet A B C"

    have H1: "\<exists> B' .  Bet A' B' C' \<and> Congr A B A' B' \<and> Congr B C B' C'" by (rule l4_5 [OF ABC AC_AC1])

    obtain X :: Point where
      conj1: "Bet A' X C' \<and> Congr A B A' X \<and> Congr B C X C'"
      using H1 by (elim exE)

    from conj1 have AXC_1: "Bet A' X C'"
      by (rule conjunct1)

    from conj1 have conj2: "Congr A B A' X \<and> Congr B C X C'"
      by (rule conjunct2)

    have col_AXC1: "Col A' X C'" by (rule col_from_bet1 [OF AXC_1])
    have conj3: "Col A' X C' \<and> Congr A B A' X \<and> Congr B C X C'" using col_AXC1 conj2 by (rule conjI)

    show "\<exists> B' . Col A' B' C' \<and> Congr A B A' B' \<and> Congr B C B' C'" using conj3 by (rule exI [of _ "X"])
  next
    case case2
    assume BCA: "Bet B C A"

    thm l4_5 [of B C A A' C']
    have H1: "\<exists> B' .  Bet A' B' C' \<and> Congr B C A' B' \<and> Congr C A B' C'" by (rule l4_5 [OF BCA AC_AC1])

    obtain X :: Point where
      conj1: "Bet A' X C' \<and> Congr A B A' X \<and> Congr B C X C'"
      using H1 by (elim exE)

    from conj1 have AXC_1: "Bet A' X C'"
      by (rule conjunct1)

    from conj1 have conj2: "Congr A B A' X \<and> Congr B C X C'"
      by (rule conjunct2)

    have col_AXC1: "Col A' X C'" by (rule col_from_bet1 [OF AXC_1])
    have conj3: "Col A' X C' \<and> Congr A B A' X \<and> Congr B C X C'" using col_AXC1 conj2 by (rule conjI)

    show "\<exists> B' . Col A' B' C' \<and> Congr A B A' B' \<and> Congr B C B' C'" using conj3 by (rule exI [of _ "X"])
  next
    case case3
    assume CAB: "Bet C A B"

    have CA_CA1: "Congr C A C' A'" by (rule congr_reverse [OF AC_AC1])
    have CB_CB1: "Congr C B C' B'" by (rule congr_reverse [OF BC_BC1])
    have CAB_1: "Bet C' A' B'" by (rule l4_6 [OF CAB CA_CA1 AB_AB1 CB_CB1])
    show "Col A' B' C'" by (rule col_from_bet3 [OF CAB_1])
  qed
end