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
  fixes A B C A' B' :: Point
  shows "Col A B C \<Longrightarrow> Congr A B A' B' \<Longrightarrow> \<exists> C' . Col A' B' C' \<and> Congr A C A' C' \<and> Congr B C B' C'"
proof -
  assume col_ABC: "Col A B C"
  assume AB_AB1: "Congr A B A' B'"

  have disj: "Bet A B C \<or> Bet B C A \<or> Bet C A B" 
    using col_ABC[unfolded Col_def] by assumption

    then consider (case1) "Bet A B C" | (case2) "Bet B C A" | (case3) "Bet C A B"
    by blast
  then show "\<exists> C' . Col A' B' C' \<and> Congr A C A' C' \<and> Congr B C B' C'"
  proof cases
    case case1
    assume ABC: "Bet A B C"

    have H1: "\<exists> C' . Bet A' B' C' \<and> Congr B' C' B C" by (rule segment_construction [of A' B' B C])

    obtain X :: Point where
      ABX_1: "Bet A' B' X" and
      BX1_BC: "Congr B' X B C"
      using H1 by blast

    have BC_BX1: "Congr B C B' X" by (rule congr_sym [OF BX1_BC])
    have AC_AX1: "Congr A C A' X" using ABC ABX_1 AB_AB1 BC_BX1 by (rule congr_summa)
    
    have col_ABX1: "Col A' B' X" by (rule col_from_bet1 [OF ABX_1])

    have conj1: "Congr A C A' X \<and> Congr B C B' X" using AC_AX1 BC_BX1 by (rule conjI)
    have conj2: "Col A' B' X \<and> Congr A C A' X \<and> Congr B C B' X" using col_ABX1 conj1 by (rule conjI)

    show "\<exists> C' . Col A' B' C' \<and> Congr A C A' C' \<and> Congr B C B' C'" using conj2 by (rule exI [of _ "X"])
  next
    case case2
    assume BCA: "Bet B C A"

    have ACB: "Bet A C B" by (rule bet_sym [OF BCA])
    have H1: "\<exists> C'. Bet A' C' B' \<and> Congr A C A' C' \<and> Congr C B C' B'" by (rule l4_5 [OF ACB AB_AB1])

    obtain X :: Point where
      AXB1: "Bet A' X B'" and
      AC_AX1: "Congr A C A' X" and
      CB_XB1: "Congr C B X B'"
      using H1 by blast

    have BXA1: "Bet B' X A'" by (rule bet_sym [OF AXB1])
    have col_ABX1: "Col A' B' X" by (rule col_from_bet2 [OF BXA1])

    have BC_BX1: "Congr B C B' X" by (rule congr_reverse [OF CB_XB1])

    have conj1: "Congr A C A' X \<and> Congr B C B' X" using AC_AX1 BC_BX1 by (rule conjI)
    have conj2: "Col A' B' X \<and> Congr A C A' X \<and> Congr B C B' X" using col_ABX1 conj1 by (rule conjI)

    show "\<exists> C' . Col A' B' C' \<and> Congr A C A' C' \<and> Congr B C B' C'" using conj2 by (rule exI [of _ "X"])    
  next
    case case3
    assume CAB: "Bet C A B"

    have H1: "\<exists> C' . Bet B' A' C' \<and> Congr A' C' A C" by (rule segment_construction [of B' A' A C])
    obtain X :: Point where
      BAX_1: "Bet B' A' X" and
      AX1_AC: "Congr A' X A C"
      using H1 by blast

    have BAC: "Bet B A C" by (rule bet_sym [OF CAB])
    have BA_BA1: "Congr B A B' A'" by (rule congr_reverse [OF AB_AB1])
    have AC_AX1: "Congr A C A' X" by (rule congr_sym [OF AX1_AC])
    
    have BC_BX1: "Congr B C B' X" using BAC BAX_1 BA_BA1 AC_AX1 by (rule congr_summa)
    have XBA_1: "Bet X A' B'" by (rule bet_sym [OF BAX_1])

    have col_ABX1: "Col A' B' X" by (rule col_from_bet3 [OF XBA_1])

    have conj1: "Congr A C A' X \<and> Congr B C B' X" using AC_AX1 BC_BX1 by (rule conjI)
    have conj2: "Col A' B' X \<and> Congr A C A' X \<and> Congr B C B' X" using col_ABX1 conj1 by (rule conjI)

    show "\<exists> C' . Col A' B' C' \<and> Congr A C A' C' \<and> Congr B C B' C'" using conj2 by (rule exI [of _ "X"])
  qed
qed

lemma l4_16:
  fixes A B C D A' B' C' D' :: Point
  shows "A \<noteq> B \<Longrightarrow> Col A B C \<Longrightarrow> Congr A B A' B' \<Longrightarrow> Congr B C B' C' \<Longrightarrow> Congr A C A' C' \<Longrightarrow> 
         Congr A D A' D' \<Longrightarrow> Congr B D B' D' \<Longrightarrow> Congr C D C' D'"
proof -
  assume A_ne_B: "A \<noteq> B"
  assume col_ABC: "Col A B C"
  assume AB_AB1: "Congr A B A' B'"
  assume BC_BC1: "Congr B C B' C'"
  assume AC_AC1: "Congr A C A' C'"
  assume AD_AD1: "Congr A D A' D'"
  assume BD_BD1: "Congr B D B' D'"

  have disj: "Bet A B C \<or> Bet B C A \<or> Bet C A B" 
    using col_ABC[unfolded Col_def] by assumption

    then consider (case1) "Bet A B C" | (case2) "Bet B C A" | (case3) "Bet C A B"
    by blast
  then show "Congr C D C' D'"
  proof cases
    case case1
    assume ABC: "Bet A B C"

    have ABC1: "Bet A' B' C'" by (rule l4_6 [OF ABC AB_AB1 BC_BC1 AC_AC1])
    show "Congr C D C' D'" by (rule five_segment [OF AB_AB1 BC_BC1 AD_AD1 BD_BD1 ABC ABC1 A_ne_B])
  next
    case case2
    assume BCA: "Bet B C A"

    have ACB: "Bet A C B" by (rule bet_sym [OF BCA])
    have CB_CB1: "Congr C B C' B'" by (rule congr_reverse [OF BC_BC1])
    
    have ABC1: "Bet A' C' B'" by (rule l4_6 [OF ACB AC_AC1 CB_CB1 AB_AB1])
    show "Congr C D C' D'" by (rule l4_2 [OF ACB ABC1 AB_AB1 CB_CB1 AD_AD1 BD_BD1])
  next
    case case3
    assume CAB: "Bet C A B"

    have BAC: "Bet B A C" by (rule bet_sym [OF CAB])
    have BA_BA1: "Congr B A B' A'" by (rule congr_reverse [OF AB_AB1])
    have B_ne_A: "B \<noteq> A" using A_ne_B by (rule not_sym) 

    thm l4_6 [of B A C B' A' C']
    have BAC1: "Bet B' A' C'" by (rule l4_6 [OF BAC BA_BA1 AC_AC1 BC_BC1])
    thm five_segment [of B A B' A' C C' D D']

    show "Congr C D C' D'" using BA_BA1 AC_AC1 BD_BD1 AD_AD1 BAC BAC1 B_ne_A  by (rule five_segment [of B A B' A' C C' D D'])
  qed
qed

lemma l4_17:
  fixes A B C P Q :: Point
  shows "A \<noteq> B \<Longrightarrow> Col A B C \<Longrightarrow> Congr A P A Q \<Longrightarrow> Congr B P B Q \<Longrightarrow> Congr C P C Q"
proof -
  assume A_ne_B: "A \<noteq> B"
  assume col_ABC: "Col A B C" 
  assume AP_AQ: "Congr A P A Q"
  assume BP_BQ: "Congr B P B Q"

  have AB_AB: "Congr A B A B" by (rule congr_refl [of A B])
  have BC_BC: "Congr B C B C" by (rule congr_refl [of B C])
  have AC_AC: "Congr A C A C" by (rule congr_refl [of A C])

  show "Congr C P C Q" using A_ne_B col_ABC AB_AB BC_BC AC_AC AP_AQ BP_BQ by (rule l4_16 [of A B C A B C P Q])
qed

lemma l4_18: 
  fixes A B C "C'" :: Point
  shows "A \<noteq> B \<Longrightarrow> Col A B C \<Longrightarrow> Congr A C A C' \<Longrightarrow> Congr B C B C' \<Longrightarrow> C = C'"
proof -
  assume A_ne_B: "A \<noteq> B"
  assume col_ABC: "Col A B C"
  assume AC_AC1: "Congr A C A C'"
  assume BC_BC1: "Congr B C B C'"

  have disj: "Bet A B C \<or> Bet B C A \<or> Bet C A B" 
    using col_ABC[unfolded Col_def] by assumption

    then consider (case1) "Bet A B C" | (case2) "Bet B C A" | (case3) "Bet C A B"
    by blast
  then show "C = C'"
  proof cases
    case case1
    assume ABC: "Bet A B C"

    have AB_AB: "Congr A B A B" by (rule congr_refl [of A B])
    have ABC1: "Bet A B C'" by (rule l4_6 [OF ABC AB_AB BC_BC1 AC_AC1])

    have BC1_BC1: "Congr B C' B C'" by (rule congr_refl [of B "C'"])
    show "C = C'" using A_ne_B ABC BC_BC1 ABC1 BC1_BC1 by (rule construction_uniqueness [of A B C B C' C'])
  next
    case case2
    assume BCA: "Bet B C A"

    have CA_C1A: "Congr C A C' A" by (rule congr_reverse [OF AC_AC1])
    have C1_eq_C: "C' = C" using BCA BC_BC1 CA_C1A by (rule cong3_bet_eq [of B C A C'])

    show "C = C'" using C1_eq_C by (rule sym)
  next
    case case3
    assume CAB: "Bet C A B"

    have B_ne_A: "B \<noteq> A" using A_ne_B by (rule not_sym)
    have CA_C1A: "Congr C A C' A" by (rule congr_reverse [OF AC_AC1])
    have AB_AB: "Congr A B A B" by (rule congr_refl [of A B])
    have CB_C1B: "Congr C B C' B" by (rule congr_reverse [OF BC_BC1])

    have C1AB: "Bet C' A B" using CAB CA_C1A AB_AB CB_C1B by (rule l4_6 [of C A B C' A B])
    
    have B_ne_A: "B \<noteq> A" using A_ne_B by (rule not_sym)
    have BAC: "Bet B A C" by (rule bet_sym [OF CAB])
    have BAC1: "Bet B A C'" by (rule bet_sym [OF C1AB])
    have AC1_AC1: "Congr A C' A C'" by (rule congr_refl [of A "C'"])

    show "C = C'" using B_ne_A BAC AC_AC1 BAC1 AC1_AC1 by (rule construction_uniqueness [of B A C A C' C'])
  qed
qed

lemma not_col_distincts:
  fixes A B C :: Point
  shows "\<not> Col A B C \<Longrightarrow> A \<noteq> B \<and> B \<noteq> C \<and> A \<noteq> C"
proof -

  assume ncol_ABC: "\<not> Col A B C"
  have disj: "\<not> (Bet A B C \<or> Bet B C A \<or> Bet C A B)"
    using ncol_ABC[unfolded Col_def] by assumption

  have conj1: "\<not> Bet A B C \<and> \<not> (Bet B C A \<or> Bet C A B)" using disj by (subst de_Morgan_disj[symmetric])

  have nABC: "\<not> Bet A B C" using conj1 by (rule conjunct1)
  have disj2: "\<not> (Bet B C A \<or> Bet C A B)" using conj1 by (rule conjunct2)
  have conj2: "\<not> Bet B C A \<and> \<not> Bet C A B" using disj2 by (subst de_Morgan_disj[symmetric])

  have nBCA: "\<not> Bet B C A" using conj2 by (rule conjunct1)
  have nCAB: "\<not> Bet C A B" using conj2 by (rule conjunct2)

  have A_neq_B: "A \<noteq> B"
  proof
    assume A_eq_B: "A = B"

    have nBBC: "\<not> Bet B B C" using A_eq_B nABC by (rule subst)
    have BBC: "Bet B B C" by (rule bet_left [of B C])
    show "False" using nBBC BBC by (rule notE)
  qed

  have B_neq_C: "B \<noteq> C"
  proof
    assume B_eq_C: "B = C"

    have nCCA: "\<not> Bet C C A" using B_eq_C nBCA by (rule subst)
    have CCA: "Bet C C A" by (rule bet_left [of C A])
    show "False" using nCCA CCA by (rule notE)
  qed

  have A_neq_C: "A \<noteq> C"
  proof
    assume A_eq_C: "A = C"

    have nCCB: "\<not> Bet C C B" using A_eq_C nCAB by (rule subst)
    have CCB: "Bet C C B" by (rule bet_left [of C B])
    show "False" using nCCB CCB by (rule notE)
  qed

  have conj3: "B \<noteq> C \<and> A \<noteq> C" using B_neq_C A_neq_C by (rule conjI)
  show "A \<noteq> B \<and> B \<noteq> C \<and> A \<noteq> C" using A_neq_B conj3 by (rule conjI)
qed

lemma col_congr_full_eq:
  fixes A B C "A'" "B'" C1 C2 :: Point
  shows "A \<noteq> B \<Longrightarrow> Col A B C \<Longrightarrow> Congr A B A' B' \<Longrightarrow> Congr B C B' C1 \<Longrightarrow> 
         Congr A C A' C1 \<Longrightarrow> Congr B C B' C2 \<Longrightarrow> Congr A C A' C2 \<Longrightarrow> C1 = C2"
proof -
  assume A_neq_B: "A \<noteq> B"
  assume col_ABC: "Col A B C"
  assume AB_AB_1: "Congr A B A' B'"
  assume BC_BC1: "Congr B C B' C1"
  assume AC_AC1: "Congr A C A' C1"
  assume BC_BC2: "Congr B C B' C2"
  assume AC_AC2: "Congr A C A' C2"

  have disj: "Bet A B C \<or> Bet B C A \<or> Bet C A B" 
    using col_ABC[unfolded Col_def] by assumption

    then consider (case1) "Bet A B C" | (case2) "Bet B C A" | (case3) "Bet C A B"
    by blast
  then show "C1 = C2"
  proof cases
    case case1
    assume ABC: "Bet A B C"

    have A1_ne_B1: "A' \<noteq> B'" using A_neq_B AB_AB_1 by (rule congr_neq)
    have BC1_BC: "Congr B' C1 B C" by (rule congr_sym [OF BC_BC1])
    have BC2_BC: "Congr B' C2 B C" by (rule congr_sym [OF BC_BC2])

    have ABC1: "Bet A' B' C1" using ABC AB_AB_1 BC_BC1 AC_AC1 by (rule l4_6 [of A B C "A'" "B'" C1])
    have ABC2: "Bet A' B' C2" using ABC AB_AB_1 BC_BC2 AC_AC2 by (rule l4_6 [of A B C "A'" "B'" C2])

    show "C1 = C2" using A1_ne_B1 ABC1 BC1_BC ABC2 BC2_BC  by (rule construction_uniqueness [of "A'" "B'" C1 B C C2])
  next
    case case2
    assume BCA: "Bet B C A"

    have CA_C1A: "Congr C A C1 A'" by (rule congr_reverse [OF AC_AC1])
    have BA_BA1: "Congr B A B' A'" by (rule congr_reverse [OF AB_AB_1])
    
    have BC1A: "Bet B' C1 A'" using BCA BC_BC1 CA_C1A BA_BA1 by (rule l4_6 [of B C A B' C1 A'])
    have AC1B: "Bet A' C1 B'" by (rule bet_sym [OF BC1A])

    have AC1_AC2: "Congr A' C1 A' C2" by (rule congr_inner_transitivity [OF AC_AC1 AC_AC2])
    have BC1_BC2: "Congr B' C1 B' C2" by (rule congr_inner_transitivity [OF BC_BC1 BC_BC2])

    have C1B_C2B: "Congr C1 B' C2 B'" by (rule congr_reverse [OF BC1_BC2])
    have C2_eq_C1: "C2 = C1" using AC1B AC1_AC2 C1B_C2B  by (rule cong3_bet_eq [of A' C1 B' C2])

    show "C1 = C2" using C2_eq_C1 by (rule sym)
  next
    case case3
    assume CAB: "Bet C A B"

    have B_neq_A: "B \<noteq> A" using A_neq_B by (rule not_sym)

    have BA_BA1: "Congr B A B' A'" by (rule congr_reverse [OF AB_AB_1])
    have B1_neq_A1: "B' \<noteq> A'" using B_neq_A BA_BA1 by (rule congr_neq [of B A B' A'])
    have BAC: "Bet B A C" by (rule bet_sym [OF CAB])

    have BAC1: "Bet B' A' C1" using BAC BA_BA1 AC_AC1 BC_BC1 by (rule l4_6 [of B A C B' A' C1])   
    have AC1_AC: "Congr A' C1 A C" by (rule congr_sym [OF AC_AC1])

    have BAC2: "Bet B' A' C2" using BAC BA_BA1 AC_AC2 BC_BC2 by (rule l4_6 [of B A C B' A' C2])   
    have AC2_AC: "Congr A' C2 A C" by (rule congr_sym [OF AC_AC2])

    show "C1 = C2" using B1_neq_A1 BAC1 AC1_AC BAC2 AC2_AC by (rule construction_uniqueness [of "B'" "A'" C1 A C C2])
  qed
qed
end