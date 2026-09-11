theory Bet
  imports Axioms Bet Congr
begin

lemma congr_summa:
  fixes A B C A' B' C' :: Point
  shows "Bet A B C \<Longrightarrow> Bet A' B' C' \<Longrightarrow> Congr A B A' B' \<Longrightarrow> 
          Congr B C B' C' \<Longrightarrow> Congr A C A' C'"
proof -
  assume H1: "Bet A B C"
  assume H2: "Bet A' B' C'"
  assume H3: "Congr A B A' B'"
  assume H4: "Congr B C B' C'"

  show "Congr A C A' C'"
  proof (cases "A = B")

    assume Heq: "A = B"

    have H5: "Congr A C B' C'" using Heq H4 by (rule ssubst)
    have H6: "Congr B B A' B'" using Heq H3 by (rule subst)
    have H7: "Congr A' B' B B" by (rule congr_sym [OF H6])
    have Heq': "A' = B'" by (rule congr_id [OF H7])

    show "Congr A C A' C'" using Heq' H5 by (rule ssubst)
  next

    assume Hneq: "A \<noteq> B"
    have H5: "Congr A A A' A'" by (rule congr_trivial_identity [of A A'])
    have H6: "Congr B A B' A'" by (rule congr_reverse [OF H3])
    have H7:  "Congr C A C' A'" using H3 H4 H5 H6 H1 H2 Hneq by (rule five_segment)
    
    show "Congr A C A' C'" by (rule congr_reverse [OF H7])
  qed
qed

lemma l4_2:
  fixes A B C D A' B' C' D' :: Point
  shows "Bet A B C \<Longrightarrow> Bet A' B' C' \<Longrightarrow> Congr A C A' C' \<Longrightarrow> 
         Congr B C B' C' \<Longrightarrow> Congr A D A' D' \<Longrightarrow> Congr C D C' D' \<Longrightarrow> Congr B D B' D'"
proof -
  assume H1: "Bet A B C"
  assume H2: "Bet A' B' C'"
  assume H3: "Congr A C A' C'"
  assume H4: "Congr B C B' C'"
  assume H5: "Congr A D A' D'"
  assume H6: "Congr C D C' D'"

  show ?thesis
  proof (cases "A = C")
    assume A_eq_C: "A = C"
    have H7: "Bet C B C" using A_eq_C H1 by (rule subst)
    have C_eq_B: "C = B" by (rule bet_id [OF H7])

    have H8: "Congr B D C' D'" using C_eq_B H6 by (rule subst)
    have H9: "Congr C C A' C'" using A_eq_C H3 by (rule subst)
    then have H10: "Congr A' C' C C" by (rule congr_sym)

    have A1_eq_C1: "A' = C'" by (rule congr_id [OF H10])
    have H11: "Bet C' B' C'" using A1_eq_C1 H2 by (rule subst)
    have C1_eq_B1: "C' = B'" by (rule bet_id [OF H11])

    show "Congr B D B' D'" using C1_eq_B1 H8 by (rule subst)
  next
    assume A_neq_C: "A \<noteq> C"
    have H7: "\<exists> E . Bet A C E \<and> C \<noteq> E" by (rule point_construction_different [of A C])
    obtain E :: Point where
      ACE: "Bet A C E" and
      H9: "C \<noteq> E"
      using H7 by blast

    have H10: "\<exists> E' . Bet A' C' E' \<and> Congr C' E' C E" by (rule segment_construction [of A' C' C E])
    obtain E' :: Point where
      H11: "Bet A' C' E'" and
      H12: "Congr C' E' C E"
      using H10 by blast

    have H13: "Congr C E C' E'" by (rule congr_sym [OF H12])
    have ED_co_E1D1: "Congr E D E' D'" using H3 H13 H5 H6 ACE H11 A_neq_C by (rule five_segment)

    have H14: "Congr E C E' C'" by (rule congr_reverse [OF H13])
    have H15: "Congr C B C' B'" by (rule congr_reverse [OF H4])

    have CBA: "Bet C B A" by (rule bet_sym [OF H1])
    have H16: "Bet B C E" by (rule CBA_BCD [OF CBA ACE])
    have ECB: "Bet E C B" by (rule bet_sym [OF H16])

    have C1B1A1: "Bet C' B' A'" by (rule bet_sym [OF H2])
    have H17: "Bet B' C' E'" by (rule CBA_BCD [OF C1B1A1 H11])
    have E1C1B1: "Bet E' C' B'" by (rule bet_sym [OF H17])

    have E_neq_C: "E \<noteq> C" by (rule H9[symmetric])
    show "Congr B D B' D'" using H14 H15 ED_co_E1D1 H6 ECB E1C1B1 E_neq_C by (rule five_segment)
  qed
qed

lemma l4_3:
  fixes A B C A' B' C' :: Point
  shows "Bet A B C \<Longrightarrow> Bet A' B' C' \<Longrightarrow> Congr A C A' C' \<Longrightarrow> Congr B C B' C' \<Longrightarrow> Congr A B A' B'"
proof -
  assume ABC: "Bet A B C"
  assume ABC1: "Bet A' B' C'"
  assume AC_AC1: "Congr A C A' C'"
  assume BC_BC1: "Congr B C B' C'"

  have AA_AA1: "Congr A A A' A'" by (rule congr_trivial_identity [of A A'])
  have CA_CA1: "Congr C A C' A'" by (rule congr_reverse [OF AC_AC1])

  have H1: "Congr B A B' A'" by (rule l4_2 [OF ABC ABC1 AC_AC1 BC_BC1 AA_AA1 CA_CA1])
  show "Congr A B A' B'" by (rule congr_reverse [OF H1])
qed

lemma l4_3_1:
  fixes A B C A' B' C' :: Point
  shows "Bet A B C \<Longrightarrow> Bet A' B' C' \<Longrightarrow> Congr A B A' B' \<Longrightarrow> Congr A C A' C' \<Longrightarrow> Congr B C B' C'"
proof -
  assume ABC: "Bet A B C"
  assume ABC1: "Bet A' B' C'"
  assume AB_AB1: "Congr A B A' B'"
  assume AC_AC1: "Congr A C A' C'"

  have CBA: "Bet C B A" by (rule bet_sym [OF ABC])
  have CBA_1: "Bet C' B' A'" by (rule bet_sym [OF ABC1])

  have CA_CA1: "Congr C A C' A'" by (rule congr_reverse [OF AC_AC1])
  have BA_BA1: "Congr B A B' A'" by (rule congr_reverse [OF AB_AB1])
  have CC_CC1: "Congr C C C' C'" by (rule congr_trivial_identity [of C C'])

  thm l4_2
  show "Congr B C B' C'" using CBA CBA_1 CA_CA1 BA_BA1 CC_CC1 AC_AC1 by (rule l4_2)
qed

lemma l4_5:
  fixes A B C A' C' :: Point
  shows "Bet A B C \<Longrightarrow> Congr A C A' C' \<Longrightarrow> \<exists> B' . Congr A B A' B' \<and> Congr B C B' C' \<and> Congr A C A' C'"
proof -