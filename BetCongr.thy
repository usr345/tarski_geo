theory BetCongr
  imports Bet Congr
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
  assume ABC: "Bet A B C"
  assume ABC_1: "Bet A' B' C'"
  assume AC_AC1: "Congr A C A' C'"
  assume BC_BC1: "Congr B C B' C'"
  assume AD_AD1: "Congr A D A' D'"
  assume CD_CD1: "Congr C D C' D'"

  show ?thesis
  proof (cases "A = C")
    assume A_eq_C: "A = C"
    have H7: "Bet C B C" using A_eq_C ABC by (rule subst)
    have C_eq_B: "C = B" by (rule bet_id [OF H7])

    have H8: "Congr B D C' D'" using C_eq_B CD_CD1 by (rule subst)
    have H9: "Congr C C A' C'" using A_eq_C AC_AC1 by (rule subst)
    then have H10: "Congr A' C' C C" by (rule congr_sym)

    have A1_eq_C1: "A' = C'" by (rule congr_id [OF H10])
    have H11: "Bet C' B' C'" using A1_eq_C1 ABC_1 by (rule subst)
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
    have ED_co_E1D1: "Congr E D E' D'" using AC_AC1 H13 AD_AD1 CD_CD1 ACE H11 A_neq_C by (rule five_segment)

    have H14: "Congr E C E' C'" by (rule congr_reverse [OF H13])
    have H15: "Congr C B C' B'" by (rule congr_reverse [OF BC_BC1])

    have CBA: "Bet C B A" by (rule bet_sym [OF ABC])
    have BCE: "Bet B C E" by (rule CBA_ACD_BCD [OF CBA ACE])
    have ECB: "Bet E C B" by (rule bet_sym [OF BCE])

    have CBA_1: "Bet C' B' A'" by (rule bet_sym [OF ABC_1])
    have BCE_1: "Bet B' C' E'" by (rule CBA_ACD_BCD [OF CBA_1 H11])
    have ECB_1: "Bet E' C' B'" by (rule bet_sym [OF BCE_1])

    have E_neq_C: "E \<noteq> C" by (rule H9[symmetric])
    show "Congr B D B' D'" using H14 H15 ED_co_E1D1 CD_CD1 ECB ECB_1 E_neq_C by (rule five_segment)
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

  show "Congr B C B' C'" using CBA CBA_1 CA_CA1 BA_BA1 CC_CC1 AC_AC1 by (rule l4_2)
qed

lemma l4_5:
  fixes A B C A' C' :: Point
  shows "Bet A B C \<Longrightarrow> Congr A C A' C' \<Longrightarrow> \<exists> B' .  Bet A' B' C' \<and> Congr A B A' B' \<and> Congr B C B' C'"
proof -
  assume ABC: "Bet A B C"
  assume AC_AC1: "Congr A C A' C'"

  have H1: "\<exists> X . Bet A' C' X \<and> C' \<noteq> X" by (rule point_construction_different [of A' C'])
  obtain X :: Point where
    ACX_1: "Bet A' C' X" and
    C1_ne_X: "C' \<noteq> X"
    using H1 by blast

  have H2: "\<exists> B'. Bet X C' B' \<and> Congr C' B' C B" by (rule segment_construction [of X C' C B])
  obtain B' :: Point where
    XCB_1: "Bet X C' B'" and
    CB1_CB: "Congr C' B' C B"
    using H2 by blast

  have CB_CB1: "Congr C B C' B'" by (rule congr_sym [OF CB1_CB])
  have BC_BC1: "Congr B C B' C'" by (rule congr_reverse [OF CB_CB1])
  
  have H3: "\<exists> Y. Bet X B' Y \<and> Congr B' Y B A" by (rule segment_construction [of X B' B A])
  obtain Y :: Point where
    XBY_1: "Bet X B' Y" and
    B1Y_BA: "Congr B' Y B A"
    using H3 by blast

  have BCX_1: "Bet B' C' X" by (rule bet_sym [OF XCB_1])
  have CBY_1: "Bet C' B' Y" by (rule CBA_ACD_BCD [OF BCX_1 XBY_1])

  have CBA: "Bet C B A" by (rule bet_sym [OF ABC])
  have CB1_CB: "Congr C' B' C B" by (rule congr_sym [OF CB_CB1])

  have CY1_CA: "Congr C' Y C A" by (rule congr_summa [OF CBY_1 CBA CB1_CB B1Y_BA])
  have YB1X: "Bet Y B' X" by (rule bet_sym [OF XBY_1])
  have YC1X: "Bet Y C' X" using YB1X BCX_1 by (rule ABD_BCD_ACD [where A=Y and B="B'" and C="C'" and D=X])
  have XC1Y: "Bet X C' Y" by (rule bet_sym [OF YC1X])

  have X_ne_C1: "X \<noteq> C'" by (rule not_sym [OF C1_ne_X])
  have AC1_AC: "Congr A' C' A C" by (rule congr_sym [OF AC_AC1])
  have CA1_CA: "Congr C' A' C A" by (rule congr_reverse [OF AC1_AC])

  have XCA_1: "Bet X C' A'" by (rule bet_sym [OF ACX_1])
  have Y_eq_A1: "Y = A'" using X_ne_C1 XC1Y CY1_CA XCA_1 CA1_CA by (rule construction_uniqueness [of X C' Y C A A'])

  have BA1_BA: "Congr B' A' B A" using Y_eq_A1 B1Y_BA by (rule subst)
  have AB1_AB: "Congr A' B' A B" by (rule congr_reverse [OF BA1_BA])
  have AB_AB1: "Congr A B A' B'" by (rule congr_sym [OF AB1_AB])

  have CBA_1: "Bet C' B' A'" using Y_eq_A1 CBY_1 by (rule subst)
  have ABC_1: "Bet A' B' C'" by (rule bet_sym [OF CBA_1])
  have conj: "Congr A B A' B' \<and> Congr B C B' C'" by (rule conjI [OF AB_AB1 BC_BC1])
  have conj1: "Bet A' B' C' \<and> Congr A B A' B' \<and> Congr B C B' C'" by 
        (rule conjI [OF ABC_1 conj])
  show "\<exists> B' .  Bet A' B' C' \<and> Congr A B A' B' \<and> Congr B C B' C'" using conj1 by (rule exI [of _ "B'"])
qed

lemma l4_6 : 
  fixes A B C A' B' C' :: Point
  shows "Bet A B C \<Longrightarrow> Congr A B A' B' \<Longrightarrow> Congr B C B' C' \<Longrightarrow> Congr A C A' C' \<Longrightarrow> Bet A' B' C'"
proof -
  assume ABC: "Bet A B C"
  assume AB_AB1: "Congr A B A' B'"
  assume BC_BC1: "Congr B C B' C'"
  assume AC_AC1: "Congr A C A' C'"

  have H1: "\<exists> X . Bet A' X C' \<and> Congr A B A' X \<and> Congr B C X C'" by (rule l4_5 [OF ABC AC_AC1])
  obtain X :: Point where
    AXC_1: "Bet A' X C'" and
    conj: "Congr A B A' X \<and> Congr B C X C'"
    using H1 by blast

  have AB_AX1: "Congr A B A' X" by (rule conjunct1 [OF conj])
  have BC_XC1: "Congr B C X C'" by (rule conjunct2 [OF conj])

  have AX1_AB: "Congr A' X A B" by (rule congr_sym [OF AB_AX1])
  have AX_AB1: "Congr A' X A' B'" by (rule congr_trans [OF AX1_AB AB_AB1])

  have XC1_BC: "Congr X C' B C" by (rule congr_sym [OF BC_XC1])
  have XC_BC1: "Congr X C' B' C'" by (rule congr_trans [OF XC1_BC BC_BC1])

  have CX_CB1: "Congr C' X C' B'" by (rule congr_reverse [OF XC_BC1])
  have AC_AC1: "Congr A' C' A' C'" by (rule congr_refl [of A' C'])
  have XC_XC1: "Congr X C' X C'" by (rule congr_refl [of X C'])

  have XX_XB1: "Congr X X X B'" using AXC_1 AXC_1 AC_AC1 XC_XC1 AX_AB1 CX_CB1
    by (rule l4_2 [where A="A'" and B=X and C="C'" and D=X and A'="A'" 
          and B'="X" and C'="C'" and D'="B'"])

  have XB1_XX: "Congr X B' X X" by (rule congr_sym [OF XX_XB1])
  have X_eq_B1: "X = B'" by (rule congr_id [OF XB1_XX])
  show "Bet A' B' C'" using X_eq_B1 AXC_1 by (rule subst)
qed

lemma cong3_bet_eq:
  fixes A B C X :: Point
  shows "Bet A B C \<Longrightarrow> Congr A B A X \<Longrightarrow> Congr B C X C \<Longrightarrow> X = B"
proof -
  assume ABC: "Bet A B C"
  assume AB_AX: "Congr A B A X"
  assume BC_XC: "Congr B C X C"

  have AC_AC: "Congr A C A C" by (rule congr_refl [of A C])
  have BC_BC: "Congr B C B C" by (rule congr_refl [of B C])
  have CB_CX: "Congr C B C X" by (rule congr_reverse [OF BC_XC])

  have BB_BX: "Congr B B B X" using ABC ABC AC_AC BC_BC AB_AX CB_CX
    by (rule l4_2 [where A="A" and B=B and C=C and D=B and A'=A 
          and B'=B and C'=C and D'=X])

  have BX_BB: "Congr B X B B" by (rule congr_sym [OF BB_BX])
  have B_eq_X: "B = X" by (rule congr_id [OF BX_BB])

  show "X = B" using B_eq_X by (rule sym)
qed
end