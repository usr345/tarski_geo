theory Bet_le
  imports BetCongr
begin

lemma bet_conn:
  "A \<noteq> B \<Longrightarrow> Bet A B C \<Longrightarrow> Bet A B D \<Longrightarrow> Bet A C D \<or> Bet A D C"
proof -
  assume A_neq_B: "A \<noteq> B"
  assume ABC: "Bet A B C"
  assume ABD: "Bet A B D"

  have H1: "\<exists> C'. Bet A D C' \<and> Congr D C' C D" by (rule segment_construction [of A D C D])
  have H2: "\<exists> D'. Bet A C D' \<and> Congr C D' C D" by (rule segment_construction [of A C C D])

  obtain "C'" :: Point where
    ADC_1: "Bet A D C'" and
    DC1_CD: "Congr D C' C D"
    using H1 by blast

  have H3: "\<exists> B'. Bet A C' B' \<and> Congr C' B' C B" by (rule segment_construction [of A C' C B])

  obtain "D'" :: Point where
    ACD_1: "Bet A C D'" and
    CD1_CD: "Congr C D' C D"
    using H2 by blast

  obtain "B'" :: Point where
    ACB_1: "Bet A C' B'" and
    CB1_CB: "Congr C' B' C B"
    using H3 by blast

  have H4: "\<exists> B2. Bet A D' B2 \<and> Congr D' B2 D B" by (rule segment_construction [of A D' D B])

  obtain B2 :: Point where
    AD1B2: "Bet A D' B2" and
    D1B2_DB: "Congr D' B2 D B"
    using H4 by blast

  have DBA: "Bet D B A" by (rule bet_sym [OF ABD])
  have BDC1: "Bet B D C'" by (rule CBA_ACD_BCD [OF DBA ADC_1])

  have CD_DC1: "Congr C D D C'" by (rule congr_sym [OF DC1_CD])
  have CD_CD1: "Congr C D C D'" by (rule congr_sym [OF CD1_CD])

  have DC1_CD1: "Congr D C' C D'" by (rule congr_inner_transitivity [OF CD_DC1 CD_CD1])
  have DC1_D1C: "Congr D C' D' C" by (rule congr_right_comm [OF DC1_CD1])
  
  have DB_DB2: "Congr D B D' B2" by (rule congr_sym [OF D1B2_DB])
  have BD_B2D1: "Congr B D B2 D'" by (rule congr_reverse [OF DB_DB2])

  have D1CA: "Bet D' C A" by (rule bet_sym [OF ACD_1])
  have CD1B2: "Bet C D' B2" by (rule CBA_ACD_BCD [OF D1CA AD1B2])
  have B2D1C: "Bet B2 D' C" by (rule bet_sym [OF CD1B2])
  
  have BC1_B2C: "Congr B C' B2 C" using BDC1 B2D1C BD_B2D1 DC1_D1C by (rule congr_summa [of B D C' B2 D' C])

  have C1DA: "Bet C' D A" by (rule bet_sym [OF ADC_1])
  have DC1B1: "Bet D C' B'" by (rule CBA_ACD_BCD [OF C1DA ACB_1])

  show "Bet A C D \<or> Bet A D C"
  proof (cases "D = C'")

    assume D_eq_C1: "D = C'"

    have C1C1_CD: "Congr C' C' C D" using D_eq_C1 DC1_CD by (rule subst)
    have CD_C1C1: "Congr C D C' C'" by (rule congr_sym [OF C1C1_CD])
    have C_eq_D: "C = D" by (rule congr_id [OF CD_C1C1])
    have ACC: "Bet A C C" by (rule bet_right [of A C])
    have ACD: "Bet A C D" using C_eq_D ACC by (rule subst)
    show "Bet A C D \<or> Bet A D C" using ACD by (rule disjI1)
  next

    assume D_neq_C1: "D \<noteq> C'"

    have BC1B1: "Bet B C' B'" using BDC1 DC1B1 D_neq_C1 by (rule outer_transitivity_between2 [of B D C' B'])

    have CBA: "Bet C B A" by (rule bet_sym [OF ABC])
    have BCD1: "Bet B C D'" by (rule CBA_ACD_BCD [OF CBA ACD_1])

    show "Bet A C D \<or> Bet A D C"
    proof (cases "C = D'")
      assume C_eq_D1: "C = D'"

      have D1D1_CD: "Congr D' D' C D" using C_eq_D1 CD1_CD by (rule subst)
      have CD_D1D1: "Congr C D D' D'" by (rule congr_sym [OF D1D1_CD])

      have C_eq_D: "C = D" using CD_D1D1 by (rule congr_id)
      have ACC: "Bet A C C" by (rule bet_right [of A C])
      have ACD: "Bet A C D" using C_eq_D ACC by (rule subst)
      show "Bet A C D \<or> Bet A D C" using ACD by (rule disjI1)
    next
      assume C_neq_D1: "C \<noteq> D'"

      have BCB2: "Bet B C B2" using BCD1 CD1B2 C_neq_D1 by (rule bet_outer_trans [of B C D' B2])
      have B2CB: "Bet B2 C B" by (rule bet_sym [OF BCB2])
      have BB1_B2B: "Congr B B' B2 B" using BC1B1 B2CB BC1_B2C CB1_CB by (rule congr_summa [of B C' B' B2 C B])

      have ACB2: "Bet A C B2" by (rule ACD_ABC_ABD [OF AD1B2 ACD_1])
      have ABB2: "Bet A B B2" by (rule ACD_ABC_ABD [OF ACB2 ABC])
      have BB2_BB2: "Congr B B2 B B2" by (rule congr_refl [of B B2])

      have ABC1: "Bet A B C'" by (rule ACD_ABC_ABD [OF ADC_1 ABD])
      have ABB1: "Bet A B B'" by (rule ACD_ABC_ABD [OF ACB_1 ABC1])

      have BB1_BB2: "Congr B B' B B2" by (rule congr_right_comm [OF BB1_B2B])
      have B2_eq_B1: "B2 = B'" using A_neq_B ABB2 BB2_BB2 ABB1 BB1_BB2 
        by (rule construction_uniqueness [of A B B2 B B2 B'])

      have AD1B1: "Bet A D' B'" using B2_eq_B1 AD1B2 by (rule subst)
      have B1D1C: "Bet B' D' C" using B2_eq_B1 B2D1C by (rule subst)
      have BD_B1D1: "Congr B D B' D'" using B2_eq_B1 BD_B2D1 by (rule subst)
    qed
    
    
  qed
  
(*

A C' B'
A D C'
B D C'
A B C
A B D
B D C'
*)

