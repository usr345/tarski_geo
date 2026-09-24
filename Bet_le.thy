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

  have BC1B1: "Bet B C' B'"
  proof (cases "B = D")

    assume B_eq_D: "B = D"

    have ABC1: "Bet A B C'" using B_eq_D ADC_1 by (rule ssubst)
    have C1BA: "Bet C' B A" by (rule bet_sym [OF ABC1])
    show "Bet B C' B'" by (rule CBA_ACD_BCD [OF C1BA ACB_1])
  next

    assume B_neq_D: "B \<noteq> D"

    thm outer_transitivity_between2 [of B D C' B']
    show "Bet B C' B'" using BDC1 DC1B1  by (rule outer_transitivity_between2 [of B D C' B'])
    (* BDC1 D C' B' *)
  qed
  thm congr_summa [of B C' B' B2 C B]
(*
Bet B C' B' <- ?
Bet B2 C B
Congr B C' B2 C --- BC1_B2C
Congr C' B' C B --- CB1_CB
------------------
Congr B B' B2 B

A C' B'
A D C'
B D C'
A B C
A B D
B D C'
*)

  have BC1_B2C: "B B' B2 B" by rule congr_summa