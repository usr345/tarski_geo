theory Bet
  imports Axioms Congr
begin

lemma bet_right:
  fixes A B :: Point
  shows "Bet A B B"
proof -

 have L0: "\<exists>E. Bet A B E \<and> Congr B E B B"
   using segment_construction [of A B B B] by this

 obtain E where
  H1: "Bet A B E" and
  H2: "Congr B E B B"
  using L0  by blast

  have L1: "B = E"
    using H2  by (rule congr_id)

  show Goal: "Bet A B B"
    using L1 H1 by (rule ssubst)
qed

lemma bet_sym:
  fixes A B C D :: Point
  shows "Bet A B C \<Longrightarrow> Bet C B A"
proof -

  assume H: "Bet A B C"

  have L1: "Bet B C C"
    by (rule bet_right [of B C])

  have construction: "\<exists>X. Bet B X B \<and> Bet C X A"
    using inner_pasch H L1 by this

  obtain X where
    L2: "Bet B X B" and
    L3: "Bet C X A"
    using construction by blast

  have L4: "B = X"
    using L2
    by (rule bet_id)

  show Goal: "Bet C B A"
    using L4 L3 by (rule ssubst)

qed

lemma bet_left:
  fixes A B C D :: Point
  shows "Bet A A B"
proof -

  have L1: "Bet B A A"
    by (rule bet_right)

  show Goal: "Bet A A B"
    using L1 by (rule bet_sym)
qed

lemma two_distinct_points: "\<exists> (A :: Point) . \<exists> (B :: Point). A \<noteq> B"
proof -
  have H1:  "\<exists>A B C.
       \<not> Bet A B C \<and>
       \<not> Bet B C A \<and>
       \<not> Bet C A B" by (rule lower_dim)

  obtain A B C where
    not_ABC: "\<not> Bet A B C" and
    not_BCA: "\<not> Bet B C A" and
    not_CAB: "\<not> Bet C A B"
    using H1 by blast

  show "\<exists> (A :: Point) . \<exists> (B :: Point). A \<noteq> B"
  proof (cases "A = B")

    assume Heq: "A = B"
    have BBC: "Bet B B C" by (rule bet_left [of B C])
    have not_BBC: "\<not> Bet B B C" using Heq not_ABC by (rule subst)

    then show ?thesis using BBC by contradiction
  next

    assume Hneq: "A \<noteq> B"
    have H1: "\<exists> (B :: Point). A \<noteq> B" using Hneq by (rule exI [of _ B])
    show "\<exists> (A :: Point). \<exists> (B :: Point). A \<noteq> B" using H1 by (rule exI [of _ A])
  qed
qed

lemma point_construction_different:
  fixes A B :: Point
  shows "\<exists> C . Bet A B C \<and> B \<noteq> C"
proof -
  have H1: "\<exists> (A :: Point) . \<exists> (B :: Point). A \<noteq> B" by (rule two_distinct_points)
  obtain C D :: Point where
    C_neq_D: "C \<noteq> D"
    using H1 by blast

  have H2: "\<exists> E. Bet A B E \<and> Congr B E C D" by (rule segment_construction [of A B C D])
  obtain E :: Point where
    H3: "Bet A B E" and
    H4: "Congr B E C D"
    using H2 by blast

  have B_ne_E: "B \<noteq> E"
  proof
    assume B_eq_E: "B = E"

    have H5: "Congr E E C D" using B_eq_E H4 by (rule subst)
    have H6: "Congr C D E E" by (rule congr_sym [OF H5])
    have C_eq_D: "C = D" using H6 by (rule congr_id)
    from C_neq_D C_eq_D show False
      by (rule notE)
  qed

  have Conj: "Bet A B E \<and> B \<noteq> E" by (rule conjI [OF H3 B_ne_E])
  show "\<exists> C . Bet A B C \<and> B \<noteq> C" using Conj by (rule exI [of _ E])
qed

lemma CBA_ACD_BCD:
  "Bet C B A \<Longrightarrow> Bet A C D \<Longrightarrow> Bet B C D"
proof -
  assume H1: "Bet C B A"
  assume H2: "Bet A C D"

  have L1 : "Bet D C A"
    using H2 by (rule bet_sym)

  have L2 : "\<exists>X. Bet B X D \<and> Bet C X C"
    using H1 L1 by (rule inner_pasch)

  obtain X where
    L3 : "Bet B X D \<and> Bet C X C"
    using L2 by (rule exE)

  have L4 : "Bet B X D"
    using L3 by (rule conjunct1)

  have L5 : "Bet C X C"
    using L3 by (rule conjunct2)

  have L6 : "C = X"
    using L5 by (rule bet_id)

  show Goal : "Bet B C D"
    using L6 L4 by (rule ssubst)
qed

lemma bet_unique_middle:
  "Bet A B C \<Longrightarrow> Bet A C B \<Longrightarrow> B = C"
proof -
  assume H1: "Bet A B C"
  assume H2: "Bet A C B"

  have L1: "Bet C B A"
    using H1 by (rule bet_sym)

 have L2: "Bet B C A"
   using H2 by (rule bet_sym)

   obtain X where
    L3: "Bet B X B" and
    L4: "Bet C X C"
     using inner_pasch[OF L1 L2] by metis

  have L5: "B = X"
    using bet_id [OF L3] by this

  have L6: "C = X"
    using bet_id [OF L4] by this

  show Goal: "B = C" using L5 L6 by metis

qed

lemma ABD_BCD_ABC:
  "Bet A B D \<Longrightarrow> Bet B C D \<Longrightarrow> Bet A B C"
proof -
  assume H1: "Bet A B D"
  assume H2: "Bet B C D"

  have L1: "Bet D B A"
    using H1 by (rule bet_sym)

  have L2: "Bet C B A"
    using H2 L1 by (rule CBA_ACD_BCD)

  show Goal: "Bet A B C" using L2 by (rule bet_sym)
qed

lemma construction_uniqueness:
  "Q \<noteq> A \<Longrightarrow> Bet Q A X \<Longrightarrow>  Congr A X B C \<Longrightarrow> Bet Q A Y \<Longrightarrow> Congr A Y B C \<Longrightarrow> X = Y"
proof -
  assume H1: "Q \<noteq> A"
  assume H2: "Bet Q A X"
  assume H3: "Congr A X B C"
  assume H4: "Bet Q A Y"
  assume H5: "Congr A Y B C"

  have L1: "Congr B C A Y"
    using H5 by (rule congr_sym)

  have L2: "Congr A X A Y" by (rule congr_trans [OF H3 L1])

  have L3: "Congr Q A Q A"
    by (rule congr_refl)

  have L4: "Congr Q Y Q Y"
    by (rule congr_refl)

  have L5: "Congr A Y A Y"
    by (rule congr_refl)

  have L7: "Congr X Y Y Y"
    using L3 L2 L4 L5 H2 H4 H1
      by (rule five_segment)

  show "X = Y"
    using L7 by (rule congr_id)
qed

lemma outer_transitivity_between2:
  "Bet A B C \<Longrightarrow> Bet B C D \<Longrightarrow> B \<noteq> C \<Longrightarrow> Bet A C D"
proof -
  assume H1: "Bet A B C"
  assume H2: "Bet B C D"
  assume H3: "B \<noteq> C"

  obtain X where
    L1: "Bet A C X" and
    L2: "Congr C X C D"
     using segment_construction by blast

  have L3: "Congr C D C X" by (rule congr_sym [OF L2])

  have L4: "Bet C B A" by (rule bet_sym [OF H1])
  have L5: "Bet B C X" by (rule CBA_ACD_BCD [OF L4 L1])

  have L6: "Congr C X C X" by (rule congr_refl [of C X])

  have L7: "D = X"
    using H3 H2 L3 L5 L6 by (rule construction_uniqueness)

  show Goal: "Bet A C D"
    using L7 L1 by (rule ssubst)
qed

lemma ABD_BCD_ACD:
  fixes A B C D :: Point
  shows "Bet A B D \<Longrightarrow> Bet B C D \<Longrightarrow> Bet A C D"
proof -
  assume H1: "Bet A B D"
  assume H2: "Bet B C D"

  show "Bet A C D"
  proof (cases "B = C")

    assume L1: "B = C"

    show "Bet A C D"
      using L1 H1
      by (rule subst)

  next

    assume L1: "B \<noteq> C"

    have L2 : "Bet D B A" by (rule bet_sym [OF H1])

    have L3 : "Bet C B A" by (rule CBA_ACD_BCD [OF H2 L2])

    have L4: "Bet A B C" by (rule bet_sym [OF L3])

    show L5: "Bet A C D"
      using L4 H2 L1 by (rule outer_transitivity_between2)

  qed
qed

lemma bet_outer_trans:
  "Bet A B C \<Longrightarrow> Bet B C D \<Longrightarrow> B \<noteq> C \<Longrightarrow> Bet A B D"
proof -
  assume H1: "Bet A B C"
  assume H2: "Bet B C D"
  assume H3: "B \<noteq> C"

  have L1: "Bet A C D"
    using H1 H2 H3 by (rule outer_transitivity_between2)

  have L2: "Bet C B A" by (rule bet_sym [OF H1])

  have L3: "Bet D C B" by (rule bet_sym [OF H2])

  have L4: "Bet D C A" by (rule bet_sym [OF L1])

  have L5: "C \<noteq> B" by (rule not_sym [OF H3])

  have L6: "Bet D B A"
    using L3 L2 L5 by (rule outer_transitivity_between2)

  show Goal: "Bet A B D"
    using L6 by (rule bet_sym)
qed

lemma ACD_ABC_ABD:
  "Bet A C D \<Longrightarrow> Bet A B C \<Longrightarrow> Bet A B D"
proof -
  assume H1: "Bet A B C"
  assume H2: "Bet A C D"

  have L1: "Bet C B A" by (rule bet_sym [OF H1])
  have L2: "Bet B C D" by (rule CBA_ACD_BCD [OF L1 H2])

  show "Bet A B D"
  proof (cases "B = C")

    assume L3: "B = C"

    show Goal: "Bet A B D"
      using H2 L3
      by (subst L3)

  next

    assume L3: "B \<noteq> C"

    show Goal: "Bet A B D"
      using H1 L2 L3
      by (rule bet_outer_trans)

  qed
qed

lemma not_bet_sym:
  fixes A B C :: Point
  shows "\<not> Bet A B C \<Longrightarrow> \<not> Bet C B A"
proof -

  assume H1: "\<not> Bet A B C"
  show "\<not> Bet C B A"
  proof
    assume Contra: "Bet C B A"

    have H2: "Bet A B C" by (rule bet_sym [OF Contra])
    show False
        using H1 H2
        by (rule notE)
  qed
qed

lemma contra_inner_trans:
  "Bet A B D \<Longrightarrow> \<not> Bet A B C \<Longrightarrow> \<not> Bet B C D"
proof -
  assume H1: "Bet A B D"
  assume H2: "\<not> Bet A B C"

  have H3: "Bet B C D \<Longrightarrow> Bet A B C" by (rule ABD_BCD_ABC [OF H1])

  show Goal: "\<not> Bet B C D"
    by (rule contrapos_nn [OF H2 H3])
qed

lemma not_bet_not_eq:
  "\<not> Bet A B C \<Longrightarrow> B \<noteq> C"
proof -
  assume H1: "\<not> Bet A B C"
  show "B \<noteq> C"
  proof
    assume Heq: "B = C"

    have H2: "\<not> Bet A C C" 
      using Heq H1 by (rule subst)

    have H3: "Bet A C C" by (rule bet_right [of A C])

    show False
        using H2 H3
        by (rule notE)
  qed
qed

lemma bet_id_neq1 : "Bet A B C \<Longrightarrow> A \<noteq> B \<Longrightarrow> A \<noteq> C"
proof -
  assume H1 :  "Bet A B C"
  assume H2 : "A \<noteq> B"
  show "A \<noteq> C"
  proof
    assume H3 : "A = C"
    
    have L1 : "Bet A B A" using H3 H1 by (rule ssubst)
    have L2 : "A = B" using L1 by (rule bet_id)
    show "False" using H2 L2 by (rule notE)
  qed
qed

lemma bet_id_neq2 : "Bet A B C \<Longrightarrow> B \<noteq> C \<Longrightarrow> A \<noteq> C"
proof -
  assume H1 :  "Bet A B C"
  assume H2 : "B \<noteq> C"
  show "A \<noteq> C"
  proof
    assume H3 : "A = C"
    
    have L1 : "Bet C B C" using H3 H1 by (rule subst)
    have L2 : "C = B" using L1 by (rule bet_id)
    have L3 : "B = C" using L2 by (rule sym)
    show "False" using H2 L3 by (rule notE)
  qed
qed

end 
