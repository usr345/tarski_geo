theory Bet
  imports Axioms
begin


lemma congr_refl:
  fixes A B :: Point
  shows "Congr A B A B"
proof -

  have L1: "Congr B A A B"  by (rule congr_pseudo_refl [of B A])

  show "Congr A B A B" using L1 L1  by (rule congr_inner_transitivity)
qed

lemma congr_reverse:
  fixes A B C D :: Point
  shows "Congr A B C D \<Longrightarrow> Congr C D A B"
proof -
  assume H: "Congr A B C D"

  have L1: "Congr A B A B"  by (rule congr_refl [of A B])
  show "Congr C D A B"  by (rule congr_inner_transitivity [OF H L1])
qed

lemma congr_reverse_id:
  fixes A B C D :: Point
  shows "Congr A A C D \<Longrightarrow> C = D"
proof -
   assume H: "Congr A A C D"

  have L1: "Congr C D A A"  by (rule congr_reverse [OF H])
  show "C = D" by (rule congr_id [OF L1])
qed

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

lemma CBA_BCD:
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

lemma bet_inner_trans:
  "Bet A B D \<Longrightarrow> Bet B C D \<Longrightarrow> Bet A B C"
proof -
  assume H1: "Bet A B D"
  assume H2: "Bet B C D"

  have L1: "Bet D B A"
    using H1 by (rule bet_sym)

  have L2: "Bet C B A"
    using H2 L1 by (rule CBA_BCD)

  show Goal: "Bet A B C" using L2 by (rule bet_sym)
qed

lemma bet_exchange3:
  "Bet A B C \<Longrightarrow> Bet A C D \<Longrightarrow> Bet B C D"
proof -
  assume H1: "Bet A B C"
  assume H2: "Bet A C D"

  have L1: "Bet D C A"
    using H2 by (rule bet_sym)

  have L2: "Bet C B A"
    using H1 by (rule bet_sym)

  have construction:"\<exists>X. Bet C X C \<and> Bet B X D"
    using L1 L2 by (rule inner_pasch)

 obtain X where
    L3: "Bet C X C" and
    L4: "Bet B X D"
   using construction by metis

  have L5: "C = X"
    using L3 by (rule bet_id)

  show Goal: "Bet B C D"
    using L5 L4 by (rule ssubst)
qed

lemma construction_uniqueness:
  "Q \<noteq> A \<Longrightarrow> Bet Q A X \<Longrightarrow>  Congr A X B C \<Longrightarrow> Bet Q A Y \<Longrightarrow> Congr A Y B C \<Longrightarrow> X = Y"
proof -
  assume H1: "Q \<noteq> A"
  assume H2: "Bet Q A X"
  assume H3: "Congr A X B C"
  assume H4: "Bet Q A Y"
  assume H5: "Congr A Y B C"

  have L1: "Congr B C A X"
    using H3 by (rule congr_reverse)

  have L2: "Congr B C A Y"
    using H5 by (rule congr_reverse)

  have L3: "Congr A X A Y"
    using L1 L2 by (rule congr_inner_transitivity)

  have L4: "Congr Q A Q A"
    by (rule congr_refl)

  have L5: "Congr Q Y Q Y"
    by (rule congr_refl)

  have L6: "Congr A Y A Y"
    by (rule congr_refl)

  have L7: "Congr X Y Y Y"
    using L4 L3 L5 L6 H2 H4 H1
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

  have L3: "Congr C D C X" by (rule congr_reverse [OF L2])

  have L4: "Bet B C X" by (rule bet_exchange3 [OF H1 L1])

  have L5: "Congr C X C X" by (rule congr_refl [of C X])

  have L6: "D = X"
    using H3 H2 L3 L4 L5 by (rule construction_uniqueness)

  show Goal: "Bet A C D"
    using L6 L1 by (rule ssubst)
qed

lemma between_exchange2:
  "Bet A B D \<Longrightarrow> Bet B C D \<Longrightarrow> Bet A C D"
proof -
  assume H1: "Bet A B D"
  assume H2: "Bet B C D"

  show "Bet A C D"
  proof (cases "B = C")

    assume L1: "B = C"

    show L2: "Bet A C D"
      using L1 H1
      by (rule subst)

  next

    assume L1: "B \<noteq> C"

    have L2 : "Bet D B A" by (rule bet_sym [OF H1])

    have L3 : "Bet C B A" by (rule CBA_BCD [OF H2 L2])

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

lemma bet_concat:
  "Bet A B C \<Longrightarrow> Bet A C D \<Longrightarrow> Bet A B D"
proof -
  assume H1: "Bet A B C"
  assume H2: "Bet A C D"

  have L1: "Bet B C D"
    using H1 H2
    by (rule bet_exchange3)

  show "Bet A B D"
  proof (cases "B = C")

    assume L2: "B = C"

    show Goal: "Bet A B D"
      using H2 L2
      by (subst L2)

  next

    assume L2: "B \<noteq> C"

    show Goal: "Bet A B D"
      using H1 L1 L2
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

lemma not_bet_BCD:
  "Bet A B D \<Longrightarrow> \<not> Bet A B C \<Longrightarrow> \<not> Bet B C D"

lemma not_bet_ABC:
  "Bet A B D \<Longrightarrow> \<not> Bet B C D \<Longrightarrow> \<not> Bet A B C"

lemma not_bet_BCD':
  "Bet A B D \<Longrightarrow> \<not> Bet A C D \<Longrightarrow> \<not> Bet B C D"

lemma not_bet_BCD_of_not_ABD:
  "Bet A B C \<Longrightarrow> B \<noteq> C \<Longrightarrow> \<not> Bet A B D \<Longrightarrow> \<not> Bet B C D"

lemma not_bet_ABC:
  "Bet A C D \<Longrightarrow> \<not> Bet A B D \<Longrightarrow> \<not> Bet A B C"

lemma not_bet_ACD:
  "Bet A B C \<Longrightarrow> \<not> Bet A B D \<Longrightarrow> \<not> Bet A C D"


lemma bet_inner_conn:
  "Bet A B D \<Longrightarrow> Bet A C D \<Longrightarrow> Bet A B C \<or> Bet A C B"
proof -
  assume H1: "Bet A B D"
  assume H2: "Bet A C D"

  show "Bet A B C \<or> Bet A C B"
  proof (cases "B = C")

    assume Heq: "B = C"

    have L2: "Bet A B B" by (rule bet_right)
    have L3: "Bet A B C"
      using Heq L2 by (rule subst)

    show Goal: "Bet A B C \<or> Bet A C B"
      using L3 by (rule disjI1)
  next
    assume Hneq: "B \<noteq> C"

end