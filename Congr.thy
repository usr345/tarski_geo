theory Congr
  imports Axioms
begin

lemma congr_refl:
  fixes A B :: Point
  shows "Congr A B A B"
proof -

  have L1: "Congr B A A B"  by (rule congr_pseudo_refl [of B A])
  show "Congr A B A B" using L1 L1  by (rule congr_inner_transitivity)
qed

lemma congr_sym:
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

  have L1: "Congr C D A A"  by (rule congr_sym [OF H])
  show "C = D" by (rule congr_id [OF L1])
qed

lemma congr_trans:
  fixes A B C D E F :: Point
  shows "Congr A B C D \<Longrightarrow> Congr C D E F \<Longrightarrow> Congr A B E F"
proof -
  assume H1: "Congr A B C D"
  assume H2: "Congr C D E F"

  have H3: "Congr C D A B" by (rule congr_sym [OF H1])
  show "Congr A B E F" by (rule congr_inner_transitivity [OF H3 H2])
qed

lemma congr_left_comm:
  fixes A B C D :: Point
  shows "Congr A B C D \<Longrightarrow> Congr B A C D"
proof -
  assume H1: "Congr A B C D"

  have H2: "Congr A B B A" by (rule  congr_pseudo_refl [of A B])
  show "Congr B A C D" by (rule congr_inner_transitivity [OF H2 H1])
qed

lemma congr_right_comm:
  fixes A B C D :: Point
  shows "Congr A B C D \<Longrightarrow> Congr A B D C"
proof -
  assume H1: "Congr A B C D"

  have H2: "Congr C D A B" by (rule congr_sym [OF H1])
  have H3: "Congr C D D C" by (rule  congr_pseudo_refl [of C D])

  show "Congr A B D C" by (rule congr_inner_transitivity [OF H2 H3])
qed

lemma congr_reverse:
  fixes A B C D :: Point
  shows "Congr A B C D \<Longrightarrow> Congr B A D C"
proof -
  assume H1: "Congr A B C D"

  have H2: "Congr B A C D" by (rule  congr_left_comm [OF H1])
  show "Congr B A D C" by (rule  congr_right_comm [OF H2])
qed

lemma congr_trivial_identity: 
  fixes A B :: Point
  shows "Congr A A B B"
proof -
  have H1: "\<exists>E. Bet A A E \<and> Congr A E B B" by (rule segment_construction [of A A B B])
  obtain E where
    H2: "Bet A A E" and
    H3: "Congr A E B B"
    using H1  by blast

  have H4: "A = E" by (rule congr_id [OF H3])
  show "Congr A A B B" using H4 H3 by (rule ssubst)
qed

lemma congr_neq:
  fixes A B "A'" "B'" :: Point
  shows "A \<noteq> B \<Longrightarrow> Congr A B A' B' \<Longrightarrow> A' \<noteq> B'"
proof -

  assume A_neq_B: "A \<noteq> B"
  assume AB_AB1: "Congr A B A' B'"

  show "A' \<noteq> B'"
  proof
    assume A1_eq_B1: "A' = B'"

    have AB_BB1: "Congr A B B' B'" using A1_eq_B1 AB_AB1 by (rule subst)
    have A_eq_B: "A = B" using AB_BB1 by (rule congr_id)

    show "False" using A_neq_B A_eq_B by (rule notE)
  qed
qed
end