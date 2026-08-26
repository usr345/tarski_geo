Require Import TarskiGeo.axioms.

Import TarskiAxioms.

Definition between_trivial_right : forall A B : Point, Between A B B :=
  fun (A B : Point) =>
    let H1 : exists C : Point, Between A B C /\ Congr B C B B := segment_construction A B B B in
    match H1 with
    | ex_intro _ C (conj B1 H2) =>
        let H3 : B = C := congr_identity H2 in
        let H4 : C = B := eq_sym H3 in
        let H5 : Between A B B :=
          (match H4 in eq _ X return Between A B X with
          | @eq_refl _ _ => B1
          end)
        in
        H5
    end.

Definition between_symm : forall {A B C : Point}, Between A B C -> Between C B A :=
  fun (A B C : Point) (H : Between A B C) =>
    let H1 : Between B C C := between_trivial_right B C in
    let H2 : exists X : Point, Between B X B /\ Between C X A :=
      @pasch A B C B C H H1 in
    match H2 with
    | ex_intro _ X (conj Hbxb Hcxa) =>
        let H3 : B = X := bet_identity Hbxb in
        let H4 : X = B := eq_sym H3 in
        let H5 : Between C B A :=
          match H4 in eq _ B return Between C B A with
          | @eq_refl _ _ => Hcxa
          end
        in
        H5
    end.

Definition between_trivial_left : forall A B : Point, Between A A B :=
  fun A B : Point =>
    let H1 : Between B A A := between_trivial_right B A in
    let H2 : Between A A B := between_symm H1 in
    H2.

Definition between_inner_trans : forall {A B C D : Point},
  Between A B D -> Between B C D ->
  Between A B C :=
  fun (A B C D : Point) (Habd : Between A B D) (Hbcd : Between B C D) =>
    let H1 : Between A B D -> Between B C D -> exists X : Point, Between B X B /\ Between C X A := @pasch A B D B C in
    let H2 : exists X : Point, Between B X B /\ Between C X A := H1 Habd Hbcd in
    match H2 with
    | ex_intro _ X (conj Hbxb Hcxa) =>
        let H3 : B = X := bet_identity Hbxb in
        let H4 : X = B := eq_sym H3 in
        let H5 : Between C B A :=
          match H4 in eq _ B return Between C B A with
          | @eq_refl _ _ => Hcxa
          end
        in
        let Habc : Between A B C := between_symm H5 in
        Habc
    end.

Definition bet_unique_middle :
  forall A B C : Point, Between A B C -> Between A C B -> B = C :=
  fun (A B C : Point) (Habc : Between A B C) (Hacb : Between A C B) =>
    let H1 : (Between C B A) -> (Between B C A) -> exists X : Point, Between B X B /\ Between C X C := @pasch C B A B C in
    let Hcba : Between C B A := between_symm Habc in
    let Hbca : Between B C A := between_symm Hacb in
    let H2 : exists X : Point, Between B X B /\ Between C X C := H1 Hcba Hbca in
    match H2 with
    | ex_intro _ X (conj H3 H4) =>
        let H5 : B = X := bet_identity H3 in
        let H6 : C = X := bet_identity H4 in
        let H7 : X = C := eq_sym H6 in
        let H8 : B = C := eq_trans H5 H7 in
        H8
    end.

Definition bet_CBA : forall {A B C D : Point}, Between C B A -> Between A C D -> Between B C D :=
  fun (A B C D : Point) (Hcba : Between C B A) (Hacd : Between A C D) =>
    let H1 : Between C B A -> Between D C A -> exists X : Point, Between B X D /\ Between C X C := @pasch C D A B C in
    let H2 : Between D C A := between_symm Hacd in
    let H3 : exists X : Point, Between B X D /\ Between C X C := H1 Hcba H2 in
    match H3 with
    | ex_intro _ X Hconj =>
        match Hconj with
        | conj H4 H5 =>
            let Heq : C = X := bet_identity H5 in
            let H6 : X = C := eq_sym Heq in
            match H6 in eq _ C return Between B C D with
            | @eq_refl _ _ => H4
            end
        end
    end.

Definition between_concat : forall {A B C D : Point},
    Between A B C -> Between A C D -> Between A B D :=
  fun (A B C D : Point) (Habc : Between A B C) (Hacd : Between A C D) =>
    let Hcba : Between C B A := between_symm Habc in
    let Hbcd : Between B C D := bet_CBA Hcba Hacd in
    let Pas1 : exists X : Point, Between C X B /\ Between C X A := @pasch A B D C C Hacd Hbcd in
    match Pas1 with
    | ex_intro _ X (conj Hcxb Hcxa) =>
        let Hxcd : Between X C D := bet_CBA Hcxb Hbcd in
        let Hbxc : Between B X C := between_symm Hcxb in
        let Hxba : Between X B A := bet_CBA Hbxc Hcba in
        let Habx : Between A B X := between_symm Hxba in
        let Haxc : Between A X C := between_symm Hcxa in
        let Pas2 : exists Y : Point, Between X Y B /\ Between X Y A:= @pasch A B C X X Haxc Hbxc in
        match Pas2 with
        | ex_intro _ Y (conj Hxyb Hxya) =>
            let Hyxc : Between Y X C := bet_CBA Hxya Haxc in
            let Hbyx : Between B Y X := between_symm Hxyb in
            let Hyba : Between Y B A := bet_CBA Hbyx Hxba in
            _
        end
    end.

Definition between_outer_trans : forall {A B C D : Point},
    Between A B C -> Between B C D -> B <> C -> Between A B D :=


(* Внешняя транзитивность *)
Definition between_outer_trans2 : forall A B C D : Point,
  Between A B C -> Between B C D -> B <> C -> Between A C D :=
