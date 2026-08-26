Require Import TarskiGeo.axioms.

Import TarskiAxioms.

Definition congr_refl : forall A B : Point, Congr A B A B :=
  fun A B : Point =>
    let H1 : Congr B A A B := congr_pseudo_refl B A in
    let H2 : Congr B A A B -> Congr B A A B -> Congr A B A B := @congr_inner_trans B A A B A B in
    let H3 : Congr A B A B := H2 H1 H1 in
    H3.

Definition congr_symm : forall {A B C D : Point},
    Congr A B C D -> Congr C D A B :=
  fun (A B C D : Point) (H : Congr A B C D) =>
    let H1 : Congr A B A B := congr_refl A B in
    let H2 : Congr A B C D -> Congr A B A B -> Congr C D A B :=
      @congr_inner_trans A B C D A B in
    let H3 : Congr C D A B := H2 H H1 in
    H3.

Definition congr_right_comm : forall {A B C D : Point},
    Congr A B C D -> Congr A B D C :=
  fun (A B C D : Point) (H : Congr A B C D) =>
    let H1 : Congr C D A B := congr_symm H in
    let H2 : Congr C D D C := congr_pseudo_refl C D in
    let H3 : Congr A B D C := congr_inner_trans H1 H2 in
      H3.

(* Перестановка местами концов левого отрезка. *)
(* Если AB ≡ CD, то BA ≡ CD. *)
Definition congr_left_comm : forall {A B C D : Point},
    Congr A B C D -> Congr B A C D :=
  fun (A B C D : Point) (H : Congr A B C D) =>
    let H1 : Congr A B B A := congr_pseudo_refl A B in
    let H2 : Congr B A C D := congr_inner_trans H1 H
    in H2.

(* Если AB ≡ CD, то BA ≡ DC. *)
Definition congr_reverse : forall {A B C D : Point},
    Congr A B C D -> Congr B A D C :=
  fun (A B C D : Point) (H : Congr A B C D) =>
    let H1 : Congr B A C D := congr_left_comm H in
    let H2 : Congr B A D C := congr_right_comm H1 in
    H2.

(* Классическая "цепочечная" транзитивность. *)
Definition congr_trans : forall {A B C D E F : Point},
    Congr A B C D -> Congr C D E F -> Congr A B E F :=
  fun (A B C D E F : Point) (H1 : Congr A B C D) (H2 : Congr C D E F) =>
    let H3 : Congr C D A B := congr_symm H1 in
    let H4 : Congr A B E F := congr_inner_trans H3 H2 in
    H4.

Definition congr_trivial_identity : forall A B : Point, Congr A A B B :=
  fun A B : Point =>
    let H1 : exists E : Point, Between A A E /\ Congr A E B B := segment_construction A A B B in
    match H1 with
    | ex_intro _ E (conj _ Hcongr) =>
        let H2 : eq A E := congr_identity Hcongr in
        let H3 : Congr A E A E := congr_refl A E in
        let H4 : eq E A := eq_sym H2 in
        let H5 : Congr A A A E :=
          (match H4 in eq _ X return Congr A X A E with
          | @eq_refl _ _ => H3
          end)
        in
        let H6 : Congr A A B B := congr_trans H5 Hcongr in
        H6
    end.
