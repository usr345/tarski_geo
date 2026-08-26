Module TarskiAxioms.
Parameter Point : Type.

(*
Лежать между — тернарное отношение (B x y z), означающее, что у «лежит между» х и z. Другими словами, что y является точкой на отрезке хz. (При этом концы включаются, то есть, как будет следовать из аксиом, B x x z — истинно).
*)
Parameter Between : Point -> Point -> Point -> Prop.

(*
Конгруэнтность — тетрадное отношение wx ≡ yz, означающее, что отрезок wx конгруэнтен отрезку yz; другими словами, что длина wx равна длине yz.
*)
Parameter Congr : Point -> Point -> Point -> Point -> Prop.

(* 3. Базовые аксиомы конгруэнтности *)

Axiom congr_pseudo_refl : forall A B : Point, Congr A B B A.

Axiom congr_inner_trans : forall {A B C D E F: Point},
    Congr A B C D -> Congr A B E F -> Congr C D E F.

Axiom congr_identity : forall {A B C : Point}, Congr A B C C -> A = B.

(* 4. Базовые аксиомы отношения "лежать между" *)

(* Аксиома тождества для Betweenness:
   Если B лежит между A и A, то B совпадает с A. *)
Axiom bet_identity : forall {A B : Point},
    Between A B A -> A = B.

(* Аксиома Паша (Pasch's axiom) - фундаментальная аксиома для двумерной геометрии.
   Она формализует идею о том, что прямая, пересекающая одну сторону треугольника,
   должна пересечь и другую (записано через точки). *)
Axiom pasch : forall {A B C P Q : Point},
    Between A P C -> Between B Q C ->
    exists X : Point, Between P X B /\ Between Q X A.

(* Аксиома непрерывности, сформулированная в логике второго порядка *)
Axiom continuity :
  forall (P Q : Point -> Prop),
    (exists a : Point, forall x y : Point,
       (P x /\ Q y) -> Between a x y) ->
    (exists b : Point, forall x y : Point,
       (P x /\ Q y) -> Between x b y).

(* Существуют 3 неколлинеарные точки *)
Axiom lower_dim :
  exists A B C : Point,
    ~ Between A B C /\
    ~ Between B C A /\
    ~ Between C A B.

(*
  Если для всех точек A, B, C - каждая из точек находится на одинаковом расстоянии от D и E, то A, B, C лежат на одной прямой
   D
  /|\
 / | \
A  |  B
 \ | /
  \|/
   E
 *)
Axiom dimension_top : forall {A B C D E : Point},
    D <> E ->
    Congr A D A E -> Congr B D B E -> Congr C D C E ->
    Between A B C
    \/ Between A C B
    \/ Between B A C.

Axiom five_segment : forall A B C D A' B' C' D': Point,
    A <> B -> (* Базис не должен быть вырожденным *)
    Between A B C -> Between A' B' C' -> (* Точки должны лежать на прямой *)
    Congr A B A' B' -> Congr B C B' C' ->
    Congr A D A' D' -> Congr B D B' D' ->
    Congr C D C' D'.

Axiom segment_construction : forall A B C D : Point,
  exists E : Point, Between A B E /\ Congr B E C D.

End TarskiAxioms.
