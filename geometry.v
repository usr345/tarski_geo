Require Import TarskiGeo.axioms.
Require Import TarskiGeo.congr.
Require Import TarskiGeo.between.

Import TarskiAxioms.

(* Три точки лежат на одной прямой, если одна из них лежит между двумя другими. *)
Definition Collinear (A B C : Point) : Prop :=
  Between A B C
  \/ Between A C B
  \/ Between B A C.

(* Определение принадлежности точки P окружности с центром O и радиусом OA *)
Definition OnCircle (O A P : Point) : Prop :=
  Congr O P O A.

(* Точка, задающая радиус, всегда лежит на своей окружности. *)
Definition on_circle_trivial : forall O A : Point, OnCircle O A A :=
  fun O A : Point =>
    let Goal : Congr O A O A := congr_refl O A in
    Goal.

Definition on_circle_sym : forall O A P : Point, OnCircle O A P -> OnCircle O P A :=
  fun (O A P : Point) (H : OnCircle O A P) =>
    let H1 : Congr O P O A := H in
    let Goal : Congr O A O P := congr_symm H1 in
    Goal.

(* Задача 6. Транзитивность окружностей (равенство радиусов). *)
(* Если P лежит на окружности (O, A), а Q лежит на окружности (O, P),
   то Q лежит на исходной окружности (O, A). *)
Definition on_circle_trans : forall O A P Q : Point,
    OnCircle O A P -> OnCircle O P Q -> OnCircle O A Q :=
  fun (O A P Q : Point) (H1 : OnCircle O A P) (H2 : OnCircle O P Q) =>
    let H3 : Congr O P O A := H1 in
    let H4 : Congr O Q O P := H2 in
    let Goal : Congr O Q O A :=
      let H5 : Congr O P O Q := congr_symm H4 in
      congr_inner_trans H5 H3
    in Goal.

(* Задача 8. Откладывание отрезка от точки (Евклид I.2). *)
(* Докажи, что от любой точки X можно отложить отрезок, конгруэнтный CD. *)
(* Подсказка: используй segment_construction с вырожденным лучом,
   передав X в качестве первых двух аргументов. Тебе потребуется
   деструктурировать экзистенциальный тип (ex) и конъюнкцию (and). *)
Definition copy_segment : forall X A B : Point,
  exists E : Point, Congr X E A B :=
  fun X A B : Point =>
    let H1 : exists E : Point, Between A X E /\ Congr X E A B := segment_construction A X A B in
    match H1 with
    | ex_intro _ E (conj _ Hcongr) =>
        ex_intro (fun y : Point => Congr X y A B) E Hcongr
    end.

(* Постулат пересечения базовых окружностей (заменяет Аксиому непрерывности) *)
Axiom equilateral_triangle_postulate : forall A B : Point,
    exists C : Point, OnCircle A B C /\ OnCircle B A C.

(* Задача 9. Предложение 1. Книга I "Начал" Евклида. *)
(* На заданном отрезке AB построить равносторонний треугольник. *)
(* Обрати внимание на типы: постулат дает тебе OnCircle,
   что по определению разворачивается в Congr A C A B и Congr B C B A.
   А доказать нужно Congr A B A C и Congr A B B C.
   Тебе придется применить твои леммы симметрии и коммутативности
   внутри конструктора экзистенциального типа. *)
Definition euclid_prop_1 : forall A B : Point,
  exists C : Point, Congr A B A C /\ Congr B A B C :=
  fun A B : Point =>
    let H1 : exists C : Point, OnCircle A B C /\ OnCircle B A C := equilateral_triangle_postulate A B in
    let H2 : exists C : Point, Congr A C A B /\ Congr B C B A := H1 in
    match H2 with
    | ex_intro _ C (conj AC_eq_AB BC_eq_BA) =>
        let AB_eq_AC : Congr A B A C := congr_symm AC_eq_AB in
        let BA_eq_BC : Congr B A B C := congr_symm BC_eq_BA in
        ex_intro (fun x : Point => Congr A B A x /\ Congr B A B x) C (conj AB_eq_AC BA_eq_BC)
     end.



Definition extend_segment_same_length : forall A B : Point,
  exists C : Point, Between A B C /\ Congr B C A B :=
  fun A B : Point =>
    segment_construction A B A B.

(* Задача 5. Сложение отрезков (Segment Addition).
   Это твоя первая встреча с five_segment.
   Если AB ≡ A'B' и BC ≡ B'C' на прямых, то AC ≡ A'C'. *)
Definition segment_addition : forall A B C A' B' C' : Point,
    A <> B ->
    Between A B C -> Between A' B' C' ->
    Congr A B A' B' -> Congr B C B' C' ->
    Congr A C A' C' :=
  fun A B C A' B' C' Hneq Hbet Hbet' HcongAB HcongBC =>
    let H1 : Congr A A A' A' -> Congr B A B' A' -> Congr C A C' A' := five_segment A B C A A' B' C' A' Hneq Hbet Hbet' HcongAB HcongBC in
    let H2 : Congr A A A' A' := congr_trivial_identity A A' in
    let H3 : Congr B A B' A' := congr_reverse HcongAB in
    let H4 : Congr C A C' A' := H1 H2 H3 in
    let H5 : Congr A C A' C' := congr_reverse H4 in
    H5.

(* Задача 12. Определение луча.
   Точка P лежит на луче с началом в A, проходящем через B (A <> B).
   В системе Тарского Between нестрогое (допускает совпадения).
   Поэтому P лежит на луче AB, если либо P находится на отрезке AB,
   либо B находится на отрезке AP. *)
Definition IsOnRay (A B P : Point) : Prop :=
    Between A P B
  \/
    Between A B P.

(* Задача 14. Определение середины отрезка.
   Точка M является серединой отрезка AB, если она лежит на отрезке AB
   и расстояние от A до M равно расстоянию от M до B. *)
Definition Midpoint (A M B : Point) : Prop :=
  Between A M B /\ Congr A M M B.

(* Задача 15. Симметрия середины отрезка.
   Докажи конструированием терма, что если M — середина AB, то M — середина BA.
   Тебе потребуются уже доказанные леммы между (between_symm)
   и конгруэнтности (congr_symm, congr_left_comm или congr_right_comm). *)
Definition midpoint_symm : forall M A B : Point,
    Midpoint A M B -> Midpoint B M A :=
  fun (M A B : Point) (H : Midpoint A M B) =>
    let H1 : Between A M B /\ Congr A M M B := H in
    let Goal : Midpoint B M A :=
      let Goal1 : Between B M A /\ Congr B M M A :=
        match H1 with
        | conj B1 H2 =>
            let B2 : Between B M A := between_symm B1 in
            let H3 : Congr M B A M := congr_symm H2 in
            let H4 : Congr B M M A := congr_reverse H3 in
            conj B2 H4
        end
      in Goal1
    in Goal.

(* Предикат корректного угла с вершиной в B *)
Definition ValidAngle (A B C : Point) : Prop :=
  A <> B /\ C <> B.

(* Задача 16. Определение прямого угла.
   Угол ABC с вершиной в B является прямым, если на прямой AB существует
   точка A' такая, что B является серединой отрезка AA', и AC ≡ A'C. *)
Definition RightAngle (A B C : Point) : Prop :=
  exists A' : Point, Midpoint A B A' /\ Congr A C A' C.

(* Равенство углов (CongAngle A B C D E F) означает, что угол ABC равен углу DEF. *)
Definition CongrAngle (A B C D E F : Point) : Prop :=
  ValidAngle A B C /\ ValidAngle D E F /\
    exists A' C' D' F' : Point,
      IsOnRay B A A' /\ A' <> B /\
      IsOnRay B C C' /\ C' <> B /\
      IsOnRay E D D' /\ D' <> E /\
      IsOnRay E F F' /\ F' <> E /\
      Congr B A' E D' /\
      Congr B C' E F' /\
      Congr A' C' D' F'.

(* Задача 17. Существование центрально-симметричной точки.
   Докажи, что любой отрезок AB можно продлить за точку B на его же длину.
   Подсказка: примени segment_construction A B A B. Тебе потребуется
   извлечь (Congr B E A B) и с помощью твоих лемм о симметрии
   превратить это в (Congr A B B E), чтобы удовлетворить предикату Midpoint. *)
Definition point_reflection : forall A B : Point,
  exists A' : Point, Midpoint A B A' :=
  fun A B : Point =>
    let Goal : exists A' : Point, Between A B A' /\ Congr A B B A' :=
      let H1 : exists A' : Point, Between A B A' /\ Congr B A' A B := segment_construction A B A B in
      match H1 with
      | ex_intro _ A' (conj B1 H2) =>
          let H3 : Congr A B B A' := congr_symm H2 in
          ex_intro (fun x : Point => Between A B x /\ Congr A B B x) A' (conj B1 H3)
      end
    in Goal.

(* Задача 18. Рефлексивность коллинеарности.
   Покажи, что любые две точки коллинеарны сами себе (A, A, B).
   Подсказка: используй bet_identity или просто тот факт,
   что Between A A B тривиально следует из определения отрезка/луча,
   но здесь проще доказать через конструирование (or_introl / or_intror).
   Вспомни, что Collinear X Y Z определено через три \/ (OR). *)
Definition collinear_trivial : forall A B : Point, Collinear A A B :=
  fun A B : Point =>
    let Goal : Between A A B \/ (Between A B A \/ Between A A B) :=
      let H1 : Between B A A := between_trivial_right B A in
      let H2 : Between A A B := between_symm H1 in
      let H3 : Between A A B \/ (Between A B A \/ Between A A B) := or_introl H2 in
      H3
    in Goal.

(* Задача 19. Симметрия прямого угла *)
Definition right_angle_symm : forall A B C : Point,
  RightAngle A B C -> RightAngle C B A :=
  (* Подсказка: здесь потребуется Пятиотрезочная аксиома,
     чтобы доказать равенство диагоналей в прямоугольнике *)


(*
Отрезок $AB$ меньше $CD$, если на $CD$ можно отложить часть, конгруэнтную $AB$.
*)
Definition SegmentLt (A B C D : Point) : Prop :=
  exists E : Point, Between C E D /\ C <> E /\ E <> D /\ Congr A B C E.

End TarskiGeometry.
