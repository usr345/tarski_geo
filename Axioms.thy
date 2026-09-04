theory Axioms
  imports Main
begin

typedecl Point

consts
  Bet  :: "Point \<Rightarrow> Point \<Rightarrow> Point \<Rightarrow> bool"
  Congr :: "Point \<Rightarrow> Point \<Rightarrow> Point \<Rightarrow> Point \<Rightarrow> bool"


(************************************************************)
(* A1. Congruence pseudo-reflexivity                       *)
(************************************************************)

axiomatization where
  congr_pseudo_refl:
    "\<And>A B. Congr A B B A"


(************************************************************)
(* A2. Inner transitivity of congruence                    *)
(************************************************************)

axiomatization where
  congr_inner_transitivity:
    "\<And>A B C D E F.
       Congr A B C D \<Longrightarrow>
       Congr A B E F \<Longrightarrow>
       Congr C D E F"


(************************************************************)
(* A3. Identity of congruence                              *)
(************************************************************)

axiomatization where
  congr_id:
    "\<And>A B C.
       Congr A B C C \<Longrightarrow>
       A = B"

(************************************************************)
(* A4. Identity of betweenness                              *)
(************************************************************)

axiomatization where
  bet_id:
    "\<And>A B.
       Bet A B A \<Longrightarrow>
       A = B"


(************************************************************)
(* A5. Inner Pasch                                         *)
(************************************************************)

axiomatization where
  inner_pasch:
    "\<And>A B C P Q.
       Bet A P C \<Longrightarrow>
       Bet B Q C \<Longrightarrow>
       \<exists>X.
         Bet P X B \<and>
         Bet Q X A"

(************************************************************)
(* A6. Five segment axiom                                  *)
(************************************************************)

axiomatization where
  five_segment:
    "\<And>A A' B B' C C' D D'.
       Congr A B A' B' \<Longrightarrow>
       Congr B C B' C' \<Longrightarrow>
       Congr A D A' D' \<Longrightarrow>
       Congr B D B' D' \<Longrightarrow>
       Bet A B C \<Longrightarrow>
       Bet A' B' C' \<Longrightarrow>
       A \<noteq> B \<Longrightarrow>
       Congr C D C' D'"

(************************************************************)
(* A7. Lower dimension                                    *)
(************************************************************)

axiomatization where
  lower_dim:
    "\<exists>A B C.
       \<not> Bet A B C \<and>
       \<not> Bet B C A \<and>
       \<not> Bet C A B"


(************************************************************)
(* A8. Upper dimension                                    *)
(************************************************************)

axiomatization where
  upper_dim:
    "\<And>A B C P Q.
       P \<noteq> Q \<Longrightarrow>
       Congr A P A Q \<Longrightarrow>
       Congr B P B Q \<Longrightarrow>
       Congr C P C Q \<Longrightarrow>
       Bet A B C \<or>
       Bet B C A \<or>
       Bet C A B"


(************************************************************)
(* A9. Dedekind continuity                               *)
(************************************************************)

axiomatization where
  continuity:
    "\<And>Xi Upsilon.
       (\<exists>A.
          \<forall>X Y.
            Xi X \<longrightarrow>
            Upsilon Y \<longrightarrow>
            Bet A X Y)
       \<Longrightarrow>
       (\<exists>B.
          \<forall>X Y.
            Xi X \<longrightarrow>
            Upsilon Y \<longrightarrow>
            Bet X B Y)"

(************************************************************)
(* A10. Segment construction                                *)
(************************************************************)

axiomatization where
  segment_construction:
    "\<And>A B C D.
       \<exists>E.
         Bet A B E \<and>
         Congr B E C D"

end