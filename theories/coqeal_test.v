From Coq Require Import Uint63.
From mathcomp Require Import all_ssreflect all_algebra.
From CoqEAL Require Import refinements hrel param.
(* Require Import misc. *)

Local Open Scope ring_scope.
Import Refinements Op.

(* From CoqEAL Require Import binrat.
From Bignums Require Import BigQ.

Section CoqEAL_binrat.

(* Goal (10 < 10^(3+3) :> rat) -> 10 < 1000^2 :> rat. 
Time by coqeal. (* 15s *)
Restart.
Time by vm_compute.
Abort. *)

Notation "[ x ]" := (bigQ2rat x).

Goal (10*10 < 100*100 :> rat) ==> (100 < 1000*100 :> rat).
by coqeal. (* 2.061s *)
Abort.

Goal ([10]*[10] < [100]*[100]) ==> ([100] < [1000]*[100]).
by coqeal. (*0.029s*)
Abort.

End CoqEAL_binrat. *)

(* Eval compute in (100000000 + 100000000)%Z. *)

From mathcomp Require Import ssrint.
From CoqEAL Require Import seqmx binint.
From Coq Require Import ZArith.

Section CoqEAL_matrix.

(* Tests From CoqEAL.seqmx.*)

Definition P := \matrix_(i,j < 100) (i + j)%:Z.
Definition Q := \matrix_(i,j < 100) (i + i + 2*j)%:Z.

Goal P == P.
Proof.
apply: refines_goal.
Abort.

(* Notation "[ x ]" := (bigQ2rat x).

Definition A := \matrix_(i,j < 100) [100000].
Definition B := \matrix_(i,j < 100) [200000].

Goal A + A == B.
Proof.
by coqeal.
Qed. *)

Goal 1000%:Z + 1000%:Z == 2000%:Z.
Proof.
coqeal.
Abort.

(* Definition P' := \matrix_(i,j < 2) (int_of_Z (1000 : BinInt.Z)%Z).
Definition Q' := \matrix_(i,j < 2) int_of_Z 2000.

Goal P' + P' == Q'.
Proof.
Set Typeclasses Debug.
Time by coqeal. (* 22.678s *) (*2nd trial : 73.386s*)
Abort. *)

End CoqEAL_matrix.

(* Section CoqEAL_rational.

From CoqEAL Require Import rational binint binnat.

Goal (10 < 10^(3+3) :> rat) -> (10 < 1000^2 :> rat). 
by coqeal. (* 15s *)
Restart.
Time by vm_compute.
Qed.

End CoqEAL_rational. *)
