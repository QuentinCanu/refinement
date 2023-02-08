From Coq Require Import Uint63.
From mathcomp Require Import all_ssreflect all_algebra.
From CoqEAL Require Import refinements hrel param.
(* Require Import misc. *)

Local Open Scope ring_scope.
Import Refinements Op.

(* Section CoqEAL_alone.

Goal (10 < 10^(3+3) :> rat) -> (10 < 1000^2 :> rat).
Time by coqeal. (* 8s *)
Restart.
Time by vm_compute.
Qed.

End CoqEAL_alone.

Section CoqEAL_binrat.

From CoqEAL Require Import binrat.
From Bignums Require Import BigQ.

Goal (10 < 10^(3+3) :> rat) -> 10 < 1000^2 :> rat. 
Time by coqeal. (* 15s *)
Restart.
Time by vm_compute.
Qed.

Notation "[ x ]" := (bigQ2rat x).

Goal (10*10 < 100*100 :> rat) ==> (100 < 1000*100 :> rat).
by coqeal. (* 2.061s *)
Qed.

Goal ([10]*[10] < [100]*[100]) ==> ([100] < [1000]*[100]).
by apply: refines_goal. (*0.029s*)
Qed.

End CoqEAL_binrat.

Section CoqEAL_rational.

From CoqEAL Require Import rational binint binnat.

Goal (10 < 10^(3+3) :> rat) -> (10 < 1000^2 :> rat). 
by coqeal. (* 15s *)
Restart.
Time by vm_compute.
Qed.

End CoqEAL_rational. *)

Require Import int63.
Section RefineInt63.

Program Definition r_ord63int63 := fun_hrel int63_to_ord63.

Global Instance zero_int63 : zero_of int63 := 0%uint63.
Global Instance one_int63 : one_of int63 := 1%uint63.
Global Instance add_int63 : add_of int63 := Uint63.add.
Global Instance eq_int63 : eq_of int63 := Uint63.eqb.

Global Instance refine_ord63int63_zero: refines r_ord63int63 ord0 0%C.
Proof. by rewrite refinesE /r_ord63int63 /fun_hrel ord63_0P. Qed.

Global Instance refine_ord63int63_one: refines r_ord63int63 ord63_1 1%C.
Proof. by rewrite refinesE /r_ord63int63 /fun_hrel ord63_1P. Qed.

Global Instance refine_ord63int63_add: 
  refines (r_ord63int63 ==> r_ord63int63 ==> r_ord63int63)%rel ord63_add +%C.
Proof. 
rewrite refinesE /r_ord63int63 /fun_hrel. 
by move=> ?? <- ?? <-; rewrite ord63_addP.
Qed.

Global Instance refine_ord63int63_eq: 
  refines (r_ord63int63 ==> r_ord63int63 ==> bool_R)%rel eqtype.eq_op eq_op.
Proof.
rewrite refinesE /r_ord63int63 /fun_hrel.
move=> ? x <- ? y <-; rewrite /eq_op /eq_int63.
rewrite ord63_eqbP; exact: bool_Rxx.
Qed.

Global Instance refine_ord63int63_to_int63 x:
  refines r_ord63int63 (int63_to_ord63 x) x.
Proof. by rewrite refinesE /r_ord63int63 /fun_hrel. Qed.

End RefineInt63.

Section Test.

Print Instances refines.

Notation "[ x ]" := (int63_to_ord63 x).

Goal ord63_add [100] [1] == [101].
coqeal.
Abort.

Goal forall x, ord63_add x [0] == x.
coqeal.

(* Goal ord63_add ord63_1 ord0 = ord63_1.
Fail Timeout 2 vm_compute.
by coqeal.
Abort. *)

End Test.
