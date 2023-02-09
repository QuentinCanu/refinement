From Coq Require Import Uint63.
From mathcomp Require Import all_ssreflect all_algebra.
From CoqEAL Require Import refinements hrel param.
Local Open Scope ring_scope.
Import Refinements Op.
Require Import int63.

Section RefineInt63.

Definition r_ord63int63 := fun_hrel int63_to_ord63.

Global Instance zero_int63 : zero_of int63 := 0%uint63.
Global Instance one_int63 : one_of int63 := 1%uint63.
Global Instance add_int63 : add_of int63 := Uint63.add.
Global Instance eq_int63 : eq_of int63 := Uint63.eqb.

(* Global Instance refine_ord63int63_zero: refines r_ord63int63 ord0 0%C.
Proof. by rewrite refinesE /r_ord63int63 /fun_hrel ord63_0P. Qed.

Global Instance refine_ord63int63_one: refines r_ord63int63 ord63_1 1%C.
Proof. by rewrite refinesE /r_ord63int63 /fun_hrel ord63_1P. Qed. *)

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

Notation "[ x ]" := (int63_to_ord63 x).

Goal [100] + [1] == [101].
coqeal.
Abort.

Goal 11 + 0 == 11 :> ord63.
Fail Timeout 2 vm_compute.
apply: refines_goal.
Abort.

End Test.