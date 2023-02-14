From Coq Require Import Uint63.
From mathcomp Require Import all_ssreflect all_algebra.
From CoqEAL Require Import refinements hrel param.
Local Open Scope ring_scope.
Import Refinements Op.
Require Import int63 int63_ordinal.

Section InstancesInt63.

Global Instance zero_int63 : zero_of int63 := 0%uint63.
Global Instance one_int63 : one_of int63 := 1%uint63.
Global Instance add_int63 : add_of int63 := Uint63.add.
Global Instance mul_int63 : mul_of int63 := Uint63.mul.
Global Instance le_int63 : leq_of int63 := Uint63.leb.
Global Instance lt_int63 : lt_of int63 := Uint63.ltb.
Global Instance eq_int63 : eq_of int63 := Uint63.eqb.

End InstancesInt63.

Section RefineInt63Nat.

Definition r_natint63 := fun_hrel int63_to_nat.

Global Instance refine_natint63_zero: refines r_natint63 0%nat 0%C.
Proof. by rewrite refinesE /r_natint63 /fun_hrel. Qed.

Global Instance refine_natint63_one: refines r_natint63 1%nat 1%C.
Proof. by rewrite refinesE /r_natint63 /fun_hrel. Qed.

Global Instance refine_natint63_eq: 
  refines (r_natint63 ==> r_natint63 ==> bool_R)%rel eqtype.eq_op eq_op.
Proof.
rewrite refinesE /r_natint63 /fun_hrel.
move=> ? x <- ? y <-; rewrite /eq_op /eq_int63.
rewrite eqEint63; exact: bool_Rxx.
Qed.

Global Instance refine_natint63_le: 
  refines (r_natint63 ==> r_natint63 ==> bool_R)%rel 
    (fun x y : nat => (x <= y)%nat) leq_op.
Proof.
rewrite refinesE /r_natint63 /fun_hrel.
move=> ? x <- ? y <-; rewrite /leq_op /le_int63.
rewrite leEint63; exact: bool_Rxx.
Qed.

Global Instance refine_natint63_lt: 
  refines (r_natint63 ==> r_natint63 ==> bool_R)%rel 
    (fun x y : nat => (x < y)%nat) lt_op.
Proof.
rewrite refinesE /r_natint63 /fun_hrel.
move=> ? x <- ? y <-; rewrite /lt_op /lt_int63.
rewrite ltEint63; exact: bool_Rxx.
Qed.

Global Instance refine_natint63_to_int63 x:
  refines r_natint63 (int63_to_nat x) x.
Proof. by rewrite refinesE /r_natint63 /fun_hrel. Qed.

End RefineInt63Nat.

Section TestNat.

Goal (int63_to_nat 5 <= int63_to_nat 10)%O.
Proof.
Set Typeclasses Debug.
by coqeal.
Abort.

End TestNat.

Section RefineInt63Ord63.

Definition r_ord63int63 := fun_hrel int63_to_ord63.

Global Instance refine_ord63int63_zero: refines r_ord63int63 0%R 0%C.
Proof. by rewrite refinesE /r_ord63int63 /fun_hrel ord63_0P. Qed.

Global Instance refine_ord63int63_one: refines r_ord63int63 1 1%C.
Proof. by rewrite refinesE /r_ord63int63 /fun_hrel ord63_1P. Qed.

Global Instance refine_ord63int63_add: 
  refines (r_ord63int63 ==> r_ord63int63 ==> r_ord63int63)%rel +%R +%C.
Proof. 
rewrite refinesE /r_ord63int63 /fun_hrel. 
by move=> ?? <- ?? <-; rewrite ord63_addP.
Qed.

Global Instance refine_ord63int63_mul: 
  refines (r_ord63int63 ==> r_ord63int63 ==> r_ord63int63)%rel *%R *%C.
Proof. 
rewrite refinesE /r_ord63int63 /fun_hrel. 
by move=> ?? <- ?? <-; rewrite ord63_mulP.
Qed.

Global Instance refine_ord63int63_eq: 
  refines (r_ord63int63 ==> r_ord63int63 ==> bool_R)%rel eqtype.eq_op eq_op.
Proof.
rewrite refinesE /r_ord63int63 /fun_hrel.
move=> ? x <- ? y <-; rewrite /eq_op /eq_int63.
rewrite ord63_eqbP; exact: bool_Rxx.
Qed.

Global Instance refine_ord63int63_le: 
  refines (r_ord63int63 ==> r_ord63int63 ==> bool_R)%rel 
    (fun x y : ord63 => (x <= y)%nat) leq_op.
Proof.
rewrite refinesE /r_ord63int63 /fun_hrel.
move=> ? x <- ? y <-.
rewrite -ord63_leP; exact: bool_Rxx.
Qed.

Global Instance refine_ord63int63_lt: 
  refines (r_ord63int63 ==> r_ord63int63 ==> bool_R)%rel 
    (fun x y : ord63 => (x < y)%nat) lt_op.
Proof.
rewrite refinesE /r_ord63int63 /fun_hrel.
move=> ? x <- ? y <-.
rewrite -ord63_ltP; exact: bool_Rxx.
Qed.

Global Instance refine_ord63int63_to_int63 x:
  refines r_ord63int63 (int63_to_ord63 x) x.
Proof. by rewrite refinesE /r_ord63int63 /fun_hrel. Qed.

End RefineInt63Ord63.

Section Test.

Notation "[ x ]" := (int63_to_ord63 x).

Goal [100] + [1] == [101].
coqeal.
Abort.

Goal ([10] * [10] < [101])%nat.
Proof.
coqeal.
Abort.

Goal ([10] * [10] + [5000] <= [5101])%nat.
Proof.
coqeal.
Abort.

Goal 1 + 0 == 1 :> ord63.
by [].
(* by apply: refines_goal. *)
Abort.

Goal 2 + 0 == 2 :> ord63.
Fail by [].
apply: refines_goal.
Abort.

End Test.