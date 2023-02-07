From Coq Require Import Uint63.
From mathcomp Require Import all_ssreflect all_algebra.
From CoqEAL Require Import refinements hrel.

Local Open Scope ring_scope.
Import Refinements Op.

(* Section CoqEAL_alone.

Goal (10 < 10^(3+3) :> rat) -> (10 < 1000^2 :> rat). 
Time by vm_compute.
Restart.
Time by coqeal. (* 8s *)
Qed.

End CoqEAL_alone.

Section CoqEAL_binrat.

From CoqEAL Require Import binrat.

Goal (10 < 10^(3+3) :> rat) -> (10 < 1000^2 :> rat). 
Time by vm_compute.
Restart.
Time by coqeal. (* 15s *)
Qed.

End CoqEAL_binrat.

Section CoqEAL_rational.

From CoqEAL Require Import rational binint binnat.

Goal (10 < 10^(3+3) :> rat) -> (10 < 1000^2 :> rat). 
Time by vm_compute.
Restart.
Time by coqeal. (* 15s *)
Qed.

End CoqEAL_rational. *)

Require Import int63.

Section RefineInt63.

Definition r_ord63int63 := fun_hrel int63_to_ord63.

Global Instance zero_int63 : zero_of int63 := 0%uint63.
Global Instance one_int63 : one_of int63 := 1%uint63.
Global Instance add_int63 : add_of int63 := Uint63.add.
Global Instance spec_int63: spec_of int63 ord63 := int63_to_ord63.
Global Instance implem_int63: implem_of ord63 int63 := ord63_to_int63.

Global Instance refine_ord63int63_zero: refines r_ord63int63 ord0 0%C.
Proof. by rewrite refinesE /r_ord63int63 /fun_hrel ord63_0P. Qed.

Global Instance refine_ord63int63_one: refines r_ord63int63 ord63_1 1%C.
Proof. by rewrite refinesE /r_ord63int63 /fun_hrel ord63_1P. Qed.

Global Instance refine_ord63int63_add: 
  refines (r_ord63int63 ==> r_ord63int63 ==> r_ord63int63)%rel ord63_add +%C.
Proof. 
rewrite refinesE /r_ord63int63 /fun_hrel. move=> ?? <- ?? <-. 
by rewrite ord63_addP.
Qed.

Global Instance refine_ord63int63_spec:
  refines (eq ==> r_ord63int63)%rel spec spec_id. 
Proof. by rewrite refinesE=> ?? ->. Qed.

Global Instance refine_ord63int63_implem:
  refines (eq ==> r_ord63int63)%rel implem_id implem.
Proof. rewrite refinesE=> ?? ->; exact:ord63_to_int63K. Qed.

End RefineInt63.

Section Test.

Goal ord63_add ord0 ord0 = ord0.
Fail Timeout 2 vm_compute.
by coqeal.
Qed.

Goal ord63_add ord63_1 ord0 = ord63_1.
Fail Timeout 2 vm_compute.
by coqeal.
Qed.

End Test.
