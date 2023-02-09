From Coq Require Import Uint63.
From mathcomp Require Import all_ssreflect all_algebra.
From CoqEAL Require Import refinements hrel param.
(* Require Import misc. *)

Local Open Scope ring_scope.
Import Refinements Op.

From CoqEAL Require Import binrat.
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

End CoqEAL_binrat.

(* Section CoqEAL_rational.

From CoqEAL Require Import rational binint binnat.

Goal (10 < 10^(3+3) :> rat) -> (10 < 1000^2 :> rat). 
by coqeal. (* 15s *)
Restart.
Time by vm_compute.
Qed.

End CoqEAL_rational. *)
