From Coq Require Import Uint63 PArray.
From CoqEAL Require Import refinements hrel.
From mathcomp Require Import all_ssreflect all_algebra.
Require Import misc coqeal_int63 int63.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import Refinements Op.
Local Open Scope ring_scope.

Local Notation "a .[ i ]" := (get a i).

Section Array.

Variable A : Type.

Definition arr_to_seq (a : array A) : seq A :=
  rev (ifold (fun i s=> a.[i] :: s) (length a) [::]).

Variant Rarrseq: array A -> seq A -> Type := 
  Rarrseq_spec (a : array A) (s : seq A) of
    r_natint63 (seq.size s) (length a) &
    (forall i j, r_natint63 i j -> a.[j] = nth (default a) s i)
  : Rarrseq a s.

(* Global Instance arr_seq_spec : spec_of boolArray boolSeq :=
  arr_to_seq. *)

(* Variant Rarr_seq (a : boolArray) (s : boolSeq) := Rarr_seq_spec
  of r_ord63int63  *)

End Array.