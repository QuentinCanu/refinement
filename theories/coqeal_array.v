From Coq Require Import Uint63 PArray.
From CoqEAL Require Import refinements hrel.
From mathcomp Require Import all_ssreflect all_algebra.
Require Import coqeal_int63 int63.

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

Variant Rarrseq: seq A -> array A -> Type := 
  Rarrseq_spec (s : seq A) (a : array A) of
    r_natint63 (seq.size s) (length a) &
    (forall i j, r_natint63 i j -> a.[j] = nth (default a) s i)
  : Rarrseq s a.

Global Instance Rarrseq_arr_to_seq a: refines Rarrseq (arr_to_seq a) a.
Proof.
rewrite refinesE; constructor.
- admit.
- admit.
Admitted.

Global Instance Rarrseq_make (i : int63) (n : nat) (x : A): 
  refines r_natint63 n i ->
  refines Rarrseq (nseq n x) (make i x).
Proof.
rewrite !refinesE => <-; constructor.
Admitted.

End Array.