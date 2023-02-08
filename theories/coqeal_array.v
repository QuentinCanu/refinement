From Coq Require Import Uint63 PArray.
From CoqEAL Require Import refinements hrel.
From mathcomp Require Import all_ssreflect.
Require Import misc.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import Refinements Op.

Section boolArray.

Definition boolArray := array bool.
Definition boolSeq := seq bool.

Definition arr_to_seq (a : boolArray) : boolSeq :=
  rev (ifold (fun i s=> a.[i] :: s) (length a) [::]).

Global Instance arr_seq_spec : spec_of boolArray boolSeq :=
  arr_to_seq.

Definition arr_seq_rel := fun_hrel arr_to_seq.

Global Instance refine_arr_seq_spec: 
  refines (eq ==> arr_seq_rel)%rel spec spec_id.
Proof. 
rewrite refinesE=> x ? <-.
by rewrite /arr_seq_rel /fun_hrel /spec /spec_id /arr_seq_spec.
Qed.


End boolArray.