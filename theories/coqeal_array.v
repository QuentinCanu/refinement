From Coq Require Import Uint63 PArray.
From CoqEAL Require Import refinements hrel.
From mathcomp Require Import all_ssreflect.
Require Import misc.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import Refinements Op.

Section NatArray.

Definition natArray := array nat.
Definition natSeq := seq nat.

Definition arr_to_seq (a : natArray) : natSeq :=
  rev (ifold (fun i s=> a.[i] :: s) (length a) [::]).

Global Instance arr_seq_spec : spec_of natArray natSeq :=
  arr_to_seq.


End NatArray.