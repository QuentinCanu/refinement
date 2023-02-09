From Coq Require Import Uint63 PArray.
From CoqEAL Require Import refinements hrel.
From mathcomp Require Import all_ssreflect.
Require Import misc coqeal_int63.

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

(* Variant Rarr_seq (a : boolArray) (s : boolSeq) := Rarr_seq_spec
  of r_ord63int63  *)

End boolArray.