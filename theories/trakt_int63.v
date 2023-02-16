(* -------------------------------------------------------------------- *)
From Coq      Require Import Uint63 BinNat.
From mathcomp Require Import all_ssreflect all_algebra.
Require Import int63 int63_ordinal.
From Trakt Require Import Trakt.
(* Cannot be treated twice by coqtop *)

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Section TraktDef.

Trakt Add Embedding int63 ord63 int63_to_ord63 ord63_to_int63 int63_to_ord63K ord63_to_int63K.
Trakt Add Embedding ord63 int63 ord63_to_int63 int63_to_ord63 ord63_to_int63K_sym int63_to_ord63K_sym.

Section Eqb.
Trakt Add Relation 2 Uint63.eqb ord63_eqb ord63_eqbP.
Trakt Add Relation 2 ord63_eqb Uint63.eqb int63_eqbP.

(* relation bool over T ~> relation bool over T' : only 1 declaration *)

Lemma eq_op_ord63_int63_eqb : forall x y, @eq_op (ordinal_eqType (S (S (Zp_trunc int63_threshold)))) x y = ((ord63_to_int63 x) =? (ord63_to_int63 y))%uint63.
Admitted.

Trakt Add Relation 2 (@eq_op (ordinal_eqType (S (S (Zp_trunc int63_threshold)))) : ord63 -> ord63 -> bool) Uint63.eqb eq_op_ord63_int63_eqb.

Goal forall x : ord63, x == x.
(* rewrite -[@eq_op _]/(ord63_eqb). *)
trakt int63 bool.
Abort.

Goal forall x : int63, (x =? x)%uint63.
Proof.
trakt ord63 bool.
Abort.

End Eqb.

Section Eq.

Trakt Add Relation 2 (@eq int63) (@eq ord63) ord63_eqP.
Trakt Add Relation 2 (@eq ord63) (@eq int63) int63_eqP.

(* relation bool over T ~> relation Prop over T' : 2 declarations
     1: relation bool T ~> relation Prop T
     2: relation Prop T ~> relation Prop T'
*)

Lemma int63_eqb_eq : forall x y, (x =? y)%uint63 = true <-> x = y.
Admitted.

Trakt Add Relation 2 Uint63.eqb (@eq int63) int63_eqb_eq.

Goal forall x : int63, x = x.
trakt ord63 Prop.
Abort.

Goal forall x : ord63, x = x.
trakt int63 Prop.
Abort.

(* Trakt uses syntax "= true" so is_true gets in the way *)
Goal forall x : int63, (x =? x)%uint63 -> x = x.
rewrite /is_true.
trakt ord63 Prop.
Abort.

End Eq.

Section Add.

Definition ord63_add (x y : ord63) : ord63 := (x + y)%R.

Lemma ord63_addP (x y : int63): int63_to_ord63 (x + y) = 
  ord63_add (int63_to_ord63 x) (int63_to_ord63 y).
Proof. exact: ord63_addP. Qed.

Trakt Add Symbol Uint63.add ord63 ord63_add ord63_addP.
Trakt Add Symbol ord63_add int63 Uint63.add int63_addP.

Goal forall x : int63, (x + x)%uint63 = x.
trakt ord63 Prop.
Abort.

Trakt Add Conversion GRing.add.
Trakt Add Conversion GRing.Zmodule.sort.

Goal forall x : ord63, (x + x)%R = x.
(* rewrite -?[GRing.Zmodule.sort _]/ord63.
rewrite -?[GRing.Ring.sort _]/ord63.
rewrite -[@GRing.add _]/ord63_add. *)
trakt int63 Prop.
Abort.

End Add.

Section Mul.

Definition ord63_mul (x y : ord63) : ord63 := (x * y)%R.

Lemma ord63_mulP: forall x y : int63,
  int63_to_ord63 (x * y)%uint63 = ((int63_to_ord63 x) * (int63_to_ord63 y))%R.
Proof. exact: ord63_mulP. Qed.

Trakt Add Symbol Uint63.mul ord63 ord63_mul ord63_mulP.
Trakt Add Symbol ord63_mul int63 Uint63.mul int63_mulP.

Trakt Add Conversion GRing.mul.

Goal forall x : ord63, (x + x * x)%R = (x * x + x)%R.
(* rewrite -[@GRing.add _]/ord63_add -[@GRing.mul _]/ord63_mul.
rewrite -[@GRing.Zmodule.sort _]/ord63. *)
trakt int63 Prop.
Abort.

End Mul.

Section Const.

Definition ord63_1 : ord63 := 1%R.

Trakt Add Symbol (0%uint63) ord63 (ord0 : ord63) ord63_0P.
Trakt Add Symbol (1%uint63) ord63 (ord63_1) ord63_1P.
Trakt Add Symbol (ord0 : ord63) int63 (0%uint63) int63_0P.
Trakt Add Symbol (ord63_1) int63 (1%uint63) int63_1P.

Trakt Add Conversion GRing.one.
Trakt Add Conversion GRing.zero.

Goal 1%R = (0 + 1)%R :> ord63.
(* rewrite -[@GRing.one _]/ord63_1 -[@GRing.add _]/ord63_add.
rewrite -[@GRing.zero _]/(ord0 : ord63). *)
trakt int63 Prop.
Abort.

Goal 0%uint63 = (0 * 1)%uint63.
trakt ord63 Prop.
rewrite /=.
Abort.

End Const.

Section LeLt.

Definition ord63_le (x y : ord63) : bool := (x <= y)%O.
Definition ord63_lt (x y : ord63) : bool := (x < y)%O.

Trakt Add Relation 2 (Uint63.leb) ord63_le ord63_leP.
Trakt Add Relation 2 (Uint63.ltb) ord63_lt ord63_ltP.
Trakt Add Relation 2 ord63_le (Uint63.leb) int63_leP.
Trakt Add Relation 2 ord63_lt (Uint63.ltb) int63_ltP.

Goal forall x y : int63, (x <? y)%uint63 -> (x <=? y)%uint63.
trakt ord63 bool.
Abort.

Trakt Add Conversion Order.lt.
Trakt Add Conversion Order.le.

Lemma Orderlt_ord63_int63_ltb :
  forall x y, (x < y)%O = (ord63_to_int63 x <? ord63_to_int63 y)%uint63.
Admitted.

Trakt Add Relation 2
  (@Order.lt (Order.OrdinalOrder.ord_display)
    (Order.OrdinalOrder.porderType (S (S (Zp_trunc int63_threshold)))))
  Uint63.ltb
  Orderlt_ord63_int63_ltb.

Lemma Orderle_ord63_int63_leb :
  forall x y, (x <= y)%O = (ord63_to_int63 x <=? ord63_to_int63 y)%uint63.
Admitted.

Trakt Add Relation 2
  (@Order.le (Order.OrdinalOrder.ord_display)
    (Order.OrdinalOrder.porderType (S (S (Zp_trunc int63_threshold)))))
  Uint63.leb
  Orderle_ord63_int63_leb.

Goal forall x y : ord63, (x < y)%O -> (x <= y)%O.
(* rewrite -[@Order.lt _ _]/ord63_lt -[@Order.le _ _]/ord63_le. *)
trakt int63 bool.
Abort.

End LeLt.

Section Exp.

Definition ord63_exp (x n : ord63) := (x ^ n)%R.

(* Trakt Add Symbol (fun n : N => int63_exp^~n) (fun n : N => ord63_exp^~n) foo. *)

End Exp.

End TraktDef.

Section Preprocessing.

Local Open Scope ring_scope.

(* Ltac ord63_preprocess := 
  rewrite
  -?[@GRing.Zmodule.sort _]/ord63
  -?[@GRing.add _]/ord63_add -?[@GRing.mul _]/ord63_mul
  -?[@eq_op _]/ord63_eqb 
  -?[@Order.le _ _]/ord63_le -?[@Order.lt _ _]/ord63_lt
  -?[@GRing.one _]/ord63_1 -?[@GRing.zero _]/(ord0 : ord63).

Ltac int63_postprocess :=
  rewrite -?int63_to_ord63K. *)

Trakt Add Conversion GRing.Zmodule.eqType.

Goal forall x : ord63, (x + x) == (x * x).
(* ord63_preprocess. *)
trakt int63 bool.
Abort.

Goal forall x : ord63, (x + x)%R = (x * x)%R.
(* ord63_preprocess. *)
trakt int63 Prop.
Abort.

Goal (0 + 0 * 1)%R = (1 * 0 + 0 * 1)%R :> ord63.
(* ord63_preprocess. *)
trakt int63 Prop.
Abort.

Goal ((0%R : ord63) < (1%R : ord63))%O.
rewrite /is_true.
(* ord63_preprocess. *)
trakt int63 bool.
Abort.

(*
A ~> B
E : A -> B

f : B -> A
f' : B -> B

forall (x : B), E (f x) = f' x

f : A -> A
forall (x : A), E (f x) = f' (E x)
*)

Lemma int63_to_ord63_id : forall x, ord63_to_int63 (int63_to_ord63 x) = x.
Admitted.

Trakt Add Symbol int63_to_ord63 (@id int63) int63_to_ord63_id.

Goal int63_to_ord63 12 + int63_to_ord63 13 == int63_to_ord63 25.
rewrite /is_true.
(* ord63_preprocess. *)
trakt int63 bool.
(* int63_postprocess. *)
vm_compute. reflexivity.
Abort.

Notation "[ x ]" := (int63_to_ord63 x).

End Preprocessing.
