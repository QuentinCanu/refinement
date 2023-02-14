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

Goal forall x : ord63, x == x.
rewrite -[@eq_op _]/(ord63_eqb).
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

Goal forall x : int63, x = x.
trakt ord63 Prop.
Abort.

Goal forall x : ord63, x = x.
trakt int63 Prop.
Abort.

Goal forall x : int63, (x =? x)%uint63 -> x = x.
trakt ord63 Prop.
(* Expected : forall x' : ord63, ord63_eqb x' x' -> x' = x' *)
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

Goal forall x : ord63, (x + x)%R = x.
rewrite -?[GRing.Zmodule.sort _]/ord63.
rewrite -?[GRing.Ring.sort _]/ord63.
rewrite -[@GRing.add _]/ord63_add.
(* We need all of that *)
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

Goal forall x : ord63, (x + x * x)%R = (x * x + x)%R.
rewrite -[@GRing.add _]/ord63_add -[@GRing.mul _]/ord63_mul.
trakt int63 Prop.
Abort.

End Mul.

Section Const.

Definition ord63_1 : ord63 := 1%R.

Trakt Add Symbol (0%uint63) ord63 (ord0 : ord63) ord63_0P.
Trakt Add Symbol (1%uint63) ord63 (ord63_1) ord63_1P.
Trakt Add Symbol (ord0 : ord63) int63 (0%uint63) int63_0P.
Trakt Add Symbol (ord63_1) int63 (1%uint63) int63_1P.

End Const.

Section LeLt.

Definition ord63_le (x y : ord63) : bool := (x <= y)%O.
Definition ord63_lt (x y : ord63) : bool := (x < y)%O.

Trakt Add Relation 2 (Uint63.leb) ord63_le ord63_leP.
Trakt Add Relation 2 (Uint63.ltb) ord63_lt ord63_ltP.
Trakt Add Relation 2 ord63_le (Uint63.leb) int63_leP.
Trakt Add Relation 2 ord63_lt (Uint63.ltb) int63_ltP.

End LeLt.

End TraktDef.
