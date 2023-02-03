(* -------------------------------------------------------------------- *)
From Coq      Require Import Uint63 BinNat.
From mathcomp Require Import all_ssreflect all_algebra.
From Trakt Require Import Trakt.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Section Misc.
Lemma peano_modE m n: m %% n = PeanoNat.Nat.modulo m n.
Proof.
case: n=> [|n] //.
rewrite [in RHS](divn_eq m n.+1).
rewrite addnC PeanoNat.Nat.mod_add //.
rewrite PeanoNat.Nat.mod_small //.
by apply/ssrnat.ltP/ltn_pmod.
Qed.
End Misc.

Notation int63 := PrimInt63.int.

Section Int63Nat.

Coercion int63_to_nat (x : int63) : nat := BinInt.Z.to_nat (to_Z x).
Definition nat_to_int63 (x : nat) : int63 := of_Z (BinInt.Z.of_nat x).

Definition int63_threshold := locked (2 ^ Uint63.size).

Lemma int63_threshold0 : (int63_threshold > 0).
Proof.
by rewrite /int63_threshold; unlock.
Qed.

Lemma int63_threshold1 : (int63_threshold > 1).
Proof.
by rewrite /int63_threshold; unlock.
Qed.

Lemma wB_def: BinInt.Z.to_nat wB = int63_threshold.
Proof.
rewrite Znat.Z2Nat.inj_pow // Znat.Z2Nat.inj_pos Znat.Nat2Z.id.
rewrite Pnat.Pos2Nat.inj_xO Pnat.Pos2Nat.inj_1 multE muln1.
rewrite /int63_threshold; unlock.
elim: Uint63.size=> /=; first by rewrite expn0.
by move=> n ->; rewrite plusE addn0 expnS mul2n addnn.
Qed.

Lemma int63_to_Z_ge0 (x : int63): BinInt.Z.le Z0 (to_Z x).
Proof. by case: (to_Z_bounded x). Qed.

Lemma int63_thresholdP (x : int63): x < int63_threshold.
Proof.
rewrite -wB_def /int63_to_nat.
apply/ltP/Znat.Nat2Z.inj_lt; case: (to_Z_bounded x)=> ??. 
by rewrite !Znat.Z2Nat.id.
Qed.

Lemma int63_to_natK : cancel int63_to_nat nat_to_int63.
Proof. 
move=> x; rewrite /nat_to_int63 /int63_to_nat.
rewrite Znat.Z2Nat.id ?of_to_Z //.
by case: (to_Z_bounded x).
Qed.

Lemma nat_to_int63K : {in gtn int63_threshold, cancel nat_to_int63 int63_to_nat}.
Proof.
move=> y; rewrite inE => /ltP/Znat.Nat2Z.inj_lt.
rewrite -wB_def Znat.Z2Nat.id // => ?. 
rewrite /int63_to_nat /nat_to_int63 of_Z_spec.
rewrite Zdiv.Zmod_small ?Znat.Nat2Z.id //; split=> //.
exact: Zorder.Zle_0_nat.
Qed.

Lemma int63_to_nat_inj: injective int63_to_nat.
Proof. by move=> i j /(congr1 nat_to_int63); rewrite !int63_to_natK. Qed.

Lemma eqEint63 (x y : int63): (x =? y)%uint63 = 
  (int63_to_nat x == int63_to_nat y).
Proof.
apply/idP/idP; first by move=> /eqb_spec ->.
move/eqP/int63_to_nat_inj=> ->; exact: eqb_refl.
Qed.

Lemma leEint63 i j: (i <=? j)%uint63 = (i <= j)%nat.
Proof.
apply/idP/idP.
- move/lebP/Znat.Z2Nat.inj_le => /(_ (@int63_to_Z_ge0 i) (@int63_to_Z_ge0 j)).
  by move/leP.
- move/leP=> h; apply/lebP/Znat.Z2Nat.inj_le=> //; exact: int63_to_Z_ge0.
Qed.

Lemma ltEint63 i j: (i <? j)%uint63 = (i < j)%nat.
Proof.
apply/idP/idP.
- move/ltbP/Znat.Z2Nat.inj_lt => /(_ (@int63_to_Z_ge0 i) (@int63_to_Z_ge0 j)).
  by move/ltP.
- move/ltP=> h; apply/ltbP/Znat.Z2Nat.inj_lt=> //; exact: int63_to_Z_ge0.
Qed.

End Int63Nat.

Section Int63Ordinal.

Definition ord63 := 'Z_(int63_threshold).

Lemma Zp_trunc_ord63E: (Zp_trunc int63_threshold).+2 = int63_threshold.
Proof.
rewrite /Zp_trunc !prednK //;
  [rewrite ltn_predRL; exact:int63_threshold1|exact:int63_threshold0].
Qed.

Program Definition int63_to_ord63 (x : int63) : ord63 := @Ordinal _ (int63_to_nat x) _.
Next Obligation. rewrite Zp_trunc_ord63E; exact: int63_thresholdP. Qed.

Definition ord63_to_int63 (x : ord63):= nat_to_int63 x.

Lemma int63_to_ord63K: forall x : int63, x = ord63_to_int63 (int63_to_ord63 x).
Proof.
by move=> x /=; rewrite /ord63_to_int63 /int63_to_ord63 /= int63_to_natK.
Qed.

Lemma int63_to_ord63K_sym: forall x : int63, ord63_to_int63 (int63_to_ord63 x) = x.
Proof. by move=> ?; rewrite -int63_to_ord63K. Qed.

Lemma ord63_to_int63K: forall x : ord63, int63_to_ord63 (ord63_to_int63 x) = x.
Proof.
move=> x; apply/val_inj=> /=; case: x=> x ? /=.
by rewrite nat_to_int63K //= inE -Zp_trunc_ord63E.
Qed.

Lemma ord63_to_int63K_sym: forall x : ord63, x = int63_to_ord63 (ord63_to_int63 x).
Proof. by move=> ?; rewrite ord63_to_int63K. Qed. 

Trakt Add Embedding int63 ord63 int63_to_ord63 ord63_to_int63 int63_to_ord63K ord63_to_int63K.
Trakt Add Embedding ord63 int63 ord63_to_int63 int63_to_ord63 ord63_to_int63K_sym int63_to_ord63K_sym.

Definition ord63_eqb (x y : ord63): bool := x == y.

Lemma ord63_eqbP: forall x y : int63, (x =? y)%uint63 = 
  ord63_eqb (int63_to_ord63 x) (int63_to_ord63 y).
Proof. by move=> x y; rewrite eqEint63 /ord63_eqb -val_eqE /=. Qed.

Lemma int63_eqbP: forall x y : ord63, 
  ord63_eqb x y = (ord63_to_int63 x =? ord63_to_int63 y)%uint63.
Proof.
move=> x y; rewrite -[in LHS](ord63_to_int63K x) -[in LHS](ord63_to_int63K y).
by rewrite ord63_eqbP.
Qed.

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

Lemma ord63_eqP: forall x y : int63, x = y <-> int63_to_ord63 x = int63_to_ord63 y.
Proof.
move=> x y; split; first by move=> ->.
by move/(congr1 val)/int63_to_nat_inj.
Qed.

Lemma int63_eqP: forall x y : ord63, x = y <-> ord63_to_int63 x = ord63_to_int63 y.
Proof.
trakt int63 Prop. 
move=> ??; split; first by move=> ->.
by rewrite -!int63_to_ord63K => ->.
Qed.

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
(* Is it okay ?*)
Abort. 

Definition ord63_add (x y : ord63) : ord63 := (x + y)%R.

Lemma ord63_addP: forall x y : int63,
  int63_to_ord63 (x + y)%uint63 = ord63_add (int63_to_ord63 x) (int63_to_ord63 y).
Proof.
move=> x y; apply/val_inj=> /=.
rewrite /int63_to_nat Zp_trunc_ord63E add_spec.
rewrite Znat.Z2Nat.inj_mod //;
  first by (apply:BinInt.Z.add_nonneg_nonneg; exact:int63_to_Z_ge0).
rewrite Znat.Z2Nat.inj_add; try exact:int63_to_Z_ge0.
by rewrite wB_def plusE peano_modE.
Qed.

Lemma int63_addP: forall x y : ord63,
  ord63_to_int63 (ord63_add x y) = (ord63_to_int63 x + ord63_to_int63 y)%uint63.
Proof.
by trakt int63 Prop=> ??; rewrite -ord63_addP -!int63_to_ord63K.
Qed.

Trakt Add Symbol Uint63.add ord63 ord63_add ord63_addP.
Trakt Add Symbol ord63_add int63 Uint63.add int63_addP.

Goal forall x : int63, (x + x)%uint63 = x.
trakt ord63 Prop.
Abort.

Set Printing All.
Goal forall x : ord63, (x + x)%R = x.
rewrite -?[GRing.Zmodule.sort _]/ord63.
rewrite -?[GRing.Ring.sort _]/ord63.
rewrite -[@GRing.add _]/ord63_add.
trakt int63 Prop.
Abort.

Definition ord63_mul (x y : ord63) : ord63 := (x * y)%R.

Lemma ord63_mulP: forall x y : int63,
  int63_to_ord63 (x * y)%uint63 = ord63_mul (int63_to_ord63 x) (int63_to_ord63 y).
Proof.
move=> x y; apply/val_inj=> /=; rewrite Zp_trunc_ord63E.
rewrite /int63_to_nat mul_spec Znat.Z2Nat.inj_mod;
  last rewrite wB_def peano_modE Znat.Z2Nat.inj_mul //.
- apply/Ztac.mul_le; exact: int63_to_Z_ge0.
- exact/BinInt.Z.lt_le_incl/wB_pos.
- exact: int63_to_Z_ge0.
- exact: int63_to_Z_ge0.
Qed.

Lemma int63_mulP: forall x y : ord63,
  ord63_to_int63 (ord63_mul x y) =
  (ord63_to_int63 x * ord63_to_int63 y)%uint63.
Proof.
by trakt int63 Prop=> ??; rewrite -ord63_mulP -!int63_to_ord63K.
Qed.

Trakt Add Symbol Uint63.mul ord63 ord63_mul ord63_mulP.
Trakt Add Symbol ord63_mul int63 Uint63.mul int63_mulP.

Goal forall x : ord63, (x + x * x)%R = (x * x + x)%R.
rewrite -[@GRing.add _]/ord63_add -[@GRing.mul _]/ord63_mul.
trakt int63 Prop.
Abort.

Lemma ord63_0P: int63_to_ord63 0%uint63 = (ord0 : ord63).
Proof. exact/val_inj. Qed.
Lemma int63_0P: ord63_to_int63 ord0 = 0%int63.
Proof. by []. Qed.

Program Definition ord63_1 : ord63 := @Ordinal _ 1 _.

Lemma ord63_1P: int63_to_ord63 1%uint63 = ord63_1.
Proof. exact/val_inj. Qed.
Lemma int63_1P: ord63_to_int63 ord63_1 = 1%uint63.
Proof. by []. Qed.

Trakt Add Symbol (0%uint63) ord63 (ord0 : ord63) ord63_0P.
Trakt Add Symbol (1%uint63) ord63 (ord63_1) ord63_1P.
Trakt Add Symbol (ord0 : ord63) int63 (0%uint63) int63_0P.
Trakt Add Symbol (ord63_1) int63 (1%uint63) int63_1P.

Definition ord63_le (x y : ord63): bool := (x <= y)%nat.
Definition ord63_lt (x y : ord63): bool := (x < y)%nat.

Lemma ord63_leP: forall x y : int63,
  (x <=? y)%uint63 = ord63_le (int63_to_ord63 x) (int63_to_ord63 y).
Proof. by rewrite /ord63_le=> x y /=; rewrite -leEint63. Qed.

Lemma ord63_ltP: forall x y : int63,
  (x <? y)%uint63 = ord63_lt (int63_to_ord63 x) (int63_to_ord63 y).
Proof. by rewrite /ord63_lt=> x y /=; rewrite -ltEint63. Qed.

Lemma int63_leP: forall x y : ord63,
  ord63_le x y = (ord63_to_int63 x <=? ord63_to_int63 y)%uint63.
Proof. by trakt int63 bool=> ??; rewrite ord63_leP -!int63_to_ord63K. Qed.

Lemma int63_ltP: forall x y : ord63,
  ord63_lt x y = (ord63_to_int63 x <? ord63_to_int63 y)%uint63.
Proof. by trakt int63 bool=> ??; rewrite ord63_ltP -!int63_to_ord63K. Qed.

Trakt Add Relation 2 (Uint63.leb) ord63_le ord63_leP.
Trakt Add Relation 2 (Uint63.ltb) ord63_lt ord63_ltP.
Trakt Add Relation 2 ord63_le (Uint63.leb) int63_leP.
Trakt Add Relation 2 ord63_lt (Uint63.ltb) int63_ltP.


(* Program Definition ord63_eqMixin := @EqMixin ord63 ord63_eq _.
Next Obligation. move=> ??; exact/eqP. Qed.
Canonical ord63_eqType := EqType ord63 ord63_eqMixin. *)

Trakt Add Conversion (@eq_op).

Local Open Scope ring_scope.

(* Goal (ord63_1 == ord63_1).
trakt int63 bool. Should be (1 =? 1)%uint63 *)
(* 
Goal ord63_eq 
  ((ord63_1 + ord63_1) * (ord0 : ord63))
  (ord0 : ord63).
rewrite -[@GRing.add _]/ord63_add -[@GRing.mul _]/ord63_mul. 
(* trakt int63 bool. vm_compute. *)
Qed. *)

End Int63Ordinal.
