(* -------------------------------------------------------------------- *)
From Coq      Require Import Uint63 BinNat.
From mathcomp Require Import all_ssreflect all_algebra.
Require Import int63.
Require Import NArith PArith BinNatDef BinPosDef.

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

Lemma ord63_eqP: forall x y : int63, x = y <-> int63_to_ord63 x = int63_to_ord63 y.
Proof.
move=> x y; split; first by move=> ->.
by move/(congr1 val)/int63_to_nat_inj.
Qed.

Lemma int63_eqP: forall x y : ord63, x = y <-> ord63_to_int63 x = ord63_to_int63 y.
Proof. 
move=> x y; split; first by move=> ->.
by rewrite -[x]ord63_to_int63K -[y]ord63_to_int63K -!int63_to_ord63K => ->.
Qed.

Lemma ord63_addP: forall x y : int63,
  int63_to_ord63 (x + y)%uint63 = ((int63_to_ord63 x) + (int63_to_ord63 y))%R.
Proof.
move=> x y; apply/val_inj=> /=.
rewrite /int63_to_nat Zp_trunc_ord63E add_spec.
rewrite Znat.Z2Nat.inj_mod //;
  first by (apply:BinInt.Z.add_nonneg_nonneg; exact:int63_to_Z_ge0).
rewrite Znat.Z2Nat.inj_add; try exact:int63_to_Z_ge0.
by rewrite wB_def plusE peano_modE.
Qed.

Lemma int63_addP: forall x y : ord63,
  ord63_to_int63 (x + y)%R = (ord63_to_int63 x + ord63_to_int63 y)%uint63.
Proof.
move=> x y.
by rewrite -[x]ord63_to_int63K -[y]ord63_to_int63K -ord63_addP -!int63_to_ord63K.
Qed.

Lemma ord63_mulP: forall x y : int63,
  int63_to_ord63 (x * y)%uint63 = ((int63_to_ord63 x) * (int63_to_ord63 y))%R.
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
  ord63_to_int63 (x * y)%R =
  (ord63_to_int63 x * ord63_to_int63 y)%uint63.
Proof.
move=> x y.
by rewrite -[x]ord63_to_int63K -[y]ord63_to_int63K -ord63_mulP -!int63_to_ord63K.
Qed.

Lemma ord63_0P: int63_to_ord63 0%uint63 = (ord0 : ord63).
Proof. exact/val_inj. Qed.
Lemma int63_0P: ord63_to_int63 ord0 = 0%int63.
Proof. by []. Qed.

Lemma ord63_1P: int63_to_ord63 1%uint63 = (1%R : ord63).
Proof. exact/val_inj. Qed.
Lemma int63_1P: ord63_to_int63 (1%R : ord63) = 1%uint63.
Proof. by []. Qed.

Lemma ord63_leP: forall x y : int63,
  (x <=? y)%uint63 = ((int63_to_ord63 x) <= (int63_to_ord63 y))%nat.
Proof. by move=> x y /=; rewrite -leEint63. Qed.

Lemma ord63_ltP: forall x y : int63,
  (x <? y)%uint63 = ((int63_to_ord63 x) < (int63_to_ord63 y))%nat.
Proof. by move=> x y /=; rewrite -ltEint63. Qed.

Lemma int63_leP: forall x y : ord63,
  (x <= y)%nat = (ord63_to_int63 x <=? ord63_to_int63 y)%uint63.
Proof. 
move=> x y.
by rewrite -[x]ord63_to_int63K -[y]ord63_to_int63K ord63_leP -!int63_to_ord63K. 
Qed.

Lemma int63_ltP: forall x y : ord63,
  (x < y)%nat = (ord63_to_int63 x <? ord63_to_int63 y)%uint63.
Proof. 
move=> x y.
by rewrite -[x]ord63_to_int63K -[y]ord63_to_int63K ord63_ltP -!int63_to_ord63K. 
Qed.

Fixpoint int63_exp_ (fuel : nat) (x n : int63):=
  if (n =? 0)%uint63 then 1%uint63 else
    if fuel is k.+1 then
      if is_even n then 
        (int63_exp_ k x (n >> 1)%uint63 * int63_exp_ k x (n >> 1))%uint63 else 
      (x * (int63_exp_ k x (n >> 1)) * (int63_exp_ k x (n >> 1)))%uint63
    else x.
  
Definition int63_exp (x n : int63):=
  int63_exp_ Uint63.size x n.

Lemma ord63_expP (x n : int63):
  int63_to_ord63 (int63_exp x n) = ((int63_to_ord63 x) ^ (int63_to_ord63 n))%R.
Proof.
apply/val_inj=> /=.
rewrite /int63_exp.
Admitted.

Lemma int63_expP (x : ord63) (n : N):
  ord63_to_int63 (x ^ n)%R = int63_exp (ord63_to_int63 x) n.
Proof.
Admitted.






End Int63Ordinal.
