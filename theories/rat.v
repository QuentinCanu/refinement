(* -------------------------------------------------------------------- *)
(* This file content originates from the CoqEAL library.                *)
(*                                                                      *)
(*   https://github.com/coq-community/coqeal                            *)
(*                                                                      *)
(* The MIT License (MIT)                                                *)
(*                                                                      *)
(* Copyright (c) 2014  Guillaume Cano                                   *)
(* Copyright (c) 2014  Cyril Cohen                                      *)
(* Copyright (c) 2014  Maxime Dénès                                     *)
(* Copyright (c) 2014  Anders Mörtberg                                  *)
(* Copyright (c) 2014  Vincent Siles                                    *)
(* -------------------------------------------------------------------- *)

From Bignums Require Import BigQ.
From Coq Require Import PArith PeanoNat.
From mathcomp Require Import all_ssreflect all_algebra.
From Trakt Require Import Trakt.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import Order.Theory.
(* -------------------------------------------------------------------- *)

Section Misc.

Definition Z2int (z : BinNums.Z) : ssrint.int :=
  match z with
  | Z0 => 0
  | Zpos p => ((Pos.to_nat p)%:Z)%R
  | Zneg n => (- (Pos.to_nat n)%:Z)%R
  end.

Definition int2Z (n : ssrint.int) : BinNums.Z :=
match n with
| Posz O => Z0
| Posz n => Zpos (Pos.of_nat n)
| Negz n => Zneg (Pos.of_nat n.+1)
end.

Lemma Z2int_inj x y : Z2int x = Z2int y -> x = y.
Proof.
rewrite /Z2int.
case x, y=>//.
{ move=>[] H.
  by rewrite -[Z0]/(BinInt.Z.of_nat 0%N) H Znat.positive_nat_Z. }
{ rewrite /GRing.opp /= /intZmod.oppz /=.
  case E: (Pos.to_nat _)=>//=; move: (Pos2Nat.is_pos p).
  by rewrite E => /ssrnat.ltP. }
{ by case; move/(congr1 BinInt.Z.of_nat); rewrite Znat.positive_nat_Z. }
{ by case; move/(congr1 BinInt.Z.of_nat); rewrite !Znat.positive_nat_Z. }
{ case E: (Pos.to_nat _)=>//=; case E': (Pos.to_nat _)=> //=.
  by move: (Pos2Nat.is_pos p); rewrite E; move/ssrnat.ltP. }
{ move/eqP; rewrite GRing.oppr_eq0=> /eqP; case=> E.
  by move/ssrnat.ltP: (Pos2Nat.is_pos p); rewrite E. }
{ case E: (Pos.to_nat _)=> //=.
  by move/ssrnat.ltP: (Pos2Nat.is_pos p); rewrite E.  }
{ move/GRing.oppr_inj; case=> /(congr1 BinInt.Z.of_nat).
  by rewrite !Znat.positive_nat_Z; case=> ->. }
Qed.

Lemma int2ZK : cancel int2Z Z2int.
Proof.
case=> n; rewrite /Z2int /int2Z.
- by case: n=> // n; rewrite Nat2Pos.id //.
- by rewrite Nat2Pos.id.
Qed.

Lemma Z2intK : cancel Z2int int2Z.
Proof.
case=> [|p|p] //; rewrite /int2Z /Z2int.
- elim:p=> // p; rewrite !Pos2Nat.id //= Pos2Nat.inj_xO.
  by case: (Pos.to_nat p).
- move:(Pos2Nat.is_pos p); case E: (Pos.to_nat p)=> [|n]. 
  + by move/Nat.lt_irrefl.
  + by move=> _; rewrite -NegzE -E Pos2Nat.id.
Qed.

Lemma Z2int_opp n : Z2int (BinInt.Z.opp n) = (- (Z2int n))%R.
Proof. by case n=>// p /=; rewrite GRing.opprK. Qed.

Lemma Z2int_abs x : Z2int (BinInt.Z.abs x) = `|Z2int x|%nat.
Proof. by case: x => // p /=; rewrite abszN. Qed.


Lemma Z2int_add x y : Z2int (BinInt.Z.add x y) = (Z2int x + Z2int y)%R.
Proof.
case: x; case: y=> //=.
- by move=> ?; rewrite GRing.add0r.
- by move=> ?; rewrite GRing.addr0.
- by move=> ??; rewrite Pnat.Pos2Nat.inj_add.
- move=> q p; rewrite BinInt.Z.pos_sub_spec.
  case: BinPos.Pos.compare_spec=> /=.
  + move=> ->; by rewrite GRing.addrN.
  + move=> /[dup] /Pnat.Pos2Nat.inj_lt + /Pnat.Pos2Nat.inj_sub ->. 
    rewrite !minusE=> /ssrnat.ltP pq.
    rewrite -subzn; first exact: ltnW.
    by rewrite GRing.opprB.
  + move=> /[dup] /Pnat.Pos2Nat.inj_lt + /Pnat.Pos2Nat.inj_sub ->. 
    rewrite !minusE=> /ssrnat.ltP pq.
    by rewrite -subzn; first exact: ltnW.
- by move=> ?; rewrite GRing.addr0.
- move=> q p; rewrite BinInt.Z.pos_sub_spec.
  case: BinPos.Pos.compare_spec=> /=.
  + by move=> ->; rewrite GRing.addNr //.
  + move=> /[dup] /Pnat.Pos2Nat.inj_lt + /Pnat.Pos2Nat.inj_sub ->. 
    rewrite !minusE=> /ssrnat.ltP pq.
    rewrite -subzn ?GRing.opprB; first exact: ltnW.
    by rewrite GRing.addrC.
  + move=> /[dup] /Pnat.Pos2Nat.inj_lt /ssrnat.ltP pq /Pnat.Pos2Nat.inj_sub ->. 
    rewrite -subzn; first exact: ltnW.
    by rewrite GRing.addrC.
- move=> p q; rewrite Pnat.Pos2Nat.inj_add plusE PoszD.
  by rewrite -GRing.opprB GRing.opprK GRing.addrC.
Qed.

Lemma Z2int_mul_nat_of_pos (x : BinNums.Z) (y : positive) :
  (Z2int x * Pos.to_nat y)%R = Z2int (BinInt.Z.mul x (BinNums.Zpos y)).
Proof.
rewrite /Z2int; case Ex: x.
{ by rewrite GRing.mul0r BinInt.Z.mul_0_l. }
{ by rewrite /= Pos2Nat.inj_mul multE . }
by rewrite /= GRing.mulNr Pos2Nat.inj_mul multE.
Qed.

Lemma Z2int_mul x y : Z2int (BinInt.Z.mul x y) = (Z2int x * Z2int y)%R.
Proof.
case y=>/=.
{ by rewrite GRing.mulr0 BinInt.Z.mul_0_r. }
{ by move=> p; rewrite Z2int_mul_nat_of_pos. }
move=> p.
rewrite GRing.mulrN Z2int_mul_nat_of_pos -Z2int_opp.
by rewrite BinInt.Z.opp_eq_mul_m1 -BinInt.Z.mul_assoc -BinInt.Z.opp_eq_mul_m1 /=.
Qed.

Lemma divE x y : Nat.div x y = divn x y.
Proof.
case: y => [//|y].
rewrite /Nat.div.
move: (Nat.divmod_spec x y 0 y).
case: Nat.divmod => q r /(_ (le_n _)) [].
rewrite Nat.mul_0_r Nat.sub_diag !Nat.add_0_r Nat.mul_comm => + Hr /=.
rewrite multE minusE plusE => /(f_equal (fun x => divn x y.+1)) ->.
rewrite divnMDl // divn_small ?addn0 //.
rewrite ltn_subLR; [exact/ssrnat.leP|].
  by rewrite -addSnnS addnC addnS ltnS leq_addr.
Qed.

Lemma Z2int_div x y : BinInt.Z.le Z0 x -> BinInt.Z.le Z0 y ->
  Z2int (BinInt.Z.div x y) = divz (Z2int x) (Z2int y).
Proof.
case: x => [|x|//] _; [by rewrite intdiv.div0z|].
case: y => [|y|//] _; [by rewrite intdiv.divz0|].
rewrite -!Znat.positive_nat_Z -Znat.Nat2Z.inj_div.
rewrite !Znat.positive_nat_Z /= /divz gtr0_sgz ?GRing.mul1r.
{ by move/ssrnat.ltP: (Pos2Nat.is_pos y). }
rewrite divE absz_nat /Z2int.
move: (Zorder.Zle_0_nat (Pos.to_nat x %/ Pos.to_nat y)).
rewrite -[X in _ = Posz X]Znat.Nat2Z.id.
by case: BinInt.Z.of_nat => //=.
Qed.

Lemma Z2int_le x y : (Z2int x <= Z2int y)%R <-> BinInt.Z.le x y.
Proof.
rewrite /Z2int; case Ex: x; case Ey: y=> //.
{ rewrite Num.Theory.oppr_ge0; split; move=> H; exfalso; move: H; [|by rewrite /BinInt.Z.le].
  apply/negP; rewrite -ltNge; exact/ssrnat.ltP/Pos2Nat.is_pos. }
{ split; move=> H; exfalso; move: H; [|by rewrite /BinInt.Z.le].
  apply/negP; rewrite -ltNge; exact/ssrnat.ltP/Pos2Nat.is_pos. }
{ rewrite /Num.Def.ler /=.
  by rewrite -!Znat.positive_nat_Z -Znat.Nat2Z.inj_le; split => /ssrnat.leP. }
{ split; move=> H; exfalso; move: H; [|by rewrite /BinInt.Z.le].
  apply /negP; rewrite -ltNge.
  apply: (@lt_trans _ _ 0%R); rewrite ?Num.Theory.oppr_lt0; 
    apply/ssrnat.ltP/Pos2Nat.is_pos. }
{ rewrite Num.Theory.oppr_le0; split; by rewrite /BinInt.Z.le. }
{ split=>_; [by rewrite /BinInt.Z.le|].
  apply: (@le_trans _ _ 0%R); [apply Num.Theory.oppr_le0|apply ltW].
  exact/ssrnat.ltP/Pos2Nat.is_pos. }
rewrite Num.Theory.ler_opp2; split.
{ rewrite /BinInt.Z.le /BinInt.Z.compare /Num.Def.ler /= => /ssrnat.leP.
  by rewrite -Pos.compare_antisym -Pos2Nat.inj_le -Pos.compare_le_iff. }
rewrite /BinInt.Z.le /BinInt.Z.compare /Num.Def.ler /=.
rewrite -Pos.compare_antisym => H; apply/ssrnat.leP.
by rewrite -Pos2Nat.inj_le -Pos.compare_le_iff.
Qed.

Lemma Z2int_lt x y : (Z2int x < Z2int y)%R <-> BinInt.Z.lt x y.
Proof.
rewrite -lez_addr1 -[GRing.one _]/(Z2int BinInt.Z.one) -Z2int_add Z2int_le.
rewrite /BinInt.Z.one BinInt.Z.add_1_r; exact: BinInt.Z.le_succ_l.
Qed.

Lemma nat_of_pos_Z_to_pos x : Pos.to_nat x = `|Z2int (Zpos x)|%N.
Proof. by rewrite /absz /Z2int. Qed.

Lemma Zabs_natE n : BinInt.Z.abs_nat n = `|Z2int n|%N.
Proof.
case: n => //= p.
by rewrite abszN absz_nat.
Qed.

Lemma Z2int_Z_of_nat n : Z2int (BinInt.Z.of_nat n) = n.
Proof.
by case: n => //= n; rewrite Pos.of_nat_succ Nat2Pos.id.
Qed.

Lemma dvdnP m n : reflect 
  (BinInt.Z.divide (BinInt.Z.of_nat m) (BinInt.Z.of_nat n)) (m %| n).
Proof.
apply: (iffP idP) => H.
{ rewrite dvdn_eq in H; rewrite -(eqP H) /BinInt.Z.divide; exists (BinInt.Z.of_nat (n %/ m)).
  by rewrite Znat.Nat2Z.inj_mul. }
{ have [q Hq] := H; apply/dvdnP; exists `|Z2int q|%N; apply/Znat.Nat2Z.inj.
  have [Zq|NZq] := ZArith_dec.Z_zerop q.
  { by rewrite Zq /= in Hq *. }
  case: m Hq H => [|m] Hq H.
  { by rewrite BinInt.Zmult_comm /= in Hq; rewrite mulnC /=. }
  rewrite Znat.Nat2Z.inj_mul -Zabs_natE Znat.Zabs2Nat.id_abs BinInt.Z.abs_eq //.
  (* have H0 : (0 <= BinInt.Z.mul q (BinInt.Z.of_nat m.+1)). by rewrite -Hq; apply Zorder.Zle_0_nat. *)
  apply: (Zorder.Zmult_le_0_reg_r (BinInt.Z.of_nat m.+1)).
  - apply/BinInt.Z.lt_gt; rewrite -/(BinInt.Z.of_nat 0).
    exact/Znat.inj_lt/ssrnat.ltP.
  - rewrite -Hq; exact: Zorder.Zle_0_nat. }
Qed.

Lemma ZgcdE n d : BinInt.Z.gcd n (Zpos d) = 
  BinInt.Z.of_nat (div.gcdn `|Z2int n| (Pos.to_nat d)).
Proof.
apply: BinInt.Z.gcd_unique.
{ exact: Zorder.Zle_0_nat. }
{ apply/BinInt.Z.divide_abs_r; rewrite -Znat.Zabs2Nat.id_abs; apply/dvdnP.
  by rewrite Zabs_natE dvdn_gcdl. }
{ apply/BinInt.Z.divide_abs_r; rewrite -Znat.Zabs2Nat.id_abs; apply/dvdnP.
  by rewrite Zabs_natE /= dvdn_gcdr. }
move=> q Hn Hd; apply/BinInt.Z.divide_abs_l; rewrite -Znat.Zabs2Nat.id_abs; apply/dvdnP.
rewrite Zabs_natE dvdn_gcd.
apply/andP; split; apply/dvdnP; rewrite -!Zabs_natE !Znat.Zabs2Nat.id_abs.
{ by apply/BinInt.Z.divide_abs_l/BinInt.Z.divide_abs_r. }
{ by apply/BinInt.Z.divide_abs_l; rewrite Znat.positive_nat_Z. }
Qed.

Lemma ZgcdE' n m : BinInt.Z.gcd n m = BinInt.Z.of_nat (gcdn `|Z2int n| `|Z2int m|).
Proof.
case m.
{ rewrite BinInt.Z.gcd_0_r {2}/absz {2}/Z2int /= gcdn0 -Znat.Zabs2Nat.id_abs; f_equal.
  rewrite /BinInt.Z.abs_nat /absz /Z2int.
  case n=>// p; rewrite //.
  case (Pos.to_nat _); [by rewrite GRing.oppr0|move=> n'].
  by rewrite /GRing.opp /=. }
{ by move=> p; rewrite ZgcdE nat_of_pos_Z_to_pos. }
by move=> p; rewrite -BinInt.Z.gcd_opp_r /= ZgcdE abszN /absz.
Qed.


Lemma Z_ggcd_1_r n : BinInt.Z.ggcd n (Zpos 1) = (Zpos 1, (n, Zpos 1)).
Proof.
move: (BinInt.Z.ggcd_gcd n (Zpos 1)) (BinInt.Z.ggcd_correct_divisors n (Zpos 1)). 
rewrite BinInt.Z.gcd_1_r.
case (BinInt.Z.ggcd _ _)=> g ab /= ->; case ab=> a b [].
by rewrite !BinInt.Z.mul_1_l => <- <-.
Qed.

Lemma Z_ggcd_coprime a b :
  let '(g, (a', b')) := BinInt.Z.ggcd a b in
  g <> Z0 -> coprime `|Z2int a'| `|Z2int b'|.
Proof.
move: (BinInt.Z.ggcd_gcd a b) (BinInt.Z.ggcd_correct_divisors a b).
case (BinInt.Z.ggcd _ _)=> g ab; case ab=> a' b' /= Hg [] Ha Hb Pg.
rewrite /coprime; apply/eqP /Znat.Nat2Z.inj; rewrite -ZgcdE' /=.
suff ->: a' = (BinInt.Z.div a g).
{ suff ->: b' = (BinInt.Z.div b g); [by apply BinInt.Z.gcd_div_gcd|].
  by rewrite Hb BinInt.Z.mul_comm Zdiv.Z_div_mult_full. }
by rewrite Ha BinInt.Z.mul_comm Zdiv.Z_div_mult_full.
Qed.

Lemma Z2int_lcm x y : BinInt.Z.le Z0 x -> BinInt.Z.le Z0 y ->
  Z2int (BinInt.Z.lcm x y) = lcmn `|Z2int x| `|Z2int y|.
Proof.
case: x => [|x|//] _; [by rewrite /= lcm0n|].
case: y => [|y|//] _; [by rewrite /= lcmn0|].
rewrite /BinInt.Z.lcm Z2int_abs Z2int_mul Z2int_div //.
rewrite ZgcdE' abszM; apply: f_equal; apply/eqP.
rewrite -(@eqn_pmul2r (gcdn `|Z2int (Zpos x)| `|Z2int (Zpos y)|)).
{ rewrite gcdn_gt0; apply/orP; left; rewrite absz_gt0 /= eqz_nat.
  exact/lt0n_neq0/ssrnat.ltP/Pos2Nat.is_pos. }
rewrite muln_lcm_gcd.
rewrite -(absz_nat (gcdn _ _)) -mulnA -abszM.
rewrite Z2int_Z_of_nat /=.
  by rewrite intdiv.divzK // /mem /in_mem /intdiv.dvdz /= dvdn_gcdr.
Qed.

Lemma Z2int_Zpos_neq0 x: Z2int (Zpos x) != 0%R.
Proof. 
rewrite /=; apply/negP=> /eqP; case=> E.
by move/ssrnat.ltP: (Pos2Nat.is_pos x); rewrite E.
Qed.

Lemma Z2int_Qred n d :
  ((Z2int (QArith_base.Qnum (Qreduction.Qred (QArith_base.Qmake n d))))%:Q /
    (Pos.to_nat (QArith_base.Qden (Qreduction.Qred (QArith_base.Qmake n d))))%:Q
   = (Z2int n)%:Q / (Z2int (Zpos d))%:Q)%R.
Proof.
rewrite -(fracqE (Z2int n, Z2int (Zpos d))) -[RHS]divq_num_den.
rewrite /Qreduction.Qred.
move: (BinInt.Z.ggcd_gcd n (Zpos d)) (BinInt.Z.ggcd_correct_divisors n (Zpos d)).
move: (Z_ggcd_coprime n (Zpos d)).
case: BinInt.Z.ggcd => g [n' d'] /=.
case: g => [|g|g].
{ by move=> _ _ [_]; rewrite BinInt.Z.mul_0_l. }
{ move=> coprime_n'_d' => _ [->].
  rewrite (nat_of_pos_Z_to_pos d) => /[dup] posd' ->.
  have d'n0 : (`|Z2int d'| != 0)%R.
  { rewrite Num.Theory.normr_eq0.
    case: d' posd' {coprime_n'_d'} => // d' _.
    exact: Z2int_Zpos_neq0. }
  rewrite !Z2int_mul abszM PoszM gez0_abs; [by rewrite -[0%R]/(Z2int Z0) Z2int_le|].
  rewrite fracqMM ?Posz_nat_of_pos_neq0 ?abszE; first exact: Z2int_Zpos_neq0.
  move: (@valq_frac (Z2int n', `|Z2int d'|%R) d'n0).
  rewrite scalqE // GRing.mul1r => [[neq deq]].
  have -> : Pos.to_nat (BinInt.Z.to_pos d') = `|Z2int d'|%R :> ssrint.int.
  { rewrite nat_of_pos_Z_to_pos BinInt.Z2Pos.id ?abszE //.
    by case: d' posd' {coprime_n'_d' d'n0 neq deq}. }
  rewrite [X in (X%:~R / _)%R]neq [X in (_ / X%:~R)%R]deq.
  rewrite (_ : gcdn _ _ = 1%nat) ?GRing.mul1r //; exact/eqP/coprime_n'_d'. }
by move: (BinInt.Z.gcd_nonneg n (Zpos d)) => + _ => /[swap] <-.
Qed.

End Misc.

Section BigQRat.

Definition bigQ_to_rat (bq : bigQ) : rat :=
  let q := Qreduction.Qred [bq]%bigQ in
  ((Z2int (QArith_base.Qnum q))%:Q / (Z2int (Zpos (QArith_base.Qden q)))%:Q)%R.

Definition rat_to_bigQ (q : rat) : bigQ :=
  let n := BigZ.of_Z (int2Z (numq q)) in
  let d := BigN.N_of_Z (int2Z (denq q)) in
  (n # d)%bigQ.

Lemma bigQ_to_ratK: forall x : bigQ, x = rat_to_bigQ (bigQ_to_rat x).
Proof.
Admitted.


Lemma rat_to_bigQK: forall x : rat, bigQ_to_rat (rat_to_bigQ x) = x.
Proof.
Admitted.

Trakt Add Embedding bigQ rat bigQ_to_rat rat_to_bigQ bigQ_to_ratK rat_to_bigQK.

End BigQRat.