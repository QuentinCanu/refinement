(* -------------------------------------------------------------------- *)
From Coq      Require Import Uint63 BinNat.
From mathcomp Require Import all_ssreflect all_algebra.
Require Import extra_misc.
From Trakt Require Import Trakt.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

(* -------------------------------------------------------------------- *)
Import Order.Theory.

(* -------------------------------------------------------------------- *)
Notation int63 := PrimInt63.int.
Coercion int63_to_nat (x : int63) : nat :=
  BinInt.Z.to_nat (to_Z x).

Definition wB_nat (x : nat) := (BinInt.Z.lt (BinInt.Z.of_nat x) wB).
Definition int63_threshold := locked (2 ^ Uint63.size).

Lemma int63_threshold0 : (int63_threshold > 0).
Proof.
by rewrite /int63_threshold; unlock.
Qed.

Lemma int63_threshold1 : (int63_threshold > 1).
Proof.
by rewrite /int63_threshold; unlock.
Qed.

Definition nat_to_int63 (x : nat) : int63 := of_Z (BinInt.Z.of_nat x).
Definition max_int63_ := nat_to_int63 (predn (int63_threshold)).

Lemma wB_natE (x : nat): wB_nat x <-> (x < int63_threshold).
Proof.
suff: wB = BinInt.Z.of_nat (int63_threshold).
- by rewrite /wB_nat=> ->; split;
    [move/Znat.Nat2Z.inj_lt/ssrnat.ltP|move/ssrnat.ltP/Znat.Nat2Z.inj_lt].
rewrite /wB /int63_threshold -Zpower.two_power_nat_equiv; unlock.
elim: Uint63.size=> //= n IHn.
rewrite expnS Zpower.two_power_nat_S IHn.
have ->: (Zpos (xO 1%AC)) = BinInt.Z.of_nat 2 by [].
by rewrite -Znat.Nat2Z.inj_mul.
Qed.

Lemma ltin i j: (i <? j)%uint63 = (i < j)%nat.
Proof.
apply/idP/idP.
- move/ltbP/Znat.Z2Nat.inj_lt.
  case: (to_Z_bounded i) (to_Z_bounded j)=> + _ [+ _] h.
  by move: h => /[apply] /[apply] /ssrnat.ltP.
- move/ssrnat.ltP=> h; apply/ltbP/Znat.Z2Nat.inj_lt=> //.
  + by case: (to_Z_bounded i).
  + by case: (to_Z_bounded j).
Qed.
  
Lemma lein i j: (i <=? j)%uint63 = (i <= j)%nat.
Proof.
apply/idP/idP.
- move/lebP/Znat.Z2Nat.inj_le.
  case: (to_Z_bounded i) (to_Z_bounded j)=> + _ [+ _] h.
    by move: h => /[apply] /[apply] /ssrnat.leP.
- move/ssrnat.leP=> h; apply/lebP/Znat.Z2Nat.inj_le=> //.
  + by case: (to_Z_bounded i).
  + by case: (to_Z_bounded j).
Qed.

Lemma wB_nat_int63 (x : int63) : wB_nat x.
Proof.
rewrite /wB_nat /int63_to_nat. 
by case: (to_Z_bounded x)=> ??; rewrite Znat.Z2Nat.id.
Qed.

Lemma int63_thresholdP (x : int63) : x < int63_threshold.
Proof. exact/wB_natE/wB_nat_int63. Qed.

Lemma int63_to_natK : cancel int63_to_nat nat_to_int63.
Proof. 
move=> x; rewrite /nat_to_int63 /int63_to_nat.
rewrite Znat.Z2Nat.id ?of_to_Z //.
by case: (to_Z_bounded x).
Qed.

Lemma nat_to_int63K : {in gtn int63_threshold, cancel nat_to_int63 int63_to_nat}.
Proof.
move=> y; rewrite inE=> /wB_natE y_lt.
rewrite /int63_to_nat /nat_to_int63 of_Z_spec.
rewrite Zdiv.Zmod_small ?Znat.Nat2Z.id //; split=> //.
exact: Zorder.Zle_0_nat.
Qed.

Lemma int63_to_nat_inj: injective int63_to_nat.
Proof. by move=> i j /(congr1 nat_to_int63); rewrite !int63_to_natK. Qed.

Lemma nat_to_int63_inj: {in gtn int63_threshold &, injective nat_to_int63}.
Proof. by move=> ???? /(congr1 int63_to_nat); rewrite !nat_to_int63K. Qed.

(* -------------------------------------------------------------------- *)

Definition int63_eqMixin := CanEqMixin int63_to_natK.
Canonical  int63_eqType  := EqType int63 int63_eqMixin.

Definition int63_choiceMixin := CanChoiceMixin int63_to_natK.
Canonical  int63_choiceType  := ChoiceType int63 int63_choiceMixin.

Definition int63_countMixin := CanCountMixin int63_to_natK.
Canonical  int63_countType  := CountType int63 int63_countMixin.

(* -------------------------------------------------------------------- *)
Definition enum_int63 := map nat_to_int63 (iota 0 int63_threshold).

Lemma enum_int63P : Finite.axiom enum_int63.
Proof.
move=> x; rewrite count_uniq_mem; last apply/eqP; rewrite ?eqb1.
- rewrite map_inj_in_uniq ?iota_uniq //.
  move=> i j; rewrite ?mem_iota add0n !leq0n /= => ??.
  by apply/nat_to_int63_inj; rewrite inE.
- apply/(nthP 0%uint63); exists x; rewrite ?size_map ?size_iota;
    first exact/int63_thresholdP.
  rewrite (nth_map 0) ?size_iota; first exact/int63_thresholdP.
  rewrite nth_iota ?add0n; first exact/int63_thresholdP.
  by rewrite int63_to_natK.
Qed.

Definition int63_finMixin := FinMixin enum_int63P.
Canonical  int63_fint63ype  := FinType int63 int63_finMixin.

(* ---------------------------------------------------------------------- *)

Definition imin (i j : int63) := if (i <? j)%uint63 then i else j.
Definition imax (i j : int63) := if (i <? j)%uint63 then j else i.

Program Definition int63_orderMixin :=
  @LeOrderMixin _ leb ltb imin imax _ _ _ _ _ _.

Next Obligation. by rewrite ltin lein ltn_neqAle eq_sym. Qed.
Next Obligation. move=> ??; rewrite !lein => ?; exact/int63_to_nat_inj/anti_leq. Qed.
Next Obligation. move=> ???; rewrite !lein; exact/leq_trans. Qed.
Next Obligation. by move=> ??; rewrite !lein leq_total. Qed.

Canonical int63_porderType :=
  POrderType Order.NatOrder.nat_display int63 int63_orderMixin.

(* ------------------------------------------------------------------------ *)

Lemma eqEint63 (x y : int63): (x =? y)%uint63 = (x == y).
Proof. by apply/idP/idP; [move/eqb_spec=> -> | move/eqP=> ->; apply/eqb_spec]. Qed. 

Lemma leEint63 : <=%O = leb.
Proof. by []. Qed.

Lemma ltEint63 : <%O = ltb.
Proof. by []. Qed.

Lemma le0int63 (x : int63) : (0%uint63 <= x)%O.
Proof. by rewrite leEint63 lein leq0n. Qed.

Lemma leint63T (x : int63) : (x <= max_int63_)%O.
Proof.
rewrite leEint63 lein /max_int63_ nat_to_int63K ?inE ?ltn_predL ?int63_threshold0 //.
move: (int63_thresholdP x); rewrite -[X in x < X](prednK int63_threshold0).
exact/ltnSE.
Qed.

Canonical int63_latticeType := LatticeType int63 int63_orderMixin.
Canonical int63_bLatticeType := BLatticeType int63 (BottomMixin le0int63).
Canonical int63_tLatticeType := TBLatticeType int63 (TopMixin leint63T).
Canonical int63_distrLatticeType := DistrLatticeType int63 int63_orderMixin.
Canonical int63_bDistrLatticeType := [bDistrLatticeType of int63].
Canonical int63_tbDistrLatticeType := [tbDistrLatticeType of int63].
Canonical int63_orderType := OrderType int63 int63_orderMixin.
Canonical int63_finLatticeType := [finLatticeType of int63].
Canonical int63_finDistrLatticeType := [finDistrLatticeType of int63].
Canonical int63_finOrderType := [finOrderType of int63].
(*
Canonical int63_bPOrderType := BPOrderType int63 (BottomMixin le0int63).
Canonical int63_tPOrderType := TPOrderType int63 (TopMixin leint63T).
Canonical int63_tbPOrderType := [tbPOrderType of int63].
Canonical int63_meetSemilatticeType := MeetSemilatticeType int63 int63_orderMixin.
Canonical int63_bMeetSemilatticeType := [bMeetSemilatticeType of int63].
Canonical int63_tMeetSemilatticeType := [tMeetSemilatticeType of int63].
Canonical int63_tbMeetSemilatticeType := [tbMeetSemilatticeType of int63].
Canonical int63_joinSemilatticeType := JoinSemilatticeType int63 int63_orderMixin.
Canonical int63_bJoinSemilatticeType := [bJoinSemilatticeType of int63].
Canonical int63_tJoinSemilatticeType := [tJoinSemilatticeType of int63].
Canonical int63_tbJoinSemilatticeType := [tbJoinSemilatticeType of int63].
Canonical int63_latticeType := [latticeType of int63].
Canonical int63_bLatticeType := [bLatticeType of int63].
Canonical int63_tLatticeType := [tLatticeType of int63].
Canonical int63_tbLatticeType := [tbLatticeType of int63].
Canonical int63_distrLatticeType := DistrLatticeType int63 int63_orderMixin.
Canonical int63_bDistrLatticeType := [bDistrLatticeType of int63].
Canonical int63_tDistrLatticeType := [tDistrLatticeType of int63].
Canonical int63_tbDistrLatticeType := [tbDistrLatticeType of int63].
Canonical int63_orderType := OrderType int63 int63_orderMixin.
Canonical int63_bOrderType := [bOrderType of int63].
Canonical int63_tOrderType := [tOrderType of int63].
Canonical int63_tbOrderType := [tbOrderType of int63].
Canonical int63_finPOrderType := [finPOrderType of int63].
Canonical int63_finBPOrderType := [finBPOrderType of int63].
Canonical int63_fint63POrderType := [fint63POrderType of int63].
Canonical int63_fint63BPOrderType := [fint63BPOrderType of int63].
Canonical int63_finMeetSemilatticeType := [finMeetSemilatticeType of int63].
Canonical int63_finBMeetSemilatticeType := [finBMeetSemilatticeType of int63].
Canonical int63_finJoinSemilatticeType := [finJoinSemilatticeType of int63].
Canonical int63_fint63JoinSemilatticeType := [fint63JoinSemilatticeType of int63].
Canonical int63_finLatticeType :=  [finLatticeType of int63].
Canonical int63_fint63BLatticeType :=  [fint63BLatticeType of int63].
Canonical int63_finDistrLatticeType :=  [finDistrLatticeType of int63].
Canonical int63_fint63BDistrLatticeType :=  [fint63BDistrLatticeType of int63].
Canonical int63_finOrderType := [finOrderType of int63].
Canonical int63_fint63BOrderType := [fint63BOrderType of int63].
*)

(* -------------------------------------------------------------------- *)

Section int63Theory.

Definition lteEint63 := (ltEint63, leEint63).

Lemma leEint63_nat (x y : int63) : (x <= y)%O = (x <= y)%nat.
Proof. by rewrite leEint63 lein. Qed.

Lemma ltEint63_nat (x y : int63) : (x < y)%O = (x < y)%nat.
Proof. by rewrite ltEint63 ltin. Qed.

End int63Theory.

(* -------------------------------------------------------------------- *)
Section SuccTheory.


Lemma succ_int63E (c : int63) :
  (c < max_int63_)%O -> Uint63.succ c = c.+1 :> nat.
Proof. 
rewrite ltEint63_nat nat_to_int63K ?inE ?ltn_predL ?int63_threshold0 //.
move=> c_int63; rewrite /int63_to_nat succ_spec Zdiv.Zmod_small; last first; try split.
- rewrite Znat.Z2Nat.inj_add; [by case: (to_Z_bounded c)|exact:BinInt.Z.le_0_1|].
  by rewrite /= Pnat.Pos2Nat.inj_1 PeanoNat.Nat.add_1_r.
- apply/Ztac.add_le; [by case: (to_Z_bounded c)|exact:BinInt.Z.le_0_1].
- move: c_int63; rewrite /int63_threshold; unlock.
  rewrite /int63_to_nat -ltnS prednK ?expn_gt0 //.
  move/ssrnat.ltP/Znat.inj_lt; rewrite /wB Znat.Nat2Z.inj_succ.
  rewrite Znat.Z2Nat.id; first by case: (to_Z_bounded c).
  rewrite BinInt.Z.add_1_r -Zpower.two_power_nat_equiv.
  suff ->: BinInt.Z.of_nat (2 ^ Uint63.size) = Zpower.two_power_nat Uint63.size by [].
  elim: Uint63.size=> //= n; rewrite expnS Znat.Nat2Z.inj_mul.
  by rewrite Zpower.two_power_nat_S => ->.
Qed.

Lemma succ_int63_max:
  Uint63.succ max_int63_ = 0%uint63.
Proof.
rewrite /max_int63_ /int63_threshold; apply/to_Z_inj=> /=.
rewrite to_Z_0 succ_spec /nat_to_int63 of_Z_spec.
rewrite Zdiv.Zplus_mod_idemp_l.
unlock; rewrite Znat.Nat2Z.inj_pred_max -BinInt.Z.add_max_distr_r.
rewrite [X in BinInt.Z.max X _]BinInt.Z.add_0_l.
rewrite BinInt.Z.add_pred_l BinInt.Z.add_1_r BinInt.Z.pred_succ.
rewrite /wB.
have ->: BinInt.Z.of_nat (2 ^ Uint63.size) = Zpower.two_power_nat Uint63.size.
  - elim: Uint63.size=> //= n; rewrite expnS Znat.Nat2Z.inj_mul.
    by rewrite Zpower.two_power_nat_S => ->.
by rewrite Zpower.two_power_nat_equiv BinInt.Z.max_r ?Zdiv.Z_mod_same_full.
Qed.

Lemma succ_int63P (c : int63) :
  (c < max_int63_)%O <-> Uint63.succ c = c.+1 :> nat.
Proof.
split; first exact: succ_int63E.
apply/contra_eqT=> /negPf c_max.
move: (lex1 c); rewrite le_eqVlt c_max orbF=> /eqP -> /=.
by rewrite succ_int63_max.
Qed.

Lemma succ_int63_ltE (a b : int63) :
  (a < b)%O -> Uint63.succ a = a.+1 :> nat.
Proof.
move=> ab.
move: (lt_le_trans ab (lex1 _)).
exact: succ_int63E.
Qed.

Lemma succ_int63_mono (a b : int63):
  (a < max_int63_)%O -> (b < max_int63_)%O -> (a <= b)%O = (succ a <= succ b)%O.
Proof.
by move=> a_max b_max; rewrite !leEint63_nat !succ_int63E.
Qed.

Lemma succ_int63_lt_mono (a b x y: int63):
  (a < x)%O -> (b < y)%O -> (a <= b)%O = (succ a <= succ b)%O.
Proof.
move=> a_x b_y.
move: (lt_le_trans a_x (lex1 _)) (lt_le_trans b_y (lex1 _)).
exact: succ_int63_mono.
Qed.

Lemma succ_int63_morph_lt (a b : int63):
  (b < max_int63_)%O -> (a < b)%O -> (succ a < succ b)%O.
Proof. by move=> b_max /[dup] a_b; rewrite !ltEint63_nat !succ_int63E //; apply/(lt_trans a_b). Qed.

Lemma succ_int63_max_lt (a b : int63):
  (a < max_int63_)%O -> (b < max_int63_)%O ->
  Order.max (succ a) (succ b) = succ (Order.max a b).
Proof.
move=> a_max b_max; case: leP.
- by rewrite -succ_int63_mono //; case: leP.
- by move/ltW; rewrite -succ_int63_mono //; case: leP.
Qed.

Lemma succ_int63_lt_max (a b x y: int63):
  (a < x)%O -> (b < y)%O ->
  Order.max (succ a) (succ b) = succ (Order.max a b).
Proof.
move=> a_x b_y.
move: (lt_le_trans a_x (lex1 _)) (lt_le_trans b_y (lex1 _)).
exact: succ_int63_max_lt.
Qed.

Lemma nat_to_int63S n : succ (nat_to_int63 n) = nat_to_int63 n.+1.
Proof.
apply/to_Z_inj; rewrite succ_spec /nat_to_int63.
rewrite Znat.Nat2Z.inj_succ -BinInt.Z.add_1_r !of_Z_spec.
exact/Zdiv.Zplus_mod_idemp_l.
Qed.

Lemma ltiS_ltVeqS (x y : int63) : (y < max_int63_)%O -> (x < succ y)%O -> (x < y)%O \/ x = y.
Proof.
move=> y_max; rewrite !ltEint63_nat succ_int63E // ltnS leq_eqVlt.
by case/orP=> [/eqP/int63_to_nat_inj ->|->]; [right|left].
Qed.

Lemma ltiSi (i : int63): (i < max_int63_)%O -> (i < succ i)%O.
Proof. by move=> ?; rewrite ltEint63_nat succ_int63E. Qed.

End SuccTheory.

(* -------------------------------------------------------------------- *)

Section PredTheory.

Lemma pred_int63E (x : int63) : (0 < x)%O -> Uint63.pred x = x.-1 :> nat.
Proof.
move=> x0; rewrite /int63_to_nat pred_spec Zdiv.Zmod_small; last first; try split.
- rewrite Znat.Z2Nat.inj_sub; first exact:BinInt.Z.le_0_1.
  by rewrite /= Pnat.Pos2Nat.inj_1 PeanoNat.Nat.sub_1_r.
- move: x0; rewrite ltEint63_nat /int63_to_nat=> /ssrnat.ltP/Znat.Z2Nat.inj_lt.
  rewrite !to_Z_0 => /(_ (BinInt.Z.le_refl _)).
  case: (to_Z_bounded x)=> Z0_x _ /(_ Z0_x) Z0_ltx.
  exact/ZMicromega.lt_le_iff.
- apply/BinInt.Z.lt_sub_lt_add_r.
  case: (to_Z_bounded x)=> _; move/BinInt.Z.lt_trans; apply.
  exact/BinInt.Z.lt_add_pos_r/BinInt.Z.lt_0_1.
Qed.

Lemma pred_succ (x : int63) : Uint63.pred (Uint63.succ x) = x.
Proof.
apply/to_Z_inj; rewrite pred_spec succ_spec Zdiv.Zminus_mod_idemp_l.
rewrite BinInt.Z.add_simpl_r.
by move/Zdiv.Zmod_small: (to_Z_bounded x).
Qed.

End PredTheory.

Section SubTheory.

Lemma sub_int63E x y: (x < y)%O -> 
  int63_to_nat (y - x) = int63_to_nat y - int63_to_nat x.
Proof.
rewrite ltEint63 /int63_to_nat sub_spec /=.
move/ltbP=> xy; rewrite Zdiv.Zmod_small; first split.
- exact/Zorder.Zle_minus_le_0/BinInt.Z.lt_le_incl.
- case: (to_Z_bounded y)=> _ /(@BinInt.Z.sub_lt_mono_r _ _ (to_Z x)).
  move/BinInt.Z.lt_le_trans; apply; apply/BinInt.Z.le_sub_nonneg.
  by case: (to_Z_bounded x).
- by rewrite Znat.Z2Nat.inj_sub //; case: (to_Z_bounded x).
Qed.

End SubTheory.

Section AddTheory.

Lemma add_int63E x y: int63_to_nat x + int63_to_nat y \in gtn int63_threshold ->
  int63_to_nat (x + y)%uint63 = x + y.
Proof.
move=> xy_max; rewrite /int63_to_nat; rewrite add_spec.
move/wB_natE: xy_max; rewrite /wB_nat Znat.Nat2Z.inj_add.
rewrite /int63_to_nat !Znat.Z2Nat.id; [by case: (to_Z_bounded x)|by case: (to_Z_bounded y)|].
move=> xy_max.
rewrite Zdiv.Zmod_small; first (split=> //; apply/BinInt.Z.add_nonneg_nonneg; [by case: (to_Z_bounded x)|by case: (to_Z_bounded y)]).
rewrite Znat.Z2Nat.inj_add //; [by case: (to_Z_bounded x)|by case: (to_Z_bounded y)].
Qed.

End AddTheory.

Section Extraint63Theory.

Lemma nat_to_int63_le (n : nat): ((nat_to_int63 n) <= n)%nat.
Proof.
rewrite /nat_to_int63 /int63_to_nat of_Z_spec -[X in (_ <= X)%nat](Znat.Nat2Z.id n).
apply/ssrnat.leP/Znat.Z2Nat.inj_le; try exact: Zorder.Zle_0_nat.
- move/BinInt.Z.mod_pos_bound: wB_pos=> /(_ (BinInt.Z.of_nat n)).
  by case.
- apply/Zdiv.Zmod_le; [exact: wB_pos|exact:Zorder.Zle_0_nat].
Qed.

End Extraint63Theory.

(* -------------------------------------------------------------------- *)


Section IRange.

Definition irange (i j : int63) : seq int63 :=
  sort Order.le (enum [set x | (i <= x)%O && (x < j)%O ]).

Lemma irangee (i : int63): irange i i = [::].
Proof.
rewrite /irange.
suff ->: ([set x | (i <= x)%O && (x < i)%O] = set0) by rewrite enum_set0.
by apply/setP=> z; rewrite !inE le_lt_asym.
Qed.

Lemma uniq_irange i j : uniq (irange i j).
Proof. by rewrite sort_uniq enum_uniq. Qed.

Lemma sorted_irange i j : sorted Order.lt (irange i j).
Proof. by rewrite sort_lt_sorted enum_uniq. Qed.

Lemma mem_irangeE i j x :
  (x \in irange i j) = (i <= x)%O && (x < j)%O.
Proof. by rewrite mem_sort mem_enum inE. Qed.

Lemma irange_cons i j: (i < j)%O -> irange i j = i :: irange (succ i) j.
Proof.
move=> ij; apply/le_sorted_eq.
- exact/sort_sorted/le_total.
- rewrite /= path_sortedE; first exact/le_trans.
  apply/andP; split; last exact/sort_sorted/le_total.
  apply/allP=> z; rewrite mem_irangeE=> /andP [+ _].
  rewrite !leEint63_nat (succ_int63_ltE ij); exact: ltnW.
- apply/uniq_perm; rewrite /= ?uniq_irange // ?andbT.
  + by rewrite mem_irangeE ij andbT leEint63_nat (succ_int63_ltE ij) ltnn.
  + move=> z; rewrite in_cons !mem_irangeE.
    case/boolP: (z == i)=> [/eqP ->|]; rewrite ?lexx ?ij //=.
    move=> z_n_i; congr andb; rewrite !leEint63_nat (succ_int63_ltE ij).
    rewrite leq_eqVlt eq_sym.
    case/boolP: (int63_to_nat z == int63_to_nat i)=> //=.
    by move/eqP=> /int63_to_nat_inj /eqP; rewrite (negPf z_n_i).
Qed.



Lemma irange_cat i j k: (i <= j)%O -> (j <= k)%O ->
  irange i k = irange i j ++ irange j k.
Proof.
rewrite !le_eqVlt; case/orP=> [/eqP ->|]; rewrite ?irangee //.
move=> ij; case/orP=> [/eqP ->|]; rewrite ?irangee ?cats0 //.
move=> jk; apply/le_sorted_eq.
- exact/sort_sorted/le_total.
- apply/sorted_cat; first exact/le_trans; split; try exact/sort_sorted/le_total.
  apply/allrelP=> x y; rewrite !mem_irangeE.
  case/andP=> _ /ltW /le_trans + /andP [+ _].
  exact.
- apply/uniq_perm; first exact/uniq_irange.
  + rewrite cat_uniq !uniq_irange /= andbT -all_predC.
    apply/allP=> x /=; rewrite !mem_irangeE negb_and leNgt.
    by case/andP=> ->; rewrite orbT.
  + move=> x; rewrite mem_cat !mem_irangeE.
    case: (leP j x)=> /=; rewrite ?andbF ?orbF ?andbT /=.
    * by move/ltW: ij => /le_trans /[apply] -> /=.
    * by move: jk=> /[swap] /lt_trans /[apply] ->; rewrite andbT.
Qed.
  

  
Definition irange0 (j : int63) : seq int63 := irange 0 j.

Lemma irange0_iota j: irange0 j = map nat_to_int63 (iota 0 j). 
Proof.
apply/lt_sorted_eq; first exact: sorted_irange.
- rewrite sorted_map.
  case E: (int63_to_nat j)=> [|j'] //=.
  apply/(pathP 0%nat)=> i.
  rewrite size_iota=> /[dup] i_j'; rewrite -ltnS -E => /ltnW i_j.
  case: i i_j' i_j; first by (move=> /= ??; rewrite nth_iota).
  move=> n ?? /=; rewrite !nth_iota //; first exact/ltnW.
  rewrite !add1n ltEint63_nat !nat_to_int63K // inE.
  + apply/(@ltn_trans j)=> //; exact: int63_thresholdP.
  + apply/(@leq_ltn_trans j)=> //; exact: int63_thresholdP.
- move=> x; rewrite mem_irangeE le0x /=.
  apply/idP/idP.
  + move=> x_j; apply/mapP; exists (int63_to_nat x); rewrite ?int63_to_natK //.
    by rewrite mem_iota add0n leq0n /=; rewrite -ltEint63_nat.
  + case/mapP=> y; rewrite mem_iota leq0n add0n /=; move=> y_j ->.
    rewrite ltEint63_nat nat_to_int63K // inE.
    apply/(@ltn_trans j)=> //; exact: int63_thresholdP.
Qed.

Lemma size_irange0 j: seq.size (irange0 j) = j.
Proof. by rewrite irange0_iota size_map size_iota. Qed.

Lemma size_irange i j: seq.size (irange i j) = (j - i)%nat.
Proof.
case: (leP i j).
- move=> ij.
  move/(congr1 size): (irange_cat (le0x i) ij); rewrite size_cat !size_irange0.
  by move=> ->; rewrite addKn.
- move=> /[dup] ij; rewrite ltEint63_nat=> /ltnW; rewrite -subn_eq0=> /eqP ->; apply/eqP/nilP.
  move: (mem_irangeE i j); case: (irange i j)=> //= a l.
  move=> /(_ a); rewrite in_cons eqxx /= => /esym/andP [] /le_lt_trans /[apply].
  by move/ltW; rewrite leNgt ij.
Qed.

Lemma nth_irange0 (j : int63) k:
  (k < j)%nat -> nth 0%uint63 (irange0 j) k = nat_to_int63 k.
Proof.
move=> kj; rewrite irange0_iota (nth_map 0) ?size_iota //.
by rewrite nth_iota.
Qed.

Lemma nth_irange (i j : int63) k:
  (k < j - i)%nat -> nth 0%uint63 (irange i j) k = nat_to_int63 (k + i).
Proof.
move=> kji; move: (leq_ltn_trans (leq0n k) kji); rewrite subn_gt0.
rewrite -ltEint63_nat=> /ltW ij.
move: (irange_cat (le0x i) ij)=> /(congr1 (fun s=> nth 0%uint63 s (k + i))).
rewrite nth_irange0 addnC -?ltn_subRL // nth_cat size_irange0.
by rewrite ltnNge leq_addr /= addKn => ->.
Qed.

Lemma irange0_succ (i : int63):
  (i < max_int63_)%O -> irange0 (succ i) = rcons (irange0 i) i.
Proof.
move=> i_max; rewrite !irange0_iota succ_int63E // iotaS_rcons add0n map_rcons.
by rewrite int63_to_natK.
Qed. 

End IRange.

Module IFold.

Fixpoint ifold_ {T : Type} (n : nat) (f : int63 -> T -> T) (i M : int63) (x : T) :=
  if (i =? M)%uint63 then (i, x) else
    if n is n.+1 then
      let: (i, x) := ((i + 1)%uint63, f i x) in
      let: (i, x) := ifold_ n f i M x in
      let: (i, x) := ifold_ n f i M x in
      (i, x)
    else (i, x).

Definition ifold {T : Type} (f : int63 -> T -> T) (i : int63) (x : T) :=
  (ifold_ Uint63.size f 0 i x).2.

Definition iall (f : int63 -> bool) (i : int63):=
  (ifold (fun i acc=> acc && f i) i true).

(* -------------------------------------------------------------------- *)
Definition iofold_ {T U: Type} (n : nat) (f : int63 -> T -> T + U) (i M : int63) (x : T + U) :=
  ifold_ n (fun i r=> if r is inl a then f i a else r) i M x.
(*TODO : Replace by an actual int63erruption function*)
  
Definition iofold {T U: Type} (f : int63 -> T -> T + U) (i : int63) (x : T + U):=
  (iofold_ Uint63.size f 0 i x).2.

End IFold.
Section Ifold.

Lemma ifold_E {S : Type} (n : nat) (f : int63 -> S -> S) (i M : int63) (x : S):
  (i <= M)%nat ->
  let: j := ((int63_to_nat i) + (2 ^ n) - 1)%nat in
  let: j' := if (j <= int63_to_nat M)%nat then nat_to_int63 j else M in
  IFold.ifold_ n f i M x = (j', foldl (fun s t=> f t s) x (irange i j')).
Proof.
elim: n i x=> /= [i x | n IHn i x].
- rewrite expn0 addnK; case: ifP=> [/eqb_spec ->|]; rewrite ?leqnn ?int63_to_natK ?irangee //=.
  by move=> _ ->; rewrite irangee.
- have leq_pow: forall y k, (y + 2 ^ k.+1 - 1 <= y)%nat = false.
  + move=> y k; rewrite leqNgt ltn_subRL addnC ltn_add2l.
    by apply/negbF; rewrite -{1}(expn0 2) ltn_exp2l.
  move=> iM; case: ifP=> [/eqb_spec ->|]; rewrite ?leq_pow ?irangee //.
  move/eqb_false_spec/eqP=> inM.
  have inM_nat: (int63_to_nat i != int63_to_nat M) by move: inM; apply/contra_neq=> /int63_to_nat_inj.
  move: iM; rewrite leq_eqVlt (negPf inM_nat) /= -ltEint63_nat => SiM.
  move: (IHn (Uint63.succ i) (f i x)); rewrite (succ_int63_ltE SiM) -ltEint63_nat=> /(_ SiM) ->.
  rewrite -addnBAC // subSS subn0.
  set N1 := (_ + 2 ^ n)%nat.
  case: ifP; last first. 
  + rewrite IHn /N1 //; case: n {IHn N1}; rewrite ?expn0 ?addn1 -?ltEint63_nat ?SiM //.
    move=> n N1_leq; rewrite leq_pow.
    suff ->: (i + 2 ^ n.+2 - 1 <= M)%nat = false by rewrite (irange_cons SiM) irangee.
    move: N1_leq; apply/contraFF=> /(leq_trans _); apply.
    rewrite -addnBA ?expn_gt0 // leq_add2l [in X in (_ <= X)%nat]expnS.
    elim: n; rewrite ?expn1 // => n; rewrite -(@leq_pmul2l 2) // -expnS.
    move/leq_trans; apply; rewrite mulnBr !mul2n ?doubleS ?double0.
    exact/leq_sub2l.
  + move=> N1_M; have N1_thre: N1 \in gtn int63_threshold by rewrite !inE; exact/(leq_ltn_trans N1_M)/int63_thresholdP.
    rewrite IHn ?nat_to_int63K //; set N2 := (i + 2 ^ n.+1 - _)%nat.
    have N1_N2_eq: (N1 + 2 ^ n - 1)%nat = N2.
    * rewrite -addnBA ?expn_gt0 // -addnA addnBA ?expn_gt0 // addnn -mul2n -expnS.
      by rewrite addnBA ?expn_gt0.
    have N1_N2_leq: (N1 <= N2)%nat by rewrite -N1_N2_eq -addnBA ?expn_gt0 // leq_addr.
    rewrite N1_N2_eq; congr pair; rewrite (@irange_cons i) /=.
      case: ifP=> // N2_M; rewrite ltEint63_nat ?nat_to_int63K ?inE; first apply/(leq_ltn_trans N2_M)/int63_thresholdP.
      rewrite /N2 -addnBA ?expn_gt0 // -ltn_psubLR ?subnn subn_gt0 -[X in (X < _)%nat](expn0 2); exact: ltn_exp2l.
    rewrite -foldl_cat -irange_cat //.
    * by rewrite leEint63_nat (succ_int63_ltE SiM) ?nat_to_int63K // -ltn_psubLR ?subnn expn_gt0.
    * rewrite leEint63_nat nat_to_int63K //; case: ifP=> // N2_M.
      rewrite ?nat_to_int63K ?inE //; exact/(leq_ltn_trans N2_M)/int63_thresholdP.
Qed.

Definition ifold {S : Type} (f : int63 -> S -> S) (M : int63) (x : S):=
  foldl (fun s t=> f t s) x (irange0 M).

Lemma ifoldE {S : Type} (f : int63 -> S -> S) (M : int63) (x : S):
  IFold.ifold f M x = ifold f M x.
Proof.
rewrite /IFold.ifold ifold_E ?leq0n //=.
move: (int63_thresholdP M); rewrite /int63_threshold; unlock.
rewrite add0n -add1n -leq_subRL ?expn_gt0 //.
rewrite leq_eqVlt ltnNge; case/orP=> [/eqP <-|]; rewrite ?leqnn ?int63_to_natK //.
by move/negPf => ->.
Qed.

Definition iall (f : int63 -> bool) (M : int63) := 
  all f (irange0 M).

Lemma iallE (f : int63 -> bool) (M : int63):
  IFold.iall f M = iall f M.
Proof. 
rewrite /IFold.iall ifoldE /ifold /iall.
elim/last_ind: (irange0 M)=> // t h IH.
by rewrite foldl_rcons all_rcons andbC IH.
Qed.

Definition iofold {T U : Type} (f : int63 -> T -> T + U) (M : int63) (x : T + U):=
  foldl (fun r i=> if r is inl t then f i t else r) x (irange0 M).

Lemma iofoldE {T U : Type} (f : int63 -> T -> T + U) (M : int63) (x : T + U):
  IFold.iofold f M x = iofold f M x.
Proof.
rewrite /IFold.iofold /IFold.iofold_.
rewrite ifold_E ?leq0n //.
move: (int63_thresholdP M); rewrite /int63_threshold; unlock.
rewrite add0n -add1n -leq_subRL ?expn_gt0 //.
rewrite leq_eqVlt ltnNge; case/orP=> [/eqP <-|]; rewrite ?leqnn ?int63_to_natK //.
by move/negPf=> -> /=.
Qed.

Lemma ifold_iter {T : Type} (f : T -> T) (n : int63) (x : T):
  ifold (fun _=> f) n x = iter n f x.
Proof.
rewrite /ifold irange0_iota.
elim: (int63_to_nat n)=> // k IH.
by rewrite iotaS_rcons add0n map_rcons foldl_rcons IH /=.
Qed.

End Ifold.

Section TraktTest.

(* T : int63; T' : nat; f : int63_to_nat; g : nat_to_int63 *)

Lemma int63_to_natK_sym: forall x : int63, x = nat_to_int63 (int63_to_nat x).
Proof. by move=> ?; rewrite int63_to_natK. Qed.

Trakt Add Embedding int63 nat
  int63_to_nat nat_to_int63 int63_to_natK_sym nat_to_int63K int63_thresholdP.

Lemma equality_trakt: forall x y : int63, (x =? y)%uint63 = (x == y)%nat.
Proof. exact/eqEint63. Qed.

Trakt Add Relation 2 nat (fun x y => (x =? y)%uint63) 
  (fun x y : nat => (x == y)%nat) equality_trakt.
Trakt Add Relation 2 nat (fun x y => (x <? y)%uint63)
  (fun x y : nat => (x < y)%nat) ltEint63_nat.
Trakt Add Relation 2 nat (fun x y => (x <=? y)%uint63)
  (fun x y : nat => (x <= y)%nat) leEint63_nat.

Definition I_K := 'Z_(int63_threshold).

Lemma Zp_trunc_KE: (Zp_trunc int63_threshold).+2 = int63_threshold.
Proof.
rewrite /Zp_trunc !prednK //;
  [rewrite ltn_predRL; exact:int63_threshold1|exact:int63_threshold0].
Qed.

Program Definition int63_to_I_K (x : int63) : I_K := @Ordinal _ (int63_to_nat x) _.
Next Obligation. rewrite Zp_trunc_KE; exact: int63_thresholdP. Qed.

Definition I_K_to_int63 (x : I_K):= nat_to_int63 x.

Lemma gof_int63: forall x : int63, x = I_K_to_int63 (int63_to_I_K x).
Proof.
by move=> x /=; rewrite /I_K_to_int63 /int63_to_I_K /= int63_to_natK.
Qed.

Lemma fog_int63: forall x : I_K, int63_to_I_K (I_K_to_int63 x) = x.
Proof.
move=> x; apply/val_inj=> /=; case: x=> x ? /=.
by rewrite nat_to_int63K //= inE -Zp_trunc_KE.
Qed.

Trakt Add Embedding int63 I_K int63_to_I_K I_K_to_int63 (gof_int63) (fog_int63).

Lemma int63_eq: forall x y : int63, (x =? y)%uint63 = 
  (int63_to_I_K x == int63_to_I_K y).
Proof. by move=> x y; rewrite eqEint63 -val_eqE /=. Qed.

Trakt Add Relation 2 (fun x y : int63 => (x =? y)%uint63)
  (fun x y : I_K => (x == y)) int63_eq.

Definition add_I_K (x y : I_K) : I_K := Zp_add x y.

Lemma int63_to_Z_ge0 (x : int63): BinInt.Z.le Z0 (to_Z x).
Proof. by case: (to_Z_bounded x). Qed.

Lemma wB_def: BinInt.Z.to_nat wB = int63_threshold.
Proof.
rewrite Znat.Z2Nat.inj_pow // Znat.Z2Nat.inj_pos Znat.Nat2Z.id.
rewrite Pnat.Pos2Nat.inj_xO Pnat.Pos2Nat.inj_1 multE muln1.
rewrite /int63_threshold; unlock.
elim: Uint63.size=> /=; first by rewrite expn0.
by move=> n ->; rewrite plusE addn0 expnS mul2n addnn.
Qed.

Lemma peano_modE m n: m %% n = PeanoNat.Nat.modulo m n.
Proof.
case: n=> [|n] //.
rewrite [in RHS](divn_eq m n.+1).
rewrite addnC PeanoNat.Nat.mod_add //.
rewrite PeanoNat.Nat.mod_small //.
by apply/ssrnat.ltP/ltn_pmod.
Qed.

Lemma int63_add: forall x y : int63,
  int63_to_I_K (x + y)%uint63 = add_I_K (int63_to_I_K x) (int63_to_I_K y).
Proof.
move=> x y; apply/val_inj=> /=.
rewrite /int63_to_nat Zp_trunc_KE add_spec.
rewrite Znat.Z2Nat.inj_mod //;
  first by (apply:BinInt.Z.add_nonneg_nonneg; exact:int63_to_Z_ge0).
rewrite Znat.Z2Nat.inj_add; try exact:int63_to_Z_ge0.
by rewrite wB_def plusE peano_modE.
Qed.

Trakt Add Symbol Uint63.add I_K add_I_K int63_add.

Definition mul_I_K (x y : I_K) : I_K :=
  Zp_mul x y.

Lemma int63_mul: forall x y : int63,
  int63_to_I_K (x * y)%uint63 = mul_I_K (int63_to_I_K x) (int63_to_I_K y).
Proof.
move=> x y; apply/val_inj=> /=; rewrite Zp_trunc_KE.
rewrite /int63_to_nat mul_spec Znat.Z2Nat.inj_mod;
  last rewrite wB_def peano_modE Znat.Z2Nat.inj_mul //.
- apply/Ztac.mul_le; exact: int63_to_Z_ge0.
- exact/BinInt.Z.lt_le_incl/wB_pos.
- exact: int63_to_Z_ge0.
- exact: int63_to_Z_ge0.
Qed.

Trakt Add Symbol Uint63.mul I_K mul_I_K int63_mul.

Lemma int63_0: int63_to_I_K 0%uint63 = (ord0 : I_K).
Proof. exact/val_inj. Qed.

Program Definition ord1 : I_K := @Ordinal _ 1 _.

Lemma int63_1: int63_to_I_K 1%uint63 = ord1.
Proof. exact/val_inj. Qed.

Trakt Add Symbol (0%uint63) I_K (ord0 : I_K) int63_0.
Trakt Add Symbol (1%uint63) I_K (ord1) int63_1.

Definition I_K_le (x y : I_K): bool := (x <= y)%nat.
Definition I_K_lt (x y : I_K): bool := (x < y)%nat.

Lemma int63_le: forall x y : int63,
  (x <=? y)%uint63 = I_K_le (int63_to_I_K x) (int63_to_I_K y).
Proof. by rewrite /I_K_le=> x y /=; rewrite -leEint63_nat. Qed.

Lemma int63_lt: forall x y : int63,
  (x <? y)%uint63 = I_K_lt (int63_to_I_K x) (int63_to_I_K y).
Proof. by rewrite /I_K_lt=> x y /=; rewrite -ltEint63_nat. Qed.

End TraktTest.
