(* -------------------------------------------------------------------- *)
From Coq      Require Import BinNat ZArith Uint63.
From mathcomp Require Import all_ssreflect.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

(* -------------------------------------------------------------------- *)
Notation int63 := Uint63.int.
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

Lemma int63_to_Z_le_wB (x : int63): (to_Z x < wB)%Z.
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

End Int63Nat.

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
  by move/(congr1 int63_to_nat); rewrite !nat_to_int63K ?inE.
- apply/(nthP 0%uint63); exists x; rewrite ?size_map ?size_iota;
    first exact/int63_thresholdP.
  rewrite (nth_map 0) ?size_iota; first exact/int63_thresholdP.
  rewrite nth_iota ?add0n; first exact/int63_thresholdP.
  by rewrite int63_to_natK.
Qed.

Definition int63_finMixin := FinMixin enum_int63P.
Canonical  int63_finType  := FinType int63 int63_finMixin.

(* ---------------------------------------------------------------------- *)

Definition imin (i j : int) := if (i <? j)%uint63 then i else j.
Definition imax (i j : int) := if (i <? j)%uint63 then j else i.

Lemma leEint63_ i j: (i <=? j)%uint63 = (i <= j)%nat.
Proof.
apply/idP/idP.
- move/lebP/Znat.Z2Nat.inj_le => /(_ (@int63_to_Z_ge0 i) (@int63_to_Z_ge0 j)).
  by move/leP.
- move/leP=> h; apply/lebP/Znat.Z2Nat.inj_le=> //; exact: int63_to_Z_ge0.
Qed.

Lemma ltEint63_ i j: (i <? j)%uint63 = (i < j)%nat.
Proof.
apply/idP/idP.
- move/ltbP/Znat.Z2Nat.inj_lt => /(_ (@int63_to_Z_ge0 i) (@int63_to_Z_ge0 j)).
  by move/ltP.
- move/ltP=> h; apply/ltbP/Znat.Z2Nat.inj_lt=> //; exact: int63_to_Z_ge0.
Qed.

Program Definition int63_orderMixin :=
  @LeOrderMixin _ leb ltb imin imax _ _ _ _ _ _.

Next Obligation. by rewrite ltEint63_ leEint63_ ltn_neqAle eq_sym. Qed.
Next Obligation. move=> ??; rewrite !leEint63_ => ?; exact/int63_to_nat_inj/anti_leq. Qed.
Next Obligation. move=> ???; rewrite !leEint63_; exact/leq_trans. Qed.
Next Obligation. by move=> ??; rewrite !leEint63_ leq_total. Qed.

Canonical int63_porderType :=
  POrderType Order.NatOrder.nat_display int int63_orderMixin.

(* ------------------------------------------------------------------------ *)

Program Definition leEint63 x y := 
  (leEint63_ x y, _ : ((x <= y)%O = (x <= y)%nat)).
Next Obligation. by rewrite /Order.le /= leEint63_. Qed.

Program Definition ltEint63 x y := 
  (ltEint63_ x y, _ : ((x < y)%O = (x < y)%nat)).
Next Obligation. by rewrite /Order.lt /= ltEint63_. Qed.

Lemma le0int63 (x : int) : (0%uint63 <= x)%O.
Proof. by rewrite leEint63 leq0n. Qed.

Definition top_int63 := (Uint63.pred 0)%uint63.

Lemma top_int63E : to_Z top_int63 = Z.pred wB.
Proof. by []. Qed.

Lemma leTint63 (x : int) : (x <= top_int63)%O.
Proof.
apply/lebP; rewrite top_int63E; apply/Z.lt_le_pred.
by case: (to_Z_bounded x).
Qed.

Canonical int63_latticeType := LatticeType int63 int63_orderMixin.
Canonical int63_bLatticeType := BLatticeType int63 (BottomMixin le0int63).
Canonical int63_tbLatticeType := TBLatticeType int63 (TopMixin leTint63).
Canonical int63_distrLatticeType := DistrLatticeType int63 int63_orderMixin.
Canonical int63_orderType := OrderType int63 int63_orderMixin.

(* -------------------------------------------------------------------- *)
Import Order.Theory.

Section SuccTheory.

Lemma succ_int63E (c : int63):
  (c < 1)%O -> Uint63.succ c = c.+1 :> nat.
Proof. 
move/ltbP; rewrite top_int63E.
move/Z.lt_succ_lt_pred=> c_small; rewrite /int63_to_nat succ_spec.
rewrite Z.add_1_r Zmod_small; first split=> //; 
  first exact/Z.le_le_succ_r/int63_to_Z_ge0.
exact/Z2Nat.inj_succ/int63_to_Z_ge0.
Qed.

Lemma succ_top_int63:
  Uint63.succ top_int63 = 0%uint63.
Proof. by []. Qed.

Lemma succ_int63P (c : int) :
  (c < 1)%O <-> Uint63.succ c = c.+1 :> nat.
Proof.
split; first exact: succ_int63E.
apply/contra_eqT=> /negPf c_max.
by move: (lex1 c); rewrite le_eqVlt c_max orbF=> /eqP -> /=.
Qed.

Lemma succ_int63_ltE (a b : int) :
  (a < b)%O -> Uint63.succ a = a.+1 :> nat.
Proof.
move=> ab.
move: (lt_le_trans ab (lex1 _)).
exact: succ_int63E.
Qed.

Lemma succ_int63_mono (a b : int):
  (a < 1)%O -> (b < 1)%O -> (a <= b)%O = (succ a <= succ b)%O.
Proof.
by move=> a_max b_max; rewrite !leEint63 !succ_int63E.
Qed.

Lemma succ_int63_lt_mono (a b x y: int):
  (a < x)%O -> (b < y)%O -> (a <= b)%O = (succ a <= succ b)%O.
Proof.
move=> a_x b_y.
move: (lt_le_trans a_x (lex1 _)) (lt_le_trans b_y (lex1 _)).
exact: succ_int63_mono.
Qed.

Lemma succ_int63_morph_lt (a b : int):
  (b < 1)%O -> (a < b)%O -> (succ a < succ b)%O.
Proof. 
move=> b_max a_b; rewrite ltEint63. 
rewrite (succ_int63_ltE b_max) (succ_int63_ltE a_b). 
by rewrite ltnS -ltEint63. 
Qed.

Lemma succ_int63_max_lt (a b : int):
  (a < 1)%O -> (b < 1)%O ->
  Order.max (succ a) (succ b) = succ (Order.max a b).
Proof.
move=> a_max b_max; case: leP.
- by rewrite -succ_int63_mono //; case: leP.
- by move/ltW; rewrite -succ_int63_mono //; case: leP.
Qed.

Lemma succ_int63_lt_max (a b x y: int):
  (a < x)%O -> (b < y)%O ->
  Order.max (succ a) (succ b) = succ (Order.max a b).
Proof.
move=> a_x b_y.
move: (lt_le_trans a_x (lex1 _)) (lt_le_trans b_y (lex1 _)).
exact: succ_int63_max_lt.
Qed.

Lemma nat_to_intS n : succ (nat_to_int63 n) = nat_to_int63 n.+1.
Proof.
apply/to_Z_inj; rewrite succ_spec /nat_to_int63.
rewrite Znat.Nat2Z.inj_succ -BinInt.Z.add_1_r !of_Z_spec.
exact/Zdiv.Zplus_mod_idemp_l.
Qed.

Lemma ltiS_ltVeqS (x y : int) : (y < 1)%O -> (x < succ y)%O -> (x < y)%O \/ x = y.
Proof.
move=> y_max; rewrite !ltEint63 succ_int63E // ltnS leq_eqVlt.
by case/orP=> [/eqP/int63_to_nat_inj ->|->]; [right|left].
Qed.

Lemma ltiSi (i : int): (i < 1)%O -> (i < succ i)%O.
Proof. by move=> ?; rewrite ltEint63 succ_int63E. Qed.

End SuccTheory.

(* -------------------------------------------------------------------- *)

(* Section PredTheory.

Lemma pred_intE (x : int) : (0 < x)%O -> Uint63.pred x = x.-1 :> nat.
Proof. 
move/ltbP; rewrite /int63_to_nat to_Z_0 pred_spec=> x_min.
rewrite Zmod_small; first split; rewrite Z.sub_1_r;
  [exact/Zgt_0_le_0_pred/Z.lt_gt|exact/Z.lt_lt_pred/int63_to_Z_le_wB|].
exact: Z2Nat.inj_pred.
Qed.

Lemma pred_succ (x : int) : Uint63.pred (Uint63.succ x) = x.
Proof.
apply/to_Z_inj; rewrite pred_spec succ_spec Zminus_mod_idemp_l.
rewrite Z.add_simpl_r.
by move/Zmod_small: (to_Z_bounded x).
Qed.

End PredTheory.

Section SubTheory.

Lemma sub_intE x y: (x < y)%O -> 
  int63_to_nat (y - x) = int63_to_nat y - int63_to_nat x.
Proof.
move/ltbP=> xy; rewrite /int63_to_nat sub_spec /=.
rewrite Zmod_small; first split.
- exact/Zle_minus_le_0/Z.lt_le_incl.
- move/(@Z.sub_lt_mono_r _ _ (to_Z x)): (int63_to_Z_le_wB y).
  move/Z.lt_le_trans; apply; apply/Z.le_sub_nonneg.
  exact: int63_to_Z_ge0.
- rewrite Z2Nat.inj_sub //; exact: int63_to_Z_ge0.
Qed.

End SubTheory.

Section AddTheory.

Lemma add_intE x y: int63_to_nat x + int63_to_nat y \in gtn int63_threshold ->
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

Section ExtraIntTheory.

Lemma nat_to_int_le (n : nat): ((nat_to_int n) <= n)%nat.
Proof.
rewrite /nat_to_int /int63_to_nat of_Z_spec -[X in (_ <= X)%nat](Znat.Nat2Z.id n).
apply/ssrnat.leP/Znat.Z2Nat.inj_le; try exact: Zorder.Zle_0_nat.
- move/BinInt.Z.mod_pos_bound: wB_pos=> /(_ (BinInt.Z.of_nat n)).
  by case.
- apply/Zdiv.Zmod_le; [exact: wB_pos|exact:Zorder.Zle_0_nat].
Qed.

End ExtraIntTheory. *)

(* -------------------------------------------------------------------- *)


Section IRange.

Definition irange (i j : int) : seq int :=
  sort Order.le (enum [set x | (i <= x)%O && (x < j)%O ]).

Lemma irangee (i : int): irange i i = [::].
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
  rewrite !leEint63 (succ_int63_ltE ij); exact: ltnW.
- apply/uniq_perm; rewrite /= ?uniq_irange // ?andbT.
  + by rewrite mem_irangeE ij andbT leEint63 (succ_int63_ltE ij) ltnn.
  + move=> z; rewrite in_cons !mem_irangeE.
    case/boolP: (z == i)=> [/eqP ->|]; rewrite ?lexx ?ij //=.
    move=> z_n_i; congr andb; rewrite !leEint63 (succ_int63_ltE ij).
    rewrite leq_eqVlt eq_sym.
    case/boolP: (int63_to_nat z == int63_to_nat i)=> //=.
    by move/eqP=> /int63_to_nat_inj /eqP; rewrite (negPf z_n_i).
Qed.

Lemma sorted_cat {T : Type} (leT : rel T) (s t : seq T):
  transitive leT ->
  reflect 
  ([/\ sorted leT s, sorted leT t & allrel leT s t]) 
  (sorted leT (s ++ t)).
Proof.
move=> leT_trans; apply/(iffP idP).
- elim: s t=> /= [t ->|]; rewrite ?allrel0l //.
  move=> a l IH t /[dup] /path_sorted /IH [stt_l stt_t all_lt]. 
  rewrite cat_path=> /andP [path_al path_alt].
  rewrite path_al stt_t; split=> //.
  rewrite allrel_consl all_lt andbT.
  case: l all_lt path_al path_alt {IH stt_l}.
  + move=> /= ??; exact/order_path_min.
  + move=> a' l'; rewrite /= path_sortedE // allrel_consl=> /andP [all_a't _].
    case/and3P=> le_aa' _ _ _; move: all_a't; apply/sub_all=> z.
    exact/leT_trans.
- case; case: s t=> // a l /= t.
  rewrite cat_path=> path_al stt_t.
  rewrite allrel_consl=> /andP [all_at allrel_lt].
  apply/andP; split=> //; rewrite path_sortedE // stt_t andbT.
  elim: l a t allrel_lt all_at {path_al stt_t}=> //=.
  move=> a' l' IH a t + _; rewrite allrel_consl=> /andP [] /[swap].
  exact/IH.
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
  
Definition irange0 (j : int) : seq int := irange 0 j.

Lemma irange0_iota j: irange0 j = map nat_to_int63 (iota 0 j). 
Proof.
apply/lt_sorted_eq; first exact: sorted_irange.
- rewrite sorted_map.
  case E: (int63_to_nat j)=> [|j'] //=.
  apply/(pathP 0%nat)=> i.
  rewrite size_iota=> /[dup] i_j'; rewrite -ltnS -E => /ltnW i_j.
  case: i i_j' i_j; first by (move=> /= ??; rewrite nth_iota).
  move=> n ?? /=; rewrite !nth_iota //; first exact/ltnW.
  rewrite !add1n ltEint63 !nat_to_int63K // inE.
  + apply/(@ltn_trans j)=> //; exact: int63_thresholdP.
  + apply/(@leq_ltn_trans j)=> //; exact: int63_thresholdP.
- move=> x; rewrite mem_irangeE le0x /=.
  apply/idP/idP.
  + move=> x_j; apply/mapP; exists (int63_to_nat x); rewrite ?int63_to_natK //.
    by rewrite mem_iota add0n leq0n /=; rewrite -ltEint63.
  + case/mapP=> y; rewrite mem_iota leq0n add0n /=; move=> y_j ->.
    rewrite ltEint63 nat_to_int63K // inE.
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
- move=> /[dup] ij; rewrite ltEint63=> /ltnW; rewrite -subn_eq0=> /eqP ->; apply/eqP/nilP.
  move: (mem_irangeE i j); case: (irange i j)=> //= a l.
  move=> /(_ a); rewrite in_cons eqxx /= => /esym/andP [] /le_lt_trans /[apply].
  by move/ltW; rewrite leNgt ij.
Qed.

Lemma nth_irange0 (j : int) k:
  (k < j)%nat -> nth 0%uint63 (irange0 j) k = nat_to_int63 k.
Proof.
move=> kj; rewrite irange0_iota (nth_map 0) ?size_iota //.
by rewrite nth_iota.
Qed.

Lemma nth_irange (i j : int) k:
  (k < j - i)%nat -> nth 0%uint63 (irange i j) k = nat_to_int63 (k + i).
Proof.
move=> kji; move: (leq_ltn_trans (leq0n k) kji); rewrite subn_gt0.
move/ltnW; rewrite -leEint63=> ij.
move: (irange_cat (le0x i) ij)=> /(congr1 (fun s=> nth 0%uint63 s (k + i))).
rewrite nth_irange0 addnC -?ltn_subRL // nth_cat size_irange0.
by rewrite ltnNge leq_addr /= addKn => ->.
Qed.

Lemma iotaS_rcons (m n : nat): iota m n.+1 = rcons (iota m n) (m + n)%nat.
Proof.
elim: n m=> [|n IH].
- move=> ? /=; rewrite addn0 //.
- by move=> m /=; rewrite addnS -addSn -IH.
Qed.

Lemma irange0_succ (i : int):
  (i < 1)%O -> irange0 (succ i) = rcons (irange0 i) i.
Proof.
move=> i_max; rewrite !irange0_iota succ_int63E // iotaS_rcons add0n map_rcons.
by rewrite int63_to_natK.
Qed. 

End IRange.

Section IFold.

Fixpoint ifold_ {T : Type} (n : nat) (f : int -> T -> T) (i M : int) (x : T) :=
  if (i =? M)%uint63 then (i, x) else
    if n is n.+1 then
      let: (i, x) := ((i + 1)%uint63, f i x) in
      let: (i, x) := ifold_ n f i M x in
      let: (i, x) := ifold_ n f i M x in
      (i, x)
    else (i, x).

Definition ifold {T : Type} (f : int -> T -> T) (i : int) (x : T) :=
  (ifold_ Uint63.size f 0 i x).2.

Definition iall (f : int -> bool) (i : int):=
  (ifold (fun i acc=> acc && f i) i true).

Lemma ifold_E {S : Type} (n : nat) (f : int -> S -> S) (i M : int) (x : S):
  (i <= M)%nat ->
  let: j := ((int63_to_nat i) + (2 ^ n) - 1)%nat in
  let: j' := if (j <= int63_to_nat M)%nat then nat_to_int63 j else M in
  ifold_ n f i M x = (j', foldl (fun s t=> f t s) x (irange i j')).
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
  move: iM; rewrite leq_eqVlt (negPf inM_nat) /= -ltEint63 => SiM.
  move: (IHn (Uint63.succ i) (f i x)); rewrite (succ_int63_ltE SiM) -ltEint63=> /(_ SiM) ->.
  rewrite -addnBAC // subSS subn0.
  set N1 := (_ + 2 ^ n)%nat.
  case: ifP; last first. 
  + rewrite IHn /N1 //; case: n {IHn N1}; rewrite ?expn0 ?addn1 -?ltEint63 ?SiM //.
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
      case: ifP=> // N2_M; rewrite ltEint63 ?nat_to_int63K ?inE; first apply/(leq_ltn_trans N2_M)/int63_thresholdP.
      rewrite /N2 -addnBA ?expn_gt0 // -ltn_psubLR ?subnn subn_gt0 -[X in (X < _)%nat](expn0 2); exact: ltn_exp2l.
    rewrite -foldl_cat -irange_cat //.
    * by rewrite leEint63 (succ_int63_ltE SiM) ?nat_to_int63K // -ltn_psubLR ?subnn expn_gt0.
    * rewrite leEint63 nat_to_int63K //; case: ifP=> // N2_M.
      rewrite ?nat_to_int63K ?inE //; exact/(leq_ltn_trans N2_M)/int63_thresholdP.
Qed.

Lemma ifoldE {S : Type} (f : int -> S -> S) (M : int) (x : S):
  IFold.ifold f M x = foldl (fun s t=> f t s) x (irange0 M).
Proof.
rewrite /ifold ifold_E ?leq0n //=.
move: (int63_thresholdP M); rewrite /int63_threshold; unlock.
rewrite add0n -add1n -leq_subRL ?expn_gt0 //.
rewrite leq_eqVlt ltnNge; case/orP=> [/eqP <-|]; rewrite ?leqnn ?int63_to_natK //.
by move/negPf => ->.
Qed.

Lemma iallE (f : int -> bool) (M : int):
  IFold.iall f M = all f (irange0 M).
Proof. 
rewrite /IFold.iall ifoldE /ifold /iall.
elim/last_ind: (irange0 M)=> // t h IH.
by rewrite foldl_rcons all_rcons andbC IH.
Qed.

End IFold.
