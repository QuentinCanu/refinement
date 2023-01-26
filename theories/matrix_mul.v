From mathcomp Require Import all_ssreflect all_algebra finmap.
From Bignums Require Import BigQ.
From Coq Require Import Uint63 PArray PArith PeanoNat.
Require Import extra_misc inner_product vector_order extra_array extra_int refinement rat_bigQ.

Import Order.Theory.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Functions to be executed within coq*)
Module Efficient.

Definition array_dot {T : Type} (addf mulf: T -> T -> T) (x0 : T)
  (a b : array T):=
  PArrayUtils.fold_pair (fun x y res=> addf res (mulf x y)) a b x0.

Definition array_mul_row_mx {T : Type} addf mulf x0
  (v : array T) (M : array (array T)):=
  PArrayUtils.map (fun c=> array_dot addf mulf x0 v c) M.

Definition array_mulmx {T : Type} addf mulf x0
  (M N : array (array T)):=
  PArrayUtils.map (fun v=> array_mul_row_mx addf mulf x0 v N) M.

End Efficient.

(*Equivalent definitions to be used on proofs*)
Section Def.

Definition array_dot {T : Type} (addf mulf: T -> T -> T) (x0 : T)
  (a b : array T):=
  arr_fold_pair (fun x y res=> addf res (mulf x y)) a b x0.

Definition array_mul_row_mx {T : Type} addf mulf x0
  (v : array T) (M : array (array T)):=
  arr_map (fun c=> array_dot addf mulf x0 v c) M.

Definition array_mulmx {T : Type} addf mulf x0
  (M N : array (array T)):=
  arr_map (fun v=> array_mul_row_mx addf mulf x0 v N) M.

Lemma array_dotE {T : Type} addf mulf x0 (a b : array T):
  Efficient.array_dot addf mulf x0 a b =
  array_dot addf mulf x0 a b.
Proof. exact/arr_fold_pairE. Qed.

Lemma array_mul_row_mxE {T : Type} addf mulf x0
  (v : array T) (M : array (array T)):
  Efficient.array_mul_row_mx addf mulf x0 v M =
  array_mul_row_mx addf mulf x0 v M.
Proof.
rewrite /Efficient.array_mul_row_mx arr_mapE.
rewrite /array_mul_row_mx /arr_map /ifold array_dotE.
by apply/eq_foldl=> ??; rewrite array_dotE.
Qed.

Lemma array_mulmxE {T : Type} addf mulf x0
  (M N : array (array T)):
  Efficient.array_mulmx addf mulf x0 M N =
  array_mulmx addf mulf x0 M N.
Proof.
rewrite /Efficient.array_mulmx arr_mapE.
rewrite /array_mulmx /arr_map array_mul_row_mxE.
by apply/eq_foldl=> ??; rewrite array_mul_row_mxE.
Qed.

End Def.

(* -------------------------------------------------------- *)

Section Refinement.

(* (r1 =~> r2 =~> r3) f F := r1 x X -> r2 y Y -> r3 (f x y) (F X Y) *)

Section RelArray.
(* rel_array r a A := length a = length A /\ 
  forall i, i < length a -> r a.[i] A.[i] *)

Lemma rel_array_dot {t T : Type} (r : t -> T -> Prop)
  addf addF mulf mulF x0 X0:
  (r =~> r =~> r) addf addF ->
  (r =~> r =~> r) mulf mulF ->
  r x0 X0 ->
  (rel_array r =~> rel_array r =~> r) 
  (array_dot addf mulf x0) (array_dot addF mulF X0).
Proof.
move=> addh mulh x0h a A aA b B bB.
apply: rel_array_fold_pair=> //; [|exact:aA|exact:bB].
move=> ?????????; apply/addh=> //; exact/mulh.
Qed.

Lemma rel_array_mul_row_mx {t T : Type} (r : t -> T -> Prop)
  addf addF mulf mulF x0 X0:
  (r =~> r =~> r) addf addF ->
  (r =~> r =~> r) mulf mulF ->
  r x0 X0 ->
  (rel_array r =~> rel_array (rel_array r) =~> rel_array r)
  (array_mul_row_mx addf mulf x0) (array_mul_row_mx addF mulF X0).
Proof.
move=> addh mulh x0h a A aA b B bB.
apply: rel_array_map; [|exact:bB].
exact:rel_array_dot.
Qed.

Lemma rel_array_mulmx {t T : Type} (r : t -> T -> Prop)
  addf addF mulf mulF x0 X0:
  (r =~> r =~> r) addf addF ->
  (r =~> r =~> r) mulf mulF ->
  r x0 X0 ->
  (rel_array (rel_array r) =~> rel_array (rel_array r) =~>
  rel_array (rel_array r))
  (array_mulmx addf mulf x0) (array_mulmx addF mulF X0).
Proof.
move=> addh mulh x0h a A aA b B bB.
apply:rel_array_map; [|exact:aA].
by move=> ???; apply:rel_array_mul_row_mx.
Qed.

End RelArray.

Section RelVector.

Context (R : realFieldType).

(* r: array R -> R-vector -> Prop *)
(* Or r: array (array R) -> R-matrix -> Prop *)
(* Matrices are represented either by rows or by columns *)

Lemma rel_cV_dot (n : nat):
  (@rel_cV R n =~> @rel_cV R n =~> eq)
  (fun x y=> array_dot +%R *%R 0%R x y)
  (fun X Y=> vdot X Y).
Proof. exact/rel_cV_big. Qed.

Lemma rel_mx_row_mul (m n : nat):
  (@rel_rV R m =~> @rel_mx_col R m n =~> @rel_rV R n) 
    (fun v a=> array_mul_row_mx +%R *%R 0%R v a)
    (fun V A=> (V *m A)%R).
Proof.
move=> v V vV a A aA; split.
- by rewrite length_arr_map; case: aA.
- move=> i; rewrite mxE -matrix_vdot row_id arr_map_nth.
  by apply/rel_cV_dot=> //; case: aA=> _ /(_ i).
Qed.

Lemma rel_mulmx (m n k : nat):
  (@rel_mx_row R m n =~> @rel_mx_col R n k =~> @rel_mx_row R m k) 
  (fun a b=> array_mulmx +%R *%R 0%R a b)
  (fun A B=> (A *m B)%R).
Proof.
move=> a A aA b B bB; split.
- by rewrite length_arr_map; case: aA.
- move=> i; rewrite arr_map_nth row_mul.
  by apply/rel_mx_row_mul=> //; case: aA=> _ /(_ i).
Qed.

End RelVector.
Section RelTotal.

Context (t : Type) (R : realFieldType).
Context (r : t -> R -> Prop).

(* rel_point_cV := rel_array r |~ rel_cV *)
(* rel_point_rV := rel_array r |~ rel_rV *)
(* rel_point_mx_row := rel_array (rel_array r) |~ rel_mx_row *)
(* rel_point_mx_col := rel_array (rel_array r) |~ rel_mx_col *)

Lemma rel_point_dot (n : nat) addf mulf x0:
  (r =~> r =~> r) addf +%R->
  (r =~> r =~> r) mulf *%R->
  r x0 0%R->
  (@rel_point_cV t R r n =~> @rel_point_cV t R r n =~> r)
  (array_dot addf mulf x0) (fun X Y=> '[X,Y]%R).
Proof.
move=> addh mulh x0h.
apply/rel_equiv_func2;
  [exact:rel_equiv_refl|exact:rel_equiv_refl|exact:rel_comp_eqR|].
by apply/rel_comp_func2; [apply:rel_array_dot|apply:rel_cV_dot].
Check rel_comp_func2.
Qed.

Lemma rel_point_mul_row_mx (m n : nat) addf mulf x0:
  (r =~> r =~> r) addf +%R->
  (r =~> r =~> r) mulf *%R->
  r x0 0%R->
  (@rel_point_rV t R r m =~> @rel_point_mx_col t R r m n =~> 
  @rel_point_rV t R r n)
  (array_mul_row_mx addf mulf x0) (fun v M=> (v *m M)%R).
Proof.
move=> addh mulh x0h.
by apply/rel_comp_func2; [apply:rel_array_mul_row_mx|apply:rel_mx_row_mul].
Qed.

Lemma rel_point_mulmx (m n p: nat) addf mulf x0:
  (r =~> r =~> r) addf +%R->
  (r =~> r =~> r) mulf *%R->
  r x0 0%R->
  (@rel_point_mx_row t R r m p =~> @rel_point_mx_col t R r p n =~> 
  @rel_point_mx_row t R r m n)
  (array_mulmx addf mulf x0) (fun A B=> (A *m B)%R).
Proof.
move=> addh mulh x0h.
by apply/rel_comp_func2;
  [apply/rel_array_mulmx|apply/rel_mulmx].
Qed.

End RelTotal.

End Refinement.

(* -------------------------------------------------------- *)

Section Equivalence.
(* Instantiations *)

Definition rel_Q_cV n:= @rel_point_cV _ _ rat_bigQ n.
Definition rel_Q_rV n:= @rel_point_rV _ _ rat_bigQ n.
Definition rel_Q_mx_row m n:= @rel_point_mx_row _ _ rat_bigQ m n.
Definition rel_Q_mx_col m n:= @rel_point_mx_col _ _ rat_bigQ m n.

Definition bigQ_array_dot := array_dot (BigQ.add) (BigQ.mul) (0%bigQ).
Definition bigQ_array_mul_row_mx :=
  array_mul_row_mx (BigQ.add) (BigQ.mul) (0%bigQ).
Definition bigQ_array_mulmx :=
  array_mulmx (BigQ.add) (BigQ.mul) (0%bigQ).

Lemma rel_Q_dot (n : nat):
  (@rel_Q_cV n =~> @rel_Q_cV n =~> rat_bigQ)
  bigQ_array_dot (fun v w=> '[v,w]%R).
Proof.
apply:rel_point_dot; 
  [exact:rat_bigQ_add|exact:rat_bigQ_mul|exact:rat_bigQ0].
Qed.
  
Lemma rel_Q_mul_row_mx (m n : nat):
  (@rel_Q_rV m =~> @rel_Q_mx_col m n =~> @rel_Q_rV n)
  bigQ_array_mul_row_mx (fun v M => (v *m M)%R).
Proof.
apply:rel_point_mul_row_mx;
  [exact:rat_bigQ_add|exact:rat_bigQ_mul|exact:rat_bigQ0].
Qed.

Lemma rel_Q_mulmx (m n p: nat):
  (@rel_Q_mx_row m n =~> @rel_Q_mx_col n p =~> @rel_Q_mx_row m p)
  bigQ_array_mulmx (fun A B=> (A *m B)%R).
Proof.
apply:rel_point_mulmx;
  [exact:rat_bigQ_add|exact:rat_bigQ_mul|exact:rat_bigQ0].
Qed.

End Equivalence.

(* -------------------------------------------------------- *)

Section SpecFunc.

(* f : t -> T, i.e P x -> r x (f x)*)

(* Definitions of f *)
Definition Q_cV_spec_func (n : nat) := 
  arr_to_point_cV n bigQ2rat_def.

Definition Q_rV_spec_func (n : nat) := 
  arr_to_point_rV n bigQ2rat_def.

Definition Q_mx_row_spec_func (m n : nat) := 
  arr_to_point_mx_row m n bigQ2rat_def.

Definition Q_mx_col_spec_func (m n : nat) := 
  arr_to_point_mx_col m n bigQ2rat_def.

(* Definitions of P *)
Definition precond_bigQ_cV (n : nat) (a : array bigQ) :=
  precond_len n a /\ precond_array (fun _=> True) a.

Definition precond_bigQ_rV (n : nat) (a : array bigQ) :=
  precond_len n a /\ precond_array (fun _=> True) a.

Definition precond_bigQ_mx_row (m n : nat) (a : array (array bigQ)):=
  precond_mx m n a /\ precond_array (precond_array (fun _=> True)) a.

Definition precond_bigQ_mx_col (m n : nat) (a : array (array bigQ)):=
  precond_mx n m a /\ precond_array (precond_array (fun _=> True)) a.

(* spec_func r f P := forall x, P x -> r x (f x) *)
Lemma Q_cV_spec_funcP (n : nat):
  spec_func (@rel_Q_cV n) (@Q_cV_spec_func n) (@precond_bigQ_cV n).
Proof. exact/spec_func_to_point_cV. Qed.

Lemma Q_rV_spec_funcP (n : nat):
  spec_func (@rel_Q_rV n) (@Q_rV_spec_func n) (@precond_bigQ_rV n).
Proof. exact/spec_func_to_point_rV. Qed.

Lemma Q_mx_row_spec_funcP (m n : nat):
  spec_func (@rel_Q_mx_row m n) (@Q_mx_row_spec_func m n) 
  (@precond_bigQ_mx_row m n).
Proof. exact: spec_func_to_point_mx_row. Qed.

Lemma Q_mx_col_spec_funcP (m n : nat):
  spec_func (@rel_Q_mx_col m n) (@Q_mx_col_spec_func m n) 
  (@precond_bigQ_mx_col m n).
Proof. exact: spec_func_to_point_mx_col. Qed.

End SpecFunc.