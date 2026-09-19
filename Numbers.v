From Stdlib Require Import NArith.NArith.
From Stdlib Require Import Lia List.

Import ListNotations.
Open Scope N_scope.

Definition byte : Type := { x : N | x < 256 }.

Definition byte_val (b : byte) : N := proj1_sig b.

(* RFC 9580 uses "octet" for a 8-bit value. *)
Definition octet : Type := byte.
Definition octet_val : octet -> N := byte_val.

Definition scalar2 (n0 n1 : octet) : N :=
  N.shiftl (octet_val n0) 8 +
  octet_val n1.

Definition scalar2' (n0 n1 : octet) : N :=
  octet_val n0 * 256 +
  octet_val n1.

Definition scalar2_foldl (os : list octet) : N :=
  fold_left (fun acc b => acc * 256 + octet_val b) os 0.

Definition scalar2_foldr (os : list octet) : N :=
  fold_right (fun b acc => acc * 256 + octet_val b) 0 os.

Theorem scalar2_foldl_rev :
  forall (l : list octet),
    scalar2_foldl l = scalar2_foldr (rev l).
Proof.
intros l.
unfold scalar2_foldr, scalar2_foldl.
rewrite <- fold_left_rev_right.
reflexivity.
Qed.

Theorem scalar2_foldl_equiv : 
  forall (n0 n1 : octet),
    scalar2 n0 n1 = scalar2_foldl [n0 ; n1].
Proof.
intros n0 n1. 
unfold scalar2, scalar2_foldl.
rewrite N.shiftl_mul_pow2.
simpl; nia.
Qed.

Theorem scalar2_eq : 
  forall (n0 n1 : octet), 
    scalar2 n0 n1 = scalar2' n0 n1.
Proof.
intros n0 n1.
unfold scalar2, scalar2'.
rewrite N.shiftl_mul_pow2; simpl.
lia.
Qed.

Definition scalar4
    (n0 n1 n2 n3 : octet) : N :=
  N.shiftl (octet_val n0) 24 +
  N.shiftl (octet_val n1) 16 +
  N.shiftl (octet_val n2) 8 +
  octet_val n3.

Definition scalar4'
    (n0 n1 n2 n3 : octet) : N :=
  octet_val n0 * 16777216 +
  octet_val n1 * 65536 +
  octet_val n2 * 256 +
  octet_val n3.

Definition scalar4_foldl (os : list octet) : N :=
  fold_left
    (fun acc b => acc * 256 + octet_val b)
    os
    0.

Definition scalar4_foldr (os : list octet) : N :=
  fold_right
    (fun b acc => acc * 256 + octet_val b)
    0
    os.

Theorem scalar4_eq : 
  forall (n0 n1 n2 n3: octet), 
    scalar4 n0 n1 n2 n3 = scalar4' n0 n1 n2 n3.
Proof.
intros n0 n1 n2 n3.
unfold scalar4, scalar4'.
do 3 (rewrite N.shiftl_mul_pow2).
simpl; lia.
Qed.

Theorem scalar2_bound :
  forall (a b : octet),
    scalar2 a b < 65536.
Proof.
intros [a Ha] [b Hb].
rewrite scalar2_eq.
unfold scalar2'.
simpl; lia.
Qed.

Theorem scalar4_bound :
  forall (a b c d : octet),
    scalar4 a b c d < 4294967296.
Proof.
intros [a Ha] [b Hb] [c Hc] [d Hd].
rewrite scalar4_eq.
unfold scalar4'.
simpl; lia.
Qed.

Theorem scalar4_fold_equiv' :
  forall (l : list octet),
    scalar4_foldr l = scalar4_foldl (rev l).
Proof.
  intros l.
  unfold scalar4_foldr, scalar4_foldl.
  rewrite <- fold_left_rev_right.
  rewrite rev_involutive.
  reflexivity.
Qed.

Theorem scalar4_foldl_eq :
  forall (n0 n1 n2 n3 : octet),
    scalar4 n0 n1 n2 n3 =
    scalar4_foldl [n0; n1; n2; n3].
Proof.
  intros n0 n1 n2 n3.
  unfold scalar4, scalar4_foldl.
  simpl.
  do 3 (rewrite N.shiftl_mul_pow2).
  simpl; lia.
Qed.
