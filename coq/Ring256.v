(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** * Int31 numbers defines Z/(2^31)Z, and can hence be equipped
      with a ring structure and a ring tactic *)

Require Import Int256 Cyclic256 CyclicAxioms.

Local Open Scope int256_scope.

(** Detection of constants *)

Local Open Scope list_scope.

Ltac isInt256cst_lst l :=
 match l with
 | nil => constr:true
 | ?t::?l => match t with
               | D1 => isInt256cst_lst l
               | D0 => isInt256cst_lst l
               | _ => constr:false
             end
 | _ => constr:false
 end.

Ltac isInt256cst t :=
 match t with
(*
 | I256 ?i0 ?i1 ?i2 ?i3 ?i4 ?i5 ?i6 ?i7  =>
    let l :=
      constr:(i0::i1::i2::i3::i4::i5::i6::i7::nil)
    in isInt8cst_lst l *)
 | Int256.On => constr:true
 | Int256.In => constr:true
 | Int256.Tn => constr:true
 | Int256.Twon => constr:true
 | _ => constr:false
 end.

Ltac Int256cst t :=
 match isInt256cst t with
 | true => constr:t
 | false => constr:NotConstant
 end.

(** The generic ring structure inferred from the Cyclic structure *)

Module Int256ring := CyclicRing Int256Cyclic.

(** Unlike in the generic [CyclicRing], we can use Leibniz here. *)

Lemma Int256_canonic : forall x y, phi x = phi y -> x = y.
Proof.
 intros x y EQ.
 now rewrite <- (phi_inv_phi x), <- (phi_inv_phi y), EQ.
Qed.

Lemma ring_theory_switch_eq :
 forall A (R R':A->A->Prop) zero one add mul sub opp,
  (forall x y : A, R x y -> R' x y) ->
  ring_theory zero one add mul sub opp R ->
  ring_theory zero one add mul sub opp R'.
Proof.
intros A R R' zero one add mul sub opp Impl Ring.
constructor; intros; apply Impl; apply Ring.
Qed.

Lemma Int256Ring : ring_theory On In add256 mul256 sub256 opp256 Logic.eq.
Proof.
exact (ring_theory_switch_eq _ _ _ _ _ _ _ _ _ Int256_canonic Int256ring.CyclicRing).
Qed.

Lemma eqb256_eq : forall x y, eqb256 x y = true <-> x=y.
Proof.
unfold eqb256. intros x y.
rewrite Cyclic256.spec_compare. case Z.compare_spec.
intuition. apply Int256_canonic; auto.
intuition; subst; auto with zarith; try discriminate.
intuition; subst; auto with zarith; try discriminate.
Qed.

Lemma eqb256_correct : forall x y, eqb256 x y = true -> x=y.
Proof. now apply eqb256_eq. Qed.

Add Ring Int256Ring : Int256Ring
 (decidable eqb256_correct,
  constants [Int256cst]).

Section TestRing.
Let test : forall x y z, x-(y+z) = x-y-z.
intros. ring.
Qed.
End TestRing.

