(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** * Int31 numbers defines Z/(2^31)Z, and can hence be equipped
      with a ring structure and a ring tactic *)

Require Import Int8 Cyclic8 CyclicAxioms.

Local Open Scope int8_scope.

(** Detection of constants *)

Local Open Scope list_scope.

Ltac isInt8cst_lst l :=
 match l with
 | nil => constr:true
 | ?t::?l => match t with
               | D1 => isInt8cst_lst l
               | D0 => isInt8cst_lst l
               | _ => constr:false
             end
 | _ => constr:false
 end.

Ltac isInt8cst t :=
 match t with
 | I8 ?i0 ?i1 ?i2 ?i3 ?i4 ?i5 ?i6 ?i7  =>
    let l :=
      constr:(i0::i1::i2::i3::i4::i5::i6::i7::nil)
    in isInt8cst_lst l
 | Int8.On => constr:true
 | Int8.In => constr:true
 | Int8.Tn => constr:true
 | Int8.Twon => constr:true
 | _ => constr:false
 end.

Ltac Int8cst t :=
 match isInt8cst t with
 | true => constr:t
 | false => constr:NotConstant
 end.

(** The generic ring structure inferred from the Cyclic structure *)

Module Int8ring := CyclicRing Int8Cyclic.

(** Unlike in the generic [CyclicRing], we can use Leibniz here. *)

Lemma Int8_canonic : forall x y, phi x = phi y -> x = y.
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

Lemma Int8Ring : ring_theory On In add8 mul8 sub8 opp8 Logic.eq.
Proof.
exact (ring_theory_switch_eq _ _ _ _ _ _ _ _ _ Int8_canonic Int8ring.CyclicRing).
Qed.

Lemma eqb8_eq : forall x y, eqb8 x y = true <-> x=y.
Proof.
unfold eqb8. intros x y.
rewrite Cyclic8.spec_compare. case Z.compare_spec.
intuition. apply Int8_canonic; auto.
intuition; subst; auto with zarith; try discriminate.
intuition; subst; auto with zarith; try discriminate.
Qed.

Lemma eqb8_correct : forall x y, eqb8 x y = true -> x=y.
Proof. now apply eqb8_eq. Qed.

Add Ring Int8Ring : Int8Ring
 (decidable eqb8_correct,
  constants [Int8cst]).

Section TestRing.
Let test : forall x y, In + x*y + x*x + In = In*In + In + y*x + In*x*x.
intros. ring.
Qed.
End TestRing.

