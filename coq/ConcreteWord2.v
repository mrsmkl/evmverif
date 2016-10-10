Require Import Word.

Require Import Cyclic.Abstract.CyclicAxioms.
Require Import Coq.Lists.List.
Require Import OrderedType.

Require FMapList.
Require Import ZArith.

Require BinNums.
Require Import Cyclic8.
Require Import Cyclic256.

Module ConcreteWord2 <: Word.

  Module W := Int256Cyclic.

  Module B := Int8Cyclic.

  Module A := Int256Cyclic.

  Definition word := W.t.

  Definition word_eq (a : W.t) (b : W.t) :=
    match ZnZ.compare a b with Eq => true | _ => false end.

  Open Scope int256_scope.
  (* with [ZnZ.to_Z], the result is guaranteed to be small,
   * and this makes rewriting easier *)
  Definition word_add (a b : W.t) := a + b.

  Definition word_mul (a b : W.t) := a * b.

  Definition word_sub a b := (a - b).

  Definition word_one := ZnZ.one.

  Definition word_zero := ZnZ.zero.

  Definition word_iszero := word_eq On.

  Definition word_mod := ZnZ.modulo.

  Ltac compute_word_mod :=
    set (focus := word_mod _ _);
    compute in focus;
    unfold focus;
    clear focus.


  Definition word_smaller a b :=
    match ZnZ.compare a b with Lt => true | _ => false end.

  Definition word_smaller_or_eq a b :=
    match ZnZ.compare a b with Lt => true | Eq => true | Gt => false end.

Print N.
  Definition word_of_N n := match n with
   | N0 => On
   | Npos p => snd (ZnZ.of_pos p)
   end.

  Definition N_of_word w := Z.to_N (ZnZ.to_Z w).


Require Import Zpow_facts.

  Lemma N_of_word_of_N :
    forall (n : N), (n < 10000)%N -> N_of_word (word_of_N n) = n.
  Proof.
    intros n nsmall.
    unfold N_of_word.
    unfold word_of_N.
    unfold ZnZ.to_Z.
    simpl.
    destruct n;auto.
    rewrite positive_to_int256_phi_inv_positive.
    rewrite phi_phi_inv_positive.
    rewrite Z.mod_small.
    rewrite Z2N.inj_pos;trivial.
    split.
    apply Pos2Z.is_nonneg.
rewrite <- Z2N.inj_pos in nsmall.
apply Z2N.inj_lt.
    apply Pos2Z.is_nonneg.
simpl.
apply Z.lt_le_incl.
apply Zpower_pos_pos.
omega.
    eapply N.lt_trans.
eassumption.
      vm_compute; auto.
  Qed.

  Module WordOrdered <: OrderedType.
  (* Before using FSetList as storage,
     I need word as OrderedType *)
      Definition t := W.t.
      Definition eq a b := is_true (word_eq a b).
      Arguments eq /.

      Definition lt a b := is_true (word_smaller a b).
      Arguments lt /.


      Lemma eq_refl : forall x : t, eq x x.
      Proof.
        intro.
        unfold eq.
        unfold word_eq.
        simpl.
        rewrite spec_compare.
        rewrite Z.compare_refl.
        auto.
      Qed.

      Lemma eq_sym : forall x y : t, eq x y -> eq y x.
      Proof.
        intros ? ?.
        simpl.
        unfold word_eq. simpl.
        rewrite !spec_compare.
        rewrite <-Zcompare_antisym.
        simpl.
        set (r := (phi y ?= phi x)%Z).
        case r; unfold CompOpp; auto.
      Qed.

      Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
      Proof.
        intros ? ? ?.
        unfold eq.
        unfold word_eq.
        simpl.
        rewrite !spec_compare.
        set (xy := (phi x ?= phi y)%Z).
        case_eq xy; auto; try congruence.
        unfold xy.
        rewrite Z.compare_eq_iff.
        intro H.
        rewrite H.
        auto.
      Qed.

      Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
      Proof.
        intros x y z.
        unfold lt.
        unfold word_smaller.
        simpl.
        rewrite !spec_compare.
        case_eq (phi x ?= phi y)%Z; try congruence.
        case_eq (phi y ?= phi z)%Z; try congruence.
        intros H I _ _.
        erewrite (Zcompare_Lt_trans); auto; eassumption.
      Qed.

      Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
      Proof.
        unfold t.
        intros x y.
        unfold lt; unfold eq.
        unfold word_smaller; unfold word_eq.
        simpl.
        case_eq (x ?= y)%int256; congruence.
      Qed.

(*
      Definition t := W.t.
      Definition eq (a b:t) := (a=b).
      Arguments eq /.

      Definition lt a b := is_true (word_smaller a b).
      Arguments lt /.


      Lemma eq_refl : forall x : t, eq x x.
      Proof.
        unfold eq.
        auto.
      Qed.

      Lemma eq_sym : forall x y : t, eq x y -> eq y x.
      Proof.
        unfold eq.
        auto.
      Qed.

      Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
      Proof.
        unfold eq.
        congruence.
      Qed.

      Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
      Proof.
        intros x y z.
        unfold lt.
        unfold word_smaller.
        rewrite !ZnZ.spec_compare.
        case_eq (ZnZ.to_Z x ?= ZnZ.to_Z y)%Z.
        intro.
        setoid_rewrite H.
        congruence.
        intro.
        setoid_rewrite H.
        case_eq (ZnZ.to_Z y ?= ZnZ.to_Z z)%Z.
        intro.
        setoid_rewrite H0.
        congruence.
        intro.
        setoid_rewrite H0.
        intros _ _.
        erewrite (Zcompare_Lt_trans); auto; eassumption.
        intro.
        setoid_rewrite H0;congruence.
        intro.
        setoid_rewrite H;congruence.
      Qed.

      Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
      Proof.
        unfold t.
        intros x y.
        unfold lt; unfold eq.
        unfold word_smaller.
        simpl.
        Require Import Int256.
        case_eq (compare256 x y); try congruence.
rewrite !spec_compare.
        intros H _.
Search ((_ ?= _)%Z = Lt).
elim (Z.compare_lt_iff (phi x) (phi y));intros.
      Qed.
*)

      Definition compare : forall x y : t, Compare lt eq x y.
      Proof.
        intros x y.
        unfold lt.
        case_eq (word_smaller x y); intro L.
        { apply LT; auto. }
        unfold eq.
        case_eq (word_eq x y); intro E.
        { apply EQ; auto. }
        apply GT.
        unfold word_smaller.
        unfold word_smaller in L.
        unfold word_eq in E.
        simpl in *.

        rewrite spec_compare in *.

        case_eq (phi y ?= phi x)%Z; try congruence.

        {
          rewrite Z.compare_eq_iff.
          intro H.
          rewrite H in E.
          rewrite Z.compare_refl in E.
          congruence.
        }
        {
          rewrite Zcompare_Gt_Lt_antisym.
          intro H.
          rewrite H in L.
          congruence.
        }
      Defined.

      Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
      Proof.
        unfold eq.
        intros x y.
        case (word_eq x y); [left | right]; congruence.
      Defined.

  End WordOrdered.


  Definition byte := B.t.

  Definition address := A.t.

  Definition address_of_word (w : word) : address := w.
  Definition word_of_address (a : address) : word := a.

  Definition address_eq a b :=
    match ZnZ.compare a b with Eq => true | _ => false end.

  Lemma address_eq_refl :
    forall a, address_eq a a = true.
  Proof.
    intro a.
    unfold address_eq.
    rewrite ZnZ.spec_compare.
    rewrite Z.compare_refl.
    reflexivity.
  Qed.


Require Int8.

(* Get bits
  Fixpoint do_shiftr w n := match n with
   | O => w
   | S n => shiftr (do_shiftr w n)
  end.

  Fixpoint do_shiftl w n := match n with
   | O => w
   | S n => shiftl (do_shiftl w n)
  end.

Fixpoint word_to_bits w n := match n with
 | O => nil
 | S n => firstr w :: word_to_bits (shiftr w) n
end.

Fixpoint bits_to_word lst := match lst with
 | nil => On
 | D0::tl => shiftl (bits_to_word tl)
 | D1::tl => In + shiftl (bits_to_word tl)
end.

Lemma word_and_bits : forall lst, word_to_bits (bits_to_word lst) 256 = lst.
intros.
induction lst.
simpl.
*)
Definition split_word n w := w / phi_inv (2^(Z.of_nat n)).

Definition combine_word n uv := (fst uv)*(phi_inv (2^(Z.of_nat n))) + (snd uv).

Require Import Ring256.

Lemma phi_eq_lemma : forall a b, phi a = phi b -> a = b.
Proof.
    intros.
    apply eqb256_correct.
unfold eqb256.
unfold compare256.
rewrite H.
rewrite Z.compare_refl.
trivial.
Qed.

Check spec_div.

Lemma spec_div_nolet : forall a b : int256,
       (0 < phi b)%Z ->
       phi a = (phi (fst (a/b)%int256) * phi b + phi (snd (a/b)%int256))%Z /\
       (0 <= phi (snd (a/b)%int256) < phi b)%Z.
intros.
pose (spec_div a b H).
rewrite (surjective_pairing (a/b)) in y.
assumption.
Qed.

Lemma Z_div_mod_nolet:
  forall a b : Z,
  (b > 0)%Z ->
  a = (b * (fst (Z.div_eucl a b)) + (snd (Z.div_eucl a b)))%Z /\
 (0 <= (snd (Z.div_eucl a b)) < b)%Z.
intros.
pose (Z_div_mod a b H).
rewrite (surjective_pairing (Z.div_eucl a b)) in y.
assumption.
Qed.

Lemma phi_mod : forall w, (phi w mod 2 ^ Z.of_nat size = phi w)%Z.
intros.
rewrite <- phi_phi_inv.
rewrite phi_inv_phi.
trivial.
Qed.

Lemma phi_inv_mod : forall a, 
  (phi_inv a = phi_inv (a mod 2 ^ Z.of_nat size)).
intros.
rewrite <- phi_phi_inv.
rewrite phi_inv_phi.
trivial.
Qed.

Lemma power_gt_0 : forall n, (0 < 2 ^ Z.of_nat n)%Z.
intros.
apply Z.pow_pos_nonneg;omega.
Qed.


Lemma split_combine : forall n w, n < size -> w = combine_word n (split_word n w).
intros n w INEQ.
unfold split_word; unfold combine_word.
unfold add256.
unfold mul256.
rewrite phi_phi_inv.
rewrite <- !spec_mul.
unfold div256.
pose (Z.div_eucl (phi w) (phi (phi_inv (2 ^ Z.of_nat n)))).
replace (Z.div_eucl (phi w) (phi (phi_inv (2 ^ Z.of_nat n)))) with p;auto.
rewrite (surjective_pairing p).
simpl.
unfold mul256.
rewrite !phi_phi_inv.
rewrite phi_inv_mod.
rewrite <- Zmult_mod.
rewrite <- Zplus_mod.
rewrite <- !phi_phi_inv.
elim (spec_div_nolet w  (phi_inv (2 ^ Z.of_nat n)));intros.
unfold div256 in H.
replace (Z.div_eucl (phi w) (phi (phi_inv (2 ^ Z.of_nat n)))) with p in H;auto.
rewrite (surjective_pairing p) in H.
simpl in H.
rewrite !phi_phi_inv in H.
rewrite phi_inv_phi.
apply phi_eq_lemma.
rewrite phi_phi_inv.
rewrite <- phi_mod.
rewrite <- phi_mod.
rewrite H.
rewrite Zplus_mod.
rewrite Zmult_mod.
rewrite Zplus_mod.
rewrite <- !Zmult_mod.
rewrite <- !Zplus_mod.
rewrite Z.mod_mod.
rewrite Zplus_mod_idemp_r.
auto.
apply not_eq_sym.
apply Z.lt_neq.

apply Z.pow_pos_nonneg;try omega.
rewrite phi_phi_inv.
rewrite Zmod_eq.
replace (2 ^ Z.of_nat n / 2 ^ Z.of_nat size)%Z with 0%Z.
simpl.
rewrite Z.sub_0_r.
apply power_gt_0.

apply eq_sym.
apply Zdiv_small.
split.
apply Z.lt_le_incl.
apply power_gt_0.

apply Z.pow_lt_mono_r;omega.
Search (_ < _ -> _ > _)%Z.
apply Z.lt_gt.
apply power_gt_0.
Qed.

Definition word_of_byte (b:byte) := Int256.phi_inv (Int8.phi b).
Definition byte_of_word (w:word) := Int8.phi_inv (Int256.phi w).

(*
  Fixpoint word_nth_byte (w : word) (n : nat) : byte := match n with
   | O => byte_of_word (snd (split_word 8%nat w))
   | S n => word_nth_byte (fst (split_word 8%nat w)) n
  end.
*)

  Fixpoint word_nth_byte_aux (w : word) (n : nat) : word := match n with
   | O => snd (split_word 8%nat w)
   | S n => word_nth_byte_aux (fst (split_word 8%nat w)) n
  end.

Definition word_nth_byte w n := byte_of_word (word_nth_byte_aux w n).

Fixpoint word_of_bytes lst := match lst with
 | nil => On
 | a::lst => combine_word 8%nat (word_of_bytes lst, word_of_byte a)
end.

Require Cyclic8.

Lemma w_b : forall w, (phi w < 2 ^ 8)%Z -> word_of_byte (byte_of_word w) = w.
unfold word_of_byte.
unfold byte_of_word.
intros.
Require Import Cyclic8.
rewrite phi_phi_inv.
rewrite Zmod_small.
Require Import Cyclic256.
rewrite phi_inv_phi;trivial.
split.
apply phi_bounded.
simpl in *.
assumption.
Qed.

  Open Scope list_scope.

  Import ListNotations.

Lemma power_zero_small : forall n m, n < m ->
   (0 <= 2 ^ Z.of_nat n < 2 ^ Z.of_nat m)%Z.
split.
try apply Z.lt_le_incl; apply power_gt_0.
apply Z.pow_lt_mono_r;simpl;try omega.
Qed.

Lemma split_small : forall w, (phi (snd (split_word 8 w)) < 2 ^ 8)%Z.
intros.
unfold split_word.
unfold div256.
pose (Z.div_eucl (phi w) (phi (phi_inv (2 ^ Z.of_nat 8)))).
replace (Z.div_eucl (phi w) (phi (phi_inv (2 ^ Z.of_nat 8)))) with p; trivial.
rewrite (surjective_pairing p); simpl.
elim (Z_div_mod_nolet (phi w) (phi (phi_inv (2 ^ Z.of_nat 8))));intros.
replace (Z.div_eucl (phi w) (phi (phi_inv (2 ^ Z.of_nat 8)))) with p in H0; trivial.
rewrite phi_phi_inv.
rewrite phi_phi_inv in H0.
assert (snd p < 2 ^ Z.of_nat 8)%Z.
replace (2 ^ Z.of_nat 8 mod 2 ^ Z.of_nat size)%Z with (2 ^ Z.of_nat 8)%Z in H0.
apply H0.
rewrite Zmod_small;trivial.
apply power_zero_small;unfold size;omega.
rewrite Zmod_small;trivial.
split.
apply H0.
eapply Z.lt_trans.
eassumption.
apply Z.pow_lt_mono_r;simpl;try omega.
rewrite phi_phi_inv.
rewrite Zmod_small;trivial.
try apply Z.lt_gt; try apply Z.lt_le_incl; apply power_gt_0.
apply power_zero_small;unfold size;omega.
Qed.

Lemma word_nth_aux1 :
 forall n w, exists w2, word_nth_byte_aux w n = snd (split_word 8 w2).
induction n;intros.
simpl.
exists w; auto.
simpl.
apply (IHn (fst (split_word 8 w))).
Qed.


Lemma word_nth_aux :
 forall n w, word_of_byte (word_nth_byte w n) = word_nth_byte_aux w n.
intros.
unfold word_nth_byte.
rewrite w_b;trivial.
elim (word_nth_aux1 n w);intros.
rewrite H.
apply split_small.
Qed.

Lemma words_of_nth_bytes_aux : forall lst w,
word_of_bytes lst = fst (split_word 8 w) ->
word_of_bytes (word_nth_byte w 0::lst) = w.
intros.
simpl.
rewrite word_nth_aux.
simpl.
rewrite H.
rewrite <- surjective_pairing.
rewrite <- split_combine;trivial;unfold size;omega.
Qed.

Lemma split_nth_byte : forall w n, word_nth_byte w (S n) = word_nth_byte (fst (split_word 8 w)) n.
intros.
unfold word_nth_byte.
simpl.
auto.
Qed.

Lemma div_eucl_fst : forall a b, (b > 0)%Z -> fst (Z.div_eucl a b) = (a / b)%Z.
intros.
Search (Z.div_eucl).
pose (Z_div_mod a b H).
rewrite (surjective_pairing (Z.div_eucl a b)) in y.
elim y;clear y;intros.
rewrite (Zdiv_unique a b (fst (Z.div_eucl a b)) (snd (Z.div_eucl a b)));auto.
Qed.

Definition Z2pow8 :Z := 2^Z.of_nat 8%nat.

Lemma z2pow8 : phi (phi_inv Z2pow8) = Z2pow8.
apply phi_phi_inv.
Qed.

Lemma phi_div_fst : forall a,
  phi (fst (a/phi_inv Z2pow8)) = (phi a/Z2pow8)%Z.
intros.
elim (spec_div_nolet a (phi_inv Z2pow8)); intros.
rewrite <- z2pow8 at 2.
rewrite (Zdiv_unique (phi a) (phi (phi_inv Z2pow8)) 
   (phi (fst (a / phi_inv Z2pow8)%int256))
   (phi (snd (a / phi_inv Z2pow8)%int256)));auto.
rewrite Z.mul_comm.
assumption.
rewrite z2pow8; unfold Z2pow8.
apply power_gt_0.
Qed.

(*
Lemma split_add : forall n m w,
 fst (split_word n (fst (split_word m w))) = fst (split_word (n+m) w).
intros.
unfold split_word.
unfold div256.

rewrite (surjective_pairing (Z.div_eucl (phi w) (phi (phi_inv (2 ^ Z.of_nat m))))).
simpl.
rewrite (surjective_pairing (Z.div_eucl (phi w) (phi (phi_inv (2 ^ Z.of_nat (n + m)))))).
simpl.
rewrite (surjective_pairing (Z.div_eucl
       (phi (phi_inv (fst (Z.div_eucl (phi w) (phi (phi_inv (2 ^ Z.of_nat m)))))))
       (phi (phi_inv (2 ^ Z.of_nat n))))); simpl.
rewrite !div_eucl_fst.

Check spec_div_nolet.

rewrite !phi_phi_inv.

elim (spec_div_nolet (fst (w / phi_inv (2 ^ Z.of_nat m))) (phi_inv (2 ^ Z.of_nat n))); intros.
elim (spec_div_nolet w (phi_inv (2 ^ Z.of_nat m))); intros.
elim (spec_div_nolet w (phi_inv (2 ^ Z.of_nat (n+m)))); intros.
unfold div256.


pose (Z.div_eucl (phi w) (phi (phi_inv (2 ^ Z.of_nat m)))).
replace (Z.div_eucl (phi w) (phi (phi_inv (2 ^ Z.of_nat m)))) with p; trivial.
rewrite (surjective_pairing p); simpl.
pose (Z.div_eucl (phi (phi_inv (fst p))) (phi (phi_inv (2 ^ Z.of_nat n)))).
replace (Z.div_eucl (phi (phi_inv (fst p))) (phi (phi_inv (2 ^ Z.of_nat n)))) with p0; trivial.
rewrite (surjective_pairing p0); simpl.

pose (Z.div_eucl (phi w) (phi (phi_inv (2 ^ Z.of_nat (n + m))))).
replace (Z.div_eucl (phi w) (phi (phi_inv (2 ^ Z.of_nat (n + m))))) with p1; trivial.
rewrite (surjective_pairing p1); simpl.
apply phi_eq_lemma.
Check phi_phi_inv.
setoid_rewrite (surjective_pairing (Z.div_eucl (phi w) (phi (phi_inv (2 ^ Z.of_nat m))))) in p.
assert (p = p0).
apply phi_eq_lemma.

Z_div_mod_nolet.
*)

Lemma Zdiv_Z2pow8 : forall a n m,
 (a / 2^(Z.of_nat n) / 2^(Z.of_nat m))%Z = (a / 2^(Z.of_nat (n+m)))%Z.
intros.
rewrite Zdiv_Zdiv.
Search (?a ^ _ * ?a ^ _)%Z.
rewrite <- Z.pow_add_r; try omega.
Search (Z.of_nat (_ + _)).
rewrite Nat2Z.inj_add;trivial.
try apply Z.lt_gt; try apply Z.lt_le_incl; apply power_gt_0.
try apply Z.lt_gt; try apply Z.lt_le_incl; apply power_gt_0.
Qed.

Lemma foo_aux: forall w, On =
fst
  (split_word 8
     (fst
        (split_word 8
           (fst
              (split_word 8
                 (fst
                    (split_word 8
                       (fst
                          (split_word 8
                             (fst
                                (split_word 8
                                   (fst
                                      (split_word 8
                                         (fst
                                            (split_word 8
                                               (fst
                                                  (split_word 8
                                                   (fst
                                                   (split_word 8
                                                   (fst
                                                   (split_word 8
                                                   (fst
                                                   (split_word 8
                                                   (fst
                                                   (split_word 8
                                                   (fst
                                                   (split_word 8
                                                   (fst
                                                   (split_word 8
                                                   (fst
                                                   (split_word 8
                                                   (fst
                                                   (split_word 8
                                                   (fst
                                                   (split_word 8
                                                   (fst
                                                   (split_word 8
                                                   (fst
                                                   (split_word 8
                                                   (fst
                                                   (split_word 8
                                                   (fst
                                                   (split_word 8
                                                   (fst
                                                   (split_word 8
                                                   (fst
                                                   (split_word 8
                                                   (fst
                                                   (split_word 8
                                                   (fst
                                                   (split_word 8
                                                   (fst
                                                   (split_word 8
                                                   (fst
                                                   (split_word 8
                                                   (fst
                                                   (split_word 8
                                                   (fst
                                                   (split_word 8
                                                   (fst
                                                   (split_word 8
                                                   (fst (split_word 8 w))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
unfold split_word.
fold Z2pow8.
intros.
apply phi_eq_lemma.
rewrite !phi_div_fst.

unfold Z2pow8.
rewrite !Zdiv_Z2pow8.
simpl.
assert (phi w < Z.pow_pos 2 256)%Z.
apply phi_bounded.
rewrite Zdiv_small;auto.
apply phi_bounded.
Qed.

Lemma words_of_nth_bytes_aux2
     : forall (lst : list byte) (w : int256),
       word_of_bytes lst = fst (split_word 8 w) ->
       phi (word_of_bytes (word_nth_byte w 0 :: lst)) = phi w.
intros.
rewrite words_of_nth_bytes_aux;auto.
Qed.

  Lemma words_of_nth_bytes :
    forall w b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31,
    b0 = word_nth_byte w 0 ->
    b1 = word_nth_byte w 1 ->
    b2 = word_nth_byte w 2 ->
    b3 = word_nth_byte w 3 ->
    b4 = word_nth_byte w 4 ->
    b5 = word_nth_byte w 5 ->
    b6 = word_nth_byte w 6 ->
    b7 = word_nth_byte w 7 ->
    b8 = word_nth_byte w 8 ->
    b9 = word_nth_byte w 9 ->
    b10 = word_nth_byte w 10 ->
    b11 = word_nth_byte w 11 ->
    b12 = word_nth_byte w 12 ->
    b13 = word_nth_byte w 13 ->
    b14 = word_nth_byte w 14 ->
    b15 = word_nth_byte w 15 ->
    b16 = word_nth_byte w 16 ->
    b17 = word_nth_byte w 17 ->
    b18 = word_nth_byte w 18 ->
    b19 = word_nth_byte w 19 ->
    b20 = word_nth_byte w 20 ->
    b21 = word_nth_byte w 21 ->
    b22 = word_nth_byte w 22 ->
    b23 = word_nth_byte w 23 ->
    b24 = word_nth_byte w 24 ->
    b25 = word_nth_byte w 25 ->
    b26 = word_nth_byte w 26 ->
    b27 = word_nth_byte w 27 ->
    b28 = word_nth_byte w 28 ->
    b29 = word_nth_byte w 29 ->
    b30 = word_nth_byte w 30 ->
    b31 = word_nth_byte w 31 ->
    word_of_bytes
    [b0; b1; b2; b3; b4; b5; b6; b7; b8; b9; b10; b11; b12; b13; b14; b15; b16;
     b17; b18; b19; b20; b21; b22; b23; b24; b25; b26; b27; b28; b29; b30; b31] =
    w.
Proof.
intros.

rewrite H.
apply words_of_nth_bytes_aux.


rewrite H0; rewrite split_nth_byte; apply words_of_nth_bytes_aux.

rewrite H1; rewrite split_nth_byte; apply words_of_nth_bytes_aux.
rewrite H2; rewrite split_nth_byte; apply words_of_nth_bytes_aux.
rewrite H3; rewrite split_nth_byte; apply words_of_nth_bytes_aux.
rewrite H4; rewrite split_nth_byte; apply words_of_nth_bytes_aux.
rewrite H5; rewrite split_nth_byte; apply words_of_nth_bytes_aux.
rewrite H6; rewrite split_nth_byte; apply words_of_nth_bytes_aux.
rewrite H7; rewrite split_nth_byte; apply words_of_nth_bytes_aux.
rewrite H8; rewrite split_nth_byte; apply words_of_nth_bytes_aux.
rewrite H9; rewrite split_nth_byte; apply words_of_nth_bytes_aux.
rewrite H10; rewrite split_nth_byte; apply words_of_nth_bytes_aux.
rewrite H11; rewrite split_nth_byte; apply words_of_nth_bytes_aux.
rewrite H12; rewrite split_nth_byte; apply words_of_nth_bytes_aux.
rewrite H13; rewrite split_nth_byte; apply words_of_nth_bytes_aux.
rewrite H14; rewrite split_nth_byte; apply words_of_nth_bytes_aux.
rewrite H15; rewrite split_nth_byte; apply words_of_nth_bytes_aux.
rewrite H16; rewrite split_nth_byte; apply words_of_nth_bytes_aux.
rewrite H17; rewrite split_nth_byte; apply words_of_nth_bytes_aux.
rewrite H18; rewrite split_nth_byte; apply words_of_nth_bytes_aux.
rewrite H19; rewrite split_nth_byte; apply words_of_nth_bytes_aux.
rewrite H20; rewrite split_nth_byte; apply words_of_nth_bytes_aux.
rewrite H21; rewrite split_nth_byte; apply words_of_nth_bytes_aux.
rewrite H22; rewrite split_nth_byte; apply words_of_nth_bytes_aux.
rewrite H23; rewrite split_nth_byte; apply words_of_nth_bytes_aux.
rewrite H24; rewrite split_nth_byte; apply words_of_nth_bytes_aux.
rewrite H25; rewrite split_nth_byte; apply words_of_nth_bytes_aux.
rewrite H26; rewrite split_nth_byte; apply words_of_nth_bytes_aux.
rewrite H27; rewrite split_nth_byte; apply words_of_nth_bytes_aux.
rewrite H28; rewrite split_nth_byte; apply words_of_nth_bytes_aux.
rewrite H29; rewrite split_nth_byte; apply words_of_nth_bytes_aux.
rewrite H30; rewrite split_nth_byte; apply words_of_nth_bytes_aux.

apply foo_aux.
Opaque split_word.
Qed.

Transparent split_word.

  Axiom event : Set.

  Axiom memory_state : Set.
  Axiom empty_memory : memory_state.

  Axiom cut_memory : word -> word -> memory_state -> list byte.
  Axiom cut_memory_zero_nil :
    forall start m, cut_memory start word_zero m = nil.

  Module ST := FMapList.Make WordOrdered.

  Definition storage := ST.t word.

  Eval compute in ST.key.

  Definition storage_load (k : word) (m : storage) : word :=
    match ST.find k m with
    | None => word_zero
    | Some x => x
    end.
  Definition storage_store (k : WordOrdered.t) (v : word) (orig : storage) : storage :=
    if word_eq word_zero v then
      ST.remove k orig
    else
      ST.add k v orig.

  Definition empty_storage : storage := ST.empty word.
  Lemma empty_storage_empty : forall idx : WordOrdered.t,
      is_true (word_iszero (storage_load idx empty_storage)).
  Proof.
    intro idx.
    compute.
    auto.
  Qed.

  Lemma word_of_zero :
    word_zero = word_of_N 0.
  Proof.
    auto.
  Qed.
  Lemma word_of_one :
    word_one = word_of_N 1.
  Proof.
    auto.
  Qed.

  Definition word_of_nat n :=
    word_of_N (N.of_nat n).

  (** Not required by the signature but useful lemmata **)

Require Import Ring256.

  Lemma word_sub_sub :
    forall a b c,
      word_sub a (word_add b c) = word_sub (word_sub a b) c.
  Proof.
intros.
unfold word_sub.
unfold word_add.
ring.
Qed.

  Lemma word_add_sub :
    forall a b c,
      word_add (word_sub a b) c =
      word_sub (word_add a c) b.
  Proof.
intros.
unfold word_sub.
unfold word_add.
ring.
Qed.

Lemma word_eq_lemma : forall a b, is_true (word_eq a b) -> a = b.
Proof.
    apply eqb256_correct.
Qed.

  Lemma word_eq_addR :
    forall a b c,
      is_true (word_eq b c) ->
      word_add a b = word_add a c.
  Proof.
    intros a b c H.
    rewrite (word_eq_lemma b c);trivial.
  Qed.

  Lemma word_addK :
    forall a b, word_sub (word_add a b) b = a.
  Proof.
unfold word_sub;unfold word_add;intros;ring.
Qed.

  Lemma word_addC :
    forall a b, word_add a b = word_add b a.
  Proof.
unfold word_sub;unfold word_add;intros;ring.
Qed.

(*
  Lemma word_sub_modulo :
    forall a b,
      ZModulo.to_Z ALEN.p (ZModulo.sub (ZModulo.to_Z ALEN.p a) b) =
      ZModulo.to_Z ALEN.p (ZModulo.sub a b).
  Admitted.
*)
  Lemma word_add_zero :
    forall a b,
      word_eq word_zero b = true ->
      word_add a b = a.
  Proof.
intros.
elim (word_eq_lemma word_zero b);trivial.
unfold word_zero;unfold word_add.
unfold ZnZ.zero;simpl.
ring.
Qed.

(*
  Lemma modulo_idem :
    forall a,
      ZnZ.to_Z (ZnZ.to_Z a) =
      ZnZ.to_Z a.
  Proof.
  Admitted.
*)
  Lemma storage_store_idem :
    forall a b c orig,
      storage_store a b (storage_store a c orig) =
      storage_store a b orig.
  Admitted.

  Lemma find_remove :
    forall a b orig,
      ST.find (elt:=word) a (ST.remove b orig) =
      if (word_eq a b) then None
      else ST.find (elt := word) a orig.
  Proof.
    intros a b orig.
    admit.
  Admitted.

  Lemma find_add :
    forall a b c orig,
      ST.find (elt:=word) a (ST.add b c orig) =
      if (word_eq a b) then Some c
      else ST.find (elt := word) a orig.
  Proof.
    intros a b c orig.
    admit.
  Admitted.

  Lemma storage_load_store :
    forall r w x orig,
      storage_load r (storage_store w x orig) =
      if word_eq r w then x else storage_load r orig.
  Proof.
    intros r w x orig.
    unfold storage_load.
    unfold storage_store.
    case_eq (word_eq word_zero x).
    {
      intro x_zero.
      case_eq (word_eq r w).
      { (* r is w *)
        intro rw.
        assert (H : r = w) by admit.
        subst.
        set (found := ST.find _ _).
        assert (H : found = None) by admit.
        rewrite H.
        (* use x_zero; a lemma for concrete word is needed *)
        admit.
      }
      {
        (* r is not w *)
        intro rw.
        (* move this lemma somewhere in the library *)
        rewrite find_remove.
        rewrite rw.
        reflexivity.
      }
    }
    {
      (* x is not zero *)
      intro x_not_zero.
      rewrite find_add.
      set (e := word_eq _ _).
      case_eq e; try solve [auto].
    }
  Admitted.

  Lemma storage_store_reorder :
    forall ak av bk bv orig,
      word_eq ak bk = false ->
      storage_store ak av (storage_store bk bv orig) =
      storage_store bk bv (storage_store ak av orig).
  Admitted.

End ConcreteWord2.
