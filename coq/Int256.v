(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*            Benjamin Gregoire, Laurent Thery, INRIA, 2007             *)
(************************************************************************)

Require Import NaryFunctions.
Require Import Wf_nat.
Require Export ZArith.
Require Export DoubleType.

(** * 31-bit integers *)

(** This file contains basic definitions of a 31-bit integer
  arithmetic. In fact it is more general than that. The only reason
  for this use of 31 is the underlying mecanism for hardware-efficient
  computations by A. Spiwack. Apart from this, a switch to, say,
  63-bit integers is now just a matter of replacing every occurrences
  of 31 by 63. This is actually made possible by the use of
  dependently-typed n-ary constructions for the inductive type
  [int31], its constructor [I31] and any pattern matching on it.
  If you modify this file, please preserve this genericity.  *)

Definition size := 256%nat.

(** Digits *)

Inductive digits : Type := D0 | D1.

(** The type of 31-bit integers *)

(** The type [int31] has a unique constructor [I31] that expects
   31 arguments of type [digits]. *)

Definition digits256 t := Eval compute in nfun digits size t.

Inductive int256 : Type := I256 : digits256 int256.


Delimit Scope int256_scope with int256.
Bind Scope int256_scope with int256.
Local Open Scope int256_scope.

(** * Constants *)

(** Zero is [I31 D0 ... D0] *)
Definition On := Eval compute in napply_cst _ _ D0 size I256.

(** One is [I31 D0 ... D0 D1] *)
Definition In := Eval compute in (napply_cst _ _ D0 (size-1) I256) D1.

(** The biggest integer is [I31 D1 ... D1], corresponding to [(2^size)-1] *)
Definition Tn := Eval compute in napply_cst _ _ D1 size I256.

(** Two is [I31 D0 ... D0 D1 D0] *)
Definition Twon := Eval compute in (napply_cst _ _ D0 (size-2) I256) D1 D0.

(** * Bits manipulation *)


(** [sneakr b x] shifts [x] to the right by one bit.
   Rightmost digit is lost while leftmost digit becomes [b].
   Pseudo-code is
    [ match x with (I31 d0 ... dN) => I31 b d0 ... d(N-1) end ]
*)

Definition sneakr : digits -> int256 -> int256 := Eval compute in
 fun b => int256_rect _ (napply_except_last _ _ (size-1) (I256 b)).

(** [sneakl b x] shifts [x] to the left by one bit.
   Leftmost digit is lost while rightmost digit becomes [b].
   Pseudo-code is
    [ match x with (I31 d0 ... dN) => I31 d1 ... dN b end ]
*)

Definition sneakl : digits -> int256 -> int256 := Eval compute in
 fun b => int256_rect _ (fun _ => napply_then_last _ _ b (size-1) I256).


(** [shiftl], [shiftr], [twice] and [twice_plus_one] are direct
    consequences of [sneakl] and [sneakr]. *)

Definition shiftl := sneakl D0.
Definition shiftr := sneakr D0.
Definition twice := sneakl D0.
Definition twice_plus_one := sneakl D1.

(** [firstl x] returns the leftmost digit of number [x].
    Pseudo-code is [ match x with (I31 d0 ... dN) => d0 end ] *)

Definition firstl : int256 -> digits := Eval compute in
 int256_rect _ (fun d => napply_discard _ _ d (size-1)).

(** [firstr x] returns the rightmost digit of number [x].
    Pseudo-code is [ match x with (I31 d0 ... dN) => dN end ] *)

Definition firstr : int256 -> digits := Eval compute in
 int256_rect _ (napply_discard _ _ (fun d=>d) (size-1)).

(** [iszero x] is true iff [x = I31 D0 ... D0]. Pseudo-code is
    [ match x with (I31 D0 ... D0) => true | _ => false end ] *)

Definition iszero : int256 -> bool := Eval compute in
 let f d b := match d with D0 => b | D1 => false end
 in int256_rect _ (nfold_bis _ _ f true size).

(* NB: DO NOT transform the above match in a nicer (if then else).
   It seems to work, but later "unfold iszero" takes forever. *)


(** [base] is [2^31], obtained via iterations of [Z.double].
   It can also be seen as the smallest b > 0 s.t. phi_inv b = 0
   (see below) *)

Definition base := Eval compute in
 iter_nat size Z Z.double 1%Z.

(** * Recursors *)

Fixpoint recl_aux (n:nat)(A:Type)(case0:A)(caserec:digits->int256->A->A)
 (i:int256) : A :=
  match n with
  | O => case0
  | S next =>
          if iszero i then
             case0
          else
             let si := shiftl i in
             caserec (firstl i) si (recl_aux next A case0 caserec si)
  end.

Fixpoint recr_aux (n:nat)(A:Type)(case0:A)(caserec:digits->int256->A->A)
 (i:int256) : A :=
  match n with
  | O => case0
  | S next =>
          if iszero i then
             case0
          else
             let si := shiftr i in
             caserec (firstr i) si (recr_aux next A case0 caserec si)
  end.

Definition recl := recl_aux size.
Definition recr := recr_aux size.

(** * Conversions *)

(** From int31 to Z, we simply iterates [Z.double] or [Z.succ_double]. *)

Definition phi : int256 -> Z :=
 recr Z (0%Z)
  (fun b _ => match b with D0 => Z.double | D1 => Z.succ_double end).

(** From positive to int31. An abstract definition could be :
      [ phi_inv (2n) = 2*(phi_inv n) /\
        phi_inv 2n+1 = 2*(phi_inv n) + 1 ] *)

Fixpoint phi_inv_positive p :=
  match p with
    | xI q => twice_plus_one (phi_inv_positive q)
    | xO q => twice (phi_inv_positive q)
    | xH => In
  end.

(** The negative part : 2-complement  *)

Fixpoint complement_negative p :=
  match p with
    | xI q => twice (complement_negative q)
    | xO q => twice_plus_one (complement_negative q)
    | xH => twice Tn
  end.

(** A simple incrementation function *)

Definition incr :=
 recr int256 In
   (fun b si rec => match b with
     | D0 => sneakl D1 si
     | D1 => sneakl D0 rec end).

(** We can now define the conversion from Z to int31. *)

Definition phi_inv := fun n =>
 match n with
 | Z0 => On
 | Zpos p => phi_inv_positive p
 | Zneg p => incr (complement_negative p)
 end.

(** [phi_inv2] is similar to [phi_inv] but returns a double word
    [zn2z int31] *)

Definition phi_inv2 n :=
  match n with
  | Z0 => W0
  | _ => WW (phi_inv (n/base)%Z) (phi_inv n)
  end.

(** [phi2] is similar to [phi] but takes a double word (two args) *)

Definition phi2 nh nl :=
  ((phi nh)*base+(phi nl))%Z.

(** * Addition *)

(** Addition modulo [2^31] *)

Definition add256 n m := phi_inv ((phi n)+(phi m)).
Notation "n + m" := (add256 n m) : int256_scope.

(** Addition with carry (the result is thus exact) *)

(* spiwack : when executed in non-compiled*)
(* mode, (phi n)+(phi m) is computed twice*)
(* it may be considered to optimize it *)

Definition add256c n m :=
  let npm := n+m in
  match (phi npm ?= (phi n)+(phi m))%Z with
  | Eq => C0 npm
  | _ => C1 npm
  end.
Notation "n '+c' m" := (add256c n m) (at level 50, no associativity) : int256_scope.

(**  Addition plus one with carry (the result is thus exact) *)

Definition add256carryc n m :=
  let npmpone_exact := ((phi n)+(phi m)+1)%Z in
  let npmpone := phi_inv npmpone_exact in
  match (phi npmpone ?= npmpone_exact)%Z with
  | Eq => C0 npmpone
  | _ => C1 npmpone
  end.

(** * Substraction *)

(** Subtraction modulo [2^31] *)

Definition sub256 n m := phi_inv ((phi n)-(phi m)).
Notation "n - m" := (sub256 n m) : int256_scope.

(** Subtraction with carry (thus exact) *)

Definition sub256c n m :=
  let nmm := n-m in
  match (phi nmm ?= (phi n)-(phi m))%Z with
  | Eq => C0 nmm
  | _ => C1 nmm
  end.
Notation "n '-c' m" := (sub256c n m) (at level 50, no associativity) : int256_scope.

(** subtraction minus one with carry (thus exact) *)

Definition sub256carryc n m :=
  let nmmmone_exact := ((phi n)-(phi m)-1)%Z in
  let nmmmone := phi_inv nmmmone_exact in
  match (phi nmmmone ?= nmmmone_exact)%Z with
  | Eq => C0 nmmmone
  | _ => C1 nmmmone
  end.

(** Opposite *)

Definition opp256 x := On - x.
Notation "- x" := (opp256 x) : int256_scope.

(** Multiplication *)

(** multiplication modulo [2^31] *)

Definition mul256 n m := phi_inv ((phi n)*(phi m)).
Notation "n * m" := (mul256 n m) : int256_scope.

(** multiplication with double word result (thus exact) *)

Definition mul256c n m := phi_inv2 ((phi n)*(phi m)).
Notation "n '*c' m" := (mul256c n m) (at level 40, no associativity) : int256_scope.


(** * Division *)

(** Division of a double size word modulo [2^31] *)

Definition div25621 nh nl m :=
  let (q,r) := Z.div_eucl (phi2 nh nl) (phi m) in
  (phi_inv q, phi_inv r).

(** Division modulo [2^31] *)

Definition div256 n m :=
  let (q,r) := Z.div_eucl (phi n) (phi m) in
  (phi_inv q, phi_inv r).
Notation "n / m" := (div256 n m) : int256_scope.


(** * Unsigned comparison *)

Definition compare256 n m := ((phi n)?=(phi m))%Z.
Notation "n ?= m" := (compare256 n m) (at level 70, no associativity) : int256_scope.

Definition eqb256 n m :=
 match n ?= m with Eq => true | _ => false end.


(** Computing the [i]-th iterate of a function:
    [iter_int31 i A f = f^i] *)

Definition iter_int256 i A f :=
  recr (A->A) (fun x => x)
   (fun b si rec => match b with
      | D0 => fun x => rec (rec x)
      | D1 => fun x => f (rec (rec x))
    end)
    i.

(** Combining the [(31-p)] low bits of [i] above the [p] high bits of [j]:
    [addmuldiv31 p i j = i*2^p+j/2^(31-p)]  (modulo [2^31]) *)

Definition addmuldiv256 p i j :=
 let (res, _ ) :=
 iter_int256 p (int256*int256)
  (fun ij => let (i,j) := ij in (sneakl (firstl j) i, shiftl j))
  (i,j)
 in
 res.

(** Bitwise operations *)

Definition lor256 n m := phi_inv (Z.lor (phi n) (phi m)).
Definition land256 n m := phi_inv (Z.land (phi n) (phi m)).
Definition lxor256 n m := phi_inv (Z.lxor (phi n) (phi m)).


Definition lnot256 n := lxor256 Tn n.
Definition ldiff256 n m := land256 n (lnot256 m).

Fixpoint euler (guard:nat) i j {struct guard} :=
  match guard with
    | O => In
    | S p => match j ?= On with
               | Eq => i
               | _ => euler p j (let (_, r ) := i/j in r)
             end
  end.

Definition gcd256 i j := euler (2*size)%nat i j.

(** Square root functions using newton iteration
    we use a very naive upper-bound on the iteration
    2^31 instead of the usual 31.
**)



Definition sqrt256_step (rec: int256 -> int256 -> int256) (i j: int256)  :=
Eval lazy delta [Twon] in
  let (quo,_) := i/j in
  match quo ?= j with
    Lt => rec i (fst ((j + quo)/Twon))
  | _ =>  j
  end.

Fixpoint iter256_sqrt (n: nat) (rec: int256 -> int256 -> int256)
          i j {struct n} :=
  sqrt256_step
   (match n with
      O =>  rec
   | S n => (iter256_sqrt n (iter256_sqrt n rec))
   end) i j.

Definition sqrt256 i :=
Eval lazy delta [On In Twon] in
  match compare256 In i with
    Gt => On
  | Eq => In
  | Lt => iter256_sqrt 256 (fun i j => j) i (fst (i/Twon))
  end.

Definition v255 := Eval compute in (addmuldiv256 (phi_inv (Z.of_nat size - 1)) In On).

Definition sqrt2562_step (rec: int256 -> int256 -> int256 -> int256)
   ih il j  :=
Eval lazy delta [Twon v255] in
  match ih ?= j with Eq => j | Gt => j | _ =>
  let (quo,_) := div25621 ih il j in
  match quo ?= j with
    Lt => let m := match j +c quo with
                    C0 m1 => fst (m1/Twon)
                  | C1 m1 => fst (m1/Twon) + v255
                  end in rec ih il m
  | _ =>  j
  end end.

Fixpoint iter2562_sqrt (n: nat)
          (rec: int256  -> int256 -> int256 -> int256)
          ih il j {struct n} :=
  sqrt2562_step
   (match n with
      O =>  rec
   | S n => (iter2562_sqrt n (iter2562_sqrt n rec))
   end) ih il j.

Definition sqrt2562 ih il :=
Eval lazy delta [On In] in
  let s := iter2562_sqrt 256 (fun ih il j => j) ih il Tn in
           match s *c s with
            W0 => (On, C0 On) (* impossible *)
          | WW ih1 il1 =>
             match il -c il1 with
                C0 il2 =>
                  match ih ?= ih1 with
                    Gt => (s, C1 il2)
                  | _  => (s, C0 il2)
                  end
              | C1 il2 =>
                  match (ih - In) ?= ih1 with (* we could parametrize ih - 1 *)
                    Gt => (s, C1 il2)
                  | _  => (s, C0 il2)
                  end
              end
          end.


Fixpoint p2i n p : (N*int256)%type :=
  match n with
    | O => (Npos p, On)
    | S n => match p with
               | xO p => let (r,i) := p2i n p in (r, Twon*i)
               | xI p => let (r,i) := p2i n p in (r, Twon*i+In)
               | xH => (N0, In)
             end
  end.

Definition positive_to_int256 (p:positive) := p2i size p.

(** Constant 31 converted into type int31.
    It is used as default answer for numbers of zeros
    in [head0] and [tail0] *)

Definition T256 : int256 := Eval compute in phi_inv (Z.of_nat size).

Definition head0256 i :=
  recl _ (fun _ => T256)
   (fun b si rec n => match b with
     | D0 => rec (add256 n In)
     | D1 => n
    end)
   i On.

Definition tail0256 (i:int256) :=
  recr _ (fun _ => T256)
   (fun b si rec n => match b with
     | D0 => rec (add256 n In)
     | D1 => n
    end)
   i On.
