

Require Import NArith Word.
Require ContractSem.

Module Fragment (W:Word).

Module Sem := ContractSem.Make(W).

Export W Sem.

Inductive fragment_result :=
| FragmentStepRunOut : fragment_result
| FragmentToWorld : contract_action ->
                   storage ->
                   (address -> word) ->
                   option variable_env -> fragment_result
| FragmentInvalid : fragment_result
| FragmentContinue : variable_env -> fragment_result.

Fixpoint fragment_sem (exit_point:_ -> bool) (v : variable_env) (c :constant_env) (steps : nat)
  : fragment_result :=
  match steps with
    | O => FragmentStepRunOut
    | S remaining_steps =>
      if exit_point v then FragmentContinue v else
      match v.(venv_prg_sfx) with
      | nil => FragmentToWorld ContractFail v.(venv_storage_at_call) v.(venv_balance_at_call) None
      | i :: _ =>
        match instruction_sem v c i with
        | InstructionContinue new_v =>
          fragment_sem exit_point new_v c remaining_steps
        | InstructionToWorld ContractFail opt_pushed_v =>
          FragmentToWorld ContractFail v.(venv_storage_at_call) v.(venv_balance_at_call) opt_pushed_v
        | InstructionToWorld (ContractCall args) (Some new_v) =>
          FragmentToWorld (ContractCall args) new_v.(venv_storage) new_v.(venv_balance) (Some new_v)
        | InstructionToWorld a opt_pushed_v =>
          FragmentToWorld a v.(venv_storage) v.(venv_balance) opt_pushed_v
        (* TODO: change the balance when suicide *)
        | InstructionInvalid => FragmentInvalid
        end
      end
  end.

Require Import List.


Fixpoint program_length lst := match lst with
 | nil => 0
 | PUSH1 _ :: tl => 2 + program_length tl
 | PUSH2 _ :: tl => 3 + program_length tl
 | _ :: tl => 1 + program_length tl
end.

Definition in_loc v c loc :=
  N.eqb (N_of_word loc + program_length v.(venv_prg_sfx))
          (program_length c.(cenv_program)).

Definition not_in_range loc n m := n < N_of_word loc \/ m > N_of_word loc.

Definition pc v := program_length v.(venv_prg_sfx).

Definition fragment_range c loc n m :=
  forall v, n <= pc v <= m -> in_loc v c loc = false.

Require Import Omega.

Axiom zero_is_zero : word_iszero word_zero = true.

Axiom word_mod_small : forall large small, N_of_word small < large ->
  word_mod small (word_of_N large) = small.

Definition is_jumpdest c loc := exists code,
  N.eqb (N_of_word loc + program_length (JUMPDEST::code))
          (program_length c.(cenv_program)) = true /\
  drop_bytes (cenv_program c) (N_of_word (word_mod loc (word_of_N 256))) =
  JUMPDEST :: code.

Lemma program_length_app : forall c1 c2,
  program_length c1 + program_length c2 = program_length (c1 ++ c2).
induction c1.
auto.
intros.
destruct a; rewrite <- app_comm_cons; unfold program_length; fold program_length; rewrite <- IHc1; ring.
Qed.

Lemma code_length : forall v code loc1 loc2,
  v.(venv_prg_sfx) = PUSH1 loc1 :: JUMPI :: PUSH1 loc2 :: JUMP :: code ->
  pc v - 6 = program_length code.
intros.

unfold pc.
destruct v.
unfold venv_prg_sfx.
unfold venv_prg_sfx in H.
rewrite H.
unfold program_length.
fold program_length.
assert (2 + (1 + (2 + (1 + program_length code))) = program_length code + 6).
ring.
rewrite H0.
rewrite N.add_sub.
trivial.
Qed.

Lemma code_length2 : forall v code loc1 loc2,
  v.(venv_prg_sfx) = PUSH1 loc1 :: JUMPI :: PUSH1 loc2 :: JUMP :: code ->
  pc v = program_length code + 6.
intros.

unfold pc.
destruct v.
unfold venv_prg_sfx.
unfold venv_prg_sfx in H.
rewrite H.
unfold program_length.
fold program_length.
ring.
Qed.

Lemma code_in_fragment : forall code frag len,
  program_length frag <= len ->
  program_length code <= program_length (frag ++ code) <= program_length code + len.
intros.
rewrite <- program_length_app.
split.
rewrite N.add_comm.
apply N.le_add_r.
rewrite N.add_comm.
apply N.add_le_mono_l.
trivial.
Qed.

Lemma pc_in_range : forall v v2 code loc1 loc2 frag,
  v.(venv_prg_sfx) = PUSH1 loc1 :: JUMPI :: PUSH1 loc2 :: JUMP :: code ->
  v2.(venv_prg_sfx) = frag ++ code ->
  program_length frag <= 6 ->
  pc v - 6 <= pc v2 <= pc v.
intros.
rewrite (code_length v code loc1 loc2); auto.
rewrite (code_length2 v code loc1 loc2); auto.
unfold pc.
rewrite H0.
apply code_in_fragment.
auto.
Qed.

Lemma split_paths1 : forall v c loc1 loc2 code stack,
  v.(venv_prg_sfx) = PUSH1 loc1 :: JUMPI :: PUSH1 loc2 :: JUMP :: code ->
  v.(venv_stack) = word_zero :: stack ->
  fragment_range c loc1 (pc v - 6) (pc v) ->
  fragment_range c loc2 (pc v - 6) (pc v) ->
  is_jumpdest c loc1 ->
  is_jumpdest c loc2 ->
  N_of_word loc1 < 256 ->
  N_of_word loc2 < 256 ->
  fragment_sem (fun v => orb (in_loc v c loc1) (in_loc v c loc2)) v c 5%nat =
  FragmentContinue (venv_pop_stack 1%nat (venv_change_sfx (N_of_word loc2) v c)).
intros.
simpl.
rewrite H1.
rewrite H2.
simpl.
rewrite H; simpl.
rewrite H1.
rewrite H2; simpl.
rewrite H; simpl.
rewrite H0; simpl.

rewrite zero_is_zero;simpl.
rewrite H1.
rewrite H2; simpl.
rewrite H1.
rewrite H2; simpl.
elim H4;intros.
elim H7; clear H7; intros.
rewrite H8;simpl.
unfold in_loc.
unfold venv_prg_sfx.
rewrite H7.
rewrite Bool.orb_true_r.
simpl.
cbn.
rewrite word_mod_small in H8.
rewrite H8.
auto.
auto.

apply (pc_in_range _ _ code loc1 loc2 (JUMP::nil));auto.
apply N.leb_le;auto.

apply (pc_in_range _ _ code loc1 loc2 (JUMP::nil));auto.
apply N.leb_le;auto.

apply (pc_in_range _ _ code loc1 loc2 (PUSH1 loc2 :: JUMP :: nil));auto.
apply N.leb_le;auto.

apply (pc_in_range _ _ code loc1 loc2 (PUSH1 loc2 :: JUMP :: nil));auto.
apply N.leb_le;auto.

rewrite H.

apply (pc_in_range _ _ code loc1 loc2 (JUMPI::PUSH1 loc2 :: JUMP :: nil));auto.
apply N.leb_le;auto.

rewrite H.

apply (pc_in_range _ _ code loc1 loc2 (JUMPI::PUSH1 loc2 :: JUMP :: nil));auto.
apply N.leb_le;auto.

apply (pc_in_range _ _ code loc1 loc2 (PUSH1 loc1::JUMPI::PUSH1 loc2 :: JUMP :: nil));auto.
apply N.leb_le;auto.

apply (pc_in_range _ _ code loc1 loc2 (PUSH1 loc1::JUMPI::PUSH1 loc2 :: JUMP :: nil));auto.
apply N.leb_le;auto.

Qed.

Definition in_locN v c loc :=
  N.eqb (loc + program_length v.(venv_prg_sfx))
          (program_length c.(cenv_program)).

Lemma bool_tf : forall b, b=false \/ b = true.
destruct b;auto.
Qed.

Lemma break_condition : forall steps v1 v2 c cond,
   FragmentContinue v2 = fragment_sem cond v1 c steps ->
   cond v2 = true.
induction steps.
simpl.
intros.
inversion H.
simpl.
intros.

elim (bool_tf (cond v1));intros;rewrite H0 in H.

destruct (venv_prg_sfx v1).

inversion H.
destruct (instruction_sem v1 c i); try inversion H.
eapply IHsteps.
eassumption.
destruct c0; try inversion H.

destruct o; inversion H.
inversion H; trivial.
Qed.

Lemma runout_dec : forall res,
  FragmentStepRunOut = res \/ FragmentStepRunOut <> res.
intros.
destruct res; try (right ; congruence).
left; auto.
Qed.

Lemma can_continue :
  forall steps v c cond vv,
  FragmentContinue vv = fragment_sem cond v c (S steps) ->
  FragmentStepRunOut <> fragment_sem cond v c steps ->
  FragmentContinue vv = fragment_sem cond v c steps.
induction steps; intros.
simpl in H0.
congruence.
assert (H' := H).
simpl; simpl in H, H0.
elim (bool_tf (cond v)); intros.
rewrite H1 in *.
destruct (venv_prg_sfx v).
inversion H.
destruct (instruction_sem v c i).
apply IHsteps;auto.
destruct c0; try congruence.
congruence.
rewrite H1 in *.
trivial.
Qed.

Lemma smallest_steps : forall steps v c cond vv,
   FragmentContinue vv = fragment_sem cond v c steps ->
   exists ss,
   FragmentContinue vv = fragment_sem cond v c (S ss) /\
   FragmentStepRunOut = fragment_sem cond v c ss.
intros.
induction steps.
inversion H.
elim (runout_dec (fragment_sem cond v c steps)); intros.
exists steps; auto.
apply IHsteps.

destruct steps.
simpl in H0.
congruence.
simpl in *.
elim (bool_tf (cond v)); intros.
rewrite H1 in *.
destruct (venv_prg_sfx v).
inversion H.
destruct (instruction_sem v c i).

apply can_continue; auto.
congruence.
congruence.
rewrite H1 in *.
trivial.
Qed.

Lemma add_useless_step : forall steps v c cond vv,
  FragmentContinue vv = fragment_sem cond v c steps -> 
  FragmentContinue vv = fragment_sem cond v c (S steps).
induction steps; intros.
simpl in H; inversion H.
unfold fragment_sem; fold fragment_sem.
unfold fragment_sem in H; fold fragment_sem in H.
elim (bool_tf (cond v)); intros; rewrite H0 in *; auto.
destruct (venv_prg_sfx v).
inversion H.

destruct (instruction_sem v c i); try inversion H.
apply IHsteps; auto.
destruct c0; try inversion H.
destruct o; inversion H.
Qed.

Lemma add_useless_steps : forall n steps v c cond vv1 vv2,
  FragmentContinue vv1 = fragment_sem cond v c (steps+n) -> 
  FragmentContinue vv2 = fragment_sem cond v c steps ->
  vv1 = vv2.
induction n; intros.
Search (_ + 0 = _)%nat.
rewrite Nat.add_0_r in H.
congruence.
apply (IHn (S steps) v c cond); auto.
replace (S steps + n)%nat with (steps + S n)%nat; auto.
omega.
apply add_useless_step.
auto.
Qed.

Lemma add_steps_same : forall steps1 steps2 v c cond vv1 vv2,
  FragmentContinue vv1 = fragment_sem cond v c steps1 -> 
  FragmentContinue vv2 = fragment_sem cond v c steps2 ->
  vv1 = vv2.
intros.
elim (Nat.add_dichotomy steps1 steps2); intros.
elim H1; clear H1; intros.
rewrite <- H1 in H0.
apply eq_sym.
eapply add_useless_steps; try rewrite Nat.add_comm; eassumption.
elim H1; clear H1; intros.
rewrite <- H1 in H.
eapply add_useless_steps; try rewrite Nat.add_comm; eassumption.
Qed.

Lemma break_weaker : forall (P:variable_env -> Prop) cond1 cond2,
   (forall v, cond1 v = true -> cond2 v = true) ->
    forall steps v c vv,
    cond1 vv = true ->
    FragmentContinue vv = fragment_sem cond2 v c steps ->
    FragmentContinue vv = fragment_sem cond1 v c steps.

induction steps; intros.
simpl in H1; inversion H1.

simpl.
simpl in H1.

elim (bool_tf (cond1 v)); elim (bool_tf (cond2 v)); intros;
 rewrite H2 in *; rewrite H3 in *.

destruct (venv_prg_sfx v).
inversion H1.

destruct (instruction_sem v c i); try inversion H.

apply IHsteps; auto.

destruct c; destruct o; inversion H1;auto.

inversion H1.

inversion H1.
rewrite H5 in *.
rewrite H3 in H0.
congruence.

rewrite H in H2; congruence.
assumption.
Qed.

Fixpoint iter_sem v c steps :=
  match steps with
    | O => FragmentContinue v
    | S remaining_steps =>
      match v.(venv_prg_sfx) with
      | nil => FragmentToWorld ContractFail v.(venv_storage_at_call) v.(venv_balance_at_call) None
      | i :: _ =>
        match instruction_sem v c i with
        | InstructionContinue new_v =>
          iter_sem new_v c remaining_steps
        | InstructionToWorld ContractFail opt_pushed_v =>
          FragmentToWorld ContractFail v.(venv_storage_at_call) v.(venv_balance_at_call) opt_pushed_v
        | InstructionToWorld (ContractCall args) (Some new_v) =>
          FragmentToWorld (ContractCall args) new_v.(venv_storage) new_v.(venv_balance) (Some new_v)
        | InstructionToWorld a opt_pushed_v =>
          FragmentToWorld a v.(venv_storage) v.(venv_balance) opt_pushed_v
        | InstructionInvalid => FragmentInvalid
        end
      end
  end.

Lemma run_out_less : forall steps v c cond,
  FragmentStepRunOut = fragment_sem cond v c (S steps) ->
  FragmentStepRunOut = fragment_sem cond v c steps.
induction steps; intros; auto.
simpl.
simpl in H.
elim (bool_tf (cond v)); intros.
rewrite H0 in *.
destruct (venv_prg_sfx v); auto.
destruct (instruction_sem v c i).
apply IHsteps.
auto.
destruct c0; destruct o; inversion H.
inversion H.
rewrite H0 in *.
inversion H.
Qed.

Lemma iter_cond : forall steps v c cond vv,
   FragmentStepRunOut = fragment_sem cond v c (S steps) ->
   FragmentContinue vv = iter_sem v c steps ->
   cond vv = false.
induction steps; intros.
simpl in *.
inversion H0.
rewrite H2 in *.
elim (bool_tf (cond v)); intros; auto.
rewrite H1 in *.
inversion H.

simpl in H, H0.

elim (bool_tf (cond v)); intros; auto.
rewrite H1 in *.

destruct (venv_prg_sfx v).
inversion H.
destruct (instruction_sem v c i).
apply (IHsteps v0 c);auto.

destruct c0; destruct o; inversion H.
inversion H.
rewrite H1 in *.
inversion H.
Qed.

Lemma iter_seq : forall steps v c vv,
   FragmentContinue vv = iter_sem v c (S steps) ->
   exists v2, FragmentContinue v2 = iter_sem v c steps.
induction steps; intros.
simpl.
exists v; auto.
simpl; simpl in H.
destruct (venv_prg_sfx v).
inversion H.
destruct (instruction_sem v c i).
elim (IHsteps v0 c vv).
intros.
exists x; auto.
auto.
destruct c0; destruct o; inversion H.
inversion H.
Qed.

Lemma iter_seq_add : forall n steps v c vv,
   FragmentContinue vv = iter_sem v c (n + steps) ->
   exists v2, FragmentContinue v2 = iter_sem v c steps.
induction n; intros.
simpl in H.
exists vv; auto.
eelim (iter_seq (n+steps) v c); intros.
eapply IHn.
exact H0.
replace (S (n + steps))%nat with (S n + steps)%nat.
eassumption.
omega.
Qed.

Lemma iter_seq_all : forall n steps v c vv,
   (n < steps)%nat ->
   FragmentContinue vv = iter_sem v c steps ->
   exists v2, FragmentContinue v2 = iter_sem v c n.
intros.
elim (Nat.add_dichotomy steps n); intros.
elim H1; intros; omega.
elim H1; clear H1; intros.
eapply iter_seq_add.
rewrite H1.
eassumption.
Qed.


Lemma iter_cond_true : forall steps v c cond vv,
   FragmentContinue vv = iter_sem v c steps ->
   cond vv = true ->
   (forall v2 n, (n < steps)%nat -> FragmentContinue v2 = iter_sem v c n ->
    cond vv = false) ->
   FragmentContinue vv = fragment_sem cond v c (S steps).
induction steps; intros.
simpl.
simpl in H.
inversion H.
rewrite H2 in *.
rewrite H0.
trivial.

elim (bool_tf (cond v)); intros; auto.
simpl; simpl in H.
rewrite H1 in *.

destruct (venv_prg_sfx v).
inversion H.
destruct (instruction_sem v c i).
apply (IHsteps v0 c);auto.

destruct c0; destruct o; inversion H.
inversion H.


simpl; simpl in H.
rewrite H1 in *.

destruct (venv_prg_sfx v).
inversion H.
destruct (instruction_sem v c i).
pose (IHsteps v0 c cond vv H H0);auto.
simpl in e.
elim (bool_tf (cond v0)); intros; auto.
rewrite H2 in *.

destruct (venv_prg_sfx v0).
inversion e.
destruct (instruction_sem v0 c i0).
apply (IHsteps v1 c);auto.

destruct c0; destruct o; inversion H.
inversion H.


rewrite H1 in *.
inversion H.
Qed.


Lemma iter_fragment : forall steps v c cond vv,
   FragmentContinue vv = fragment_sem cond v c steps ->
   exists n, iter_sem v c n = fragment_sem cond v c steps.
intros.
elim (smallest_steps steps v c cond vv H); intros.
elim H0; clear H0; intros.
exists (S x).
induction x.
simpl in *.



Lemma iter_smallest_fragment : forall n v c cond vv,
   FragmentContinue vv = fragment_sem cond v c (S n) ->
   FragmentStepRunOut = fragment_sem cond v c n ->
   cond v = false ->
   iter_sem v c (S n) = fragment_sem cond v c (S n).



Lemma iter_smallest_fragment_O : forall v c cond vv,
   FragmentContinue vv = fragment_sem cond v c (S O) ->
   cond v = false ->
   iter_sem v c (S O) = fragment_sem cond v c (S O).
intros.
simpl in H.
simpl.
rewrite !H0 in *.
destruct (venv_prg_sfx v); auto.
destruct (instruction_sem v c i).
inversion H.
destruct c0; destruct o; inversion H.
inversion H.
Qed.


induction n; intros.
eapply iter_smallest_fragment_O; eassumption.

rewrite <- H.
simpl.
simpl in H.
rewrite !H1 in *.
destruct (venv_prg_sfx v); auto.
destruct (instruction_sem v c i).

simpl in H; simpl.

simpl in H0.
rewrite !H1 in *.
rewrite H1.

Lemma iter_fragment_step : forall steps v c cond vv,
    FragmentContinue vv = fragment_sem cond v c (S steps) ->
    FragmentStepRunOut = fragment_sem cond v c steps ->
   cond v = false ->
   iter_sem v c (S steps) = fragment_sem cond v c (S steps).



induction steps; intros.
simpl in H; inversion H.
simpl in H.
elim (bool_tf (cond v)); intros.
rewrite H0 in *.
destruct (venv_prg_sfx v).
inversion H.
destruct (instruction_sem v c i).
apply (IHsteps v c cond).

(* Needs to specify that it stays in fragment *)
Lemma compose_simple_fragments :
  forall (Pre P2 Post: variable_env -> Prop) c steps1 steps2 v code1 code2 rest,
  v.(venv_prg_sfx) = code1 ++ code2 ++ rest -> 
  (forall v1 rest1 c1,
     v1.(venv_prg_sfx) = code1 ++ rest1 -> 
     Pre v1 ->
     exists vv, P2 vv /\
     in_locN v c1 (pc v1 + program_length code1) = true /\
     FragmentContinue vv = fragment_sem (fun v =>
       in_locN v c1 (pc v1 + program_length code1) ||
       in_locN v c1 (pc v1 + program_length code1 + program_length code2))%bool v1 c steps1) ->
  (forall v2 rest2 c2,
     v2.(venv_prg_sfx) = code2 ++ rest2 -> 
     P2 v2 ->
     exists vv, Post vv /\
     FragmentContinue vv =
     fragment_sem (fun v => in_locN v c2 (pc v2 + program_length code2)) v2 c steps2) ->
  Pre v -> exists vv, Post vv /\
  FragmentContinue vv =
  fragment_sem (fun v' => in_locN v' c (pc v + program_length code1 + program_length code2)) v c (steps1 + steps2).
intros.
elim (H0 v (code2++rest) c H H2); intros.
clear H0.
elim H3; clear H3; intros.
elim H3; clear H3; intros.
elim (H1 x rest c); intros; auto.
elim H5; clear H5; intros.
exists x0.
split; auto.
clear H1.

End Fragment.

