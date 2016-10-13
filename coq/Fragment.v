

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

Inductive f_result :=
| FToWorld : contract_action ->
                   storage ->
                   (address -> word) ->
                   option variable_env -> f_result
| FInvalid : f_result
| FContinue : variable_env -> f_result
| FFinish : variable_env -> f_result.

Definition f_step (exit_point:_ -> bool) c v :=
  match v with
    | FContinue v =>
      if exit_point v then FFinish v else
      match v.(venv_prg_sfx) with
      | nil => FToWorld ContractFail v.(venv_storage_at_call) v.(venv_balance_at_call) None
      | i :: _ =>
        match instruction_sem v c i with
        | InstructionContinue new_v =>
          FContinue new_v
        | InstructionToWorld ContractFail opt_pushed_v =>
          FToWorld ContractFail v.(venv_storage_at_call) v.(venv_balance_at_call) opt_pushed_v
        | InstructionToWorld (ContractCall args) (Some new_v) =>
          FToWorld (ContractCall args) new_v.(venv_storage) new_v.(venv_balance) (Some new_v)
        | InstructionToWorld a opt_pushed_v =>
          FToWorld a v.(venv_storage) v.(venv_balance) opt_pushed_v
        | InstructionInvalid => FInvalid
        end
      end
    | a => a
  end.

Fixpoint f_step_iter (exit_point:_ -> bool) c v steps :=
  match steps with
  | O => v
  | S steps => f_step_iter exit_point c (f_step exit_point c v) steps
end.

Definition f_step_big exit_point c v steps :=
  match f_step_iter exit_point c (FContinue v) steps with
  | FContinue _ => FragmentStepRunOut
  | FFinish v => FragmentContinue v
  | FInvalid => FragmentInvalid
  | FToWorld x1 x2 x3 x4 => FragmentToWorld x1 x2 x3 x4
  end.

Lemma f_step_tail : forall steps cond c v,
  f_step cond c (f_step_iter cond c v steps) = 
  (f_step_iter cond c v (S steps)).
induction steps;auto;intros.
simpl.
rewrite IHsteps.
auto.
Qed.

Lemma iter_world : forall cond c n x1 x2 x3 x4,
  f_step_iter cond c (FToWorld x1 x2 x3 x4) n = FToWorld x1 x2 x3 x4.
induction n; intros; auto.
rewrite <- IHn at 2.
auto.
Qed.

Lemma iter_invalid : forall cond c n, f_step_iter cond c FInvalid n = FInvalid.
induction n; intros; auto.
Qed.

Lemma iter_finish : forall cond c n v,
   f_step_iter cond c (FFinish v) n = FFinish v.
induction n; intros; auto.
rewrite <- IHn at 2.
auto.
Qed.

Lemma big_small : forall steps cond c v,
  f_step_big cond c v steps = fragment_sem cond v c steps.
induction steps; intros; auto.
simpl.
unfold f_step_big.
simpl.

elim (bool_tf (cond v)); intros; auto; rewrite H in *.

destruct (venv_prg_sfx v).
rewrite iter_world; auto.

destruct (instruction_sem v c i).
rewrite <- IHsteps.
auto.

destruct c0; destruct o; rewrite iter_world; auto.

rewrite iter_invalid; auto.

rewrite iter_finish; auto.
Qed.

(*
Lemma iter_cond_true : forall steps v c cond vv,
   FragmentContinue vv = iter_sem v c steps ->
   cond vv = true ->
   exists steps2 vv2, FragmentContinue vv2 = fragment_sem cond v c steps2.
induction steps; intros.
simpl in H.
exists (S O).
exists vv.
simpl.
inversion H.
rewrite H2 in *.
rewrite H0 in *.
trivial.
elim (iter_seq steps v c vv); intros; auto.
Check (IHsteps v c cond x H1).
eapply IHsteps.


Lemma iter_cond_false : forall steps v c cond vv,
   FragmentContinue vv = iter_sem v c steps ->
   cond vv = false ->
   FragmentStepRunOut = fragment_sem cond v c steps ->
   FragmentStepRunOut = fragment_sem cond v c (S steps).

induction steps; intros; auto.

elim (bool_tf (cond v)); intros; auto.
simpl; simpl in H.
rewrite H1 in *.

destruct (venv_prg_sfx v).
inversion H.
rewrite H2 in *.
simpl.

rewrite H4 in *.
congruence.

destruct (instruction_sem v c i).
eapply (IHsteps v0 c);eauto.
destruct c0; destruct o; inversion H.
inversion H.

simpl; simpl in H.
rewrite H1 in *.

intros.

apply (H1 _ n); try omega.

Lemma iter_cond_true : forall steps v c cond vv,
   FragmentContinue vv = iter_sem v c steps ->
   cond vv = true ->
   (forall v2 n, (n < steps)%nat -> FragmentContinue v2 = iter_sem v c n ->
    cond v2 = false) ->
   FragmentContinue vv = fragment_sem cond v c (S steps).


induction steps; intros.
simpl.
simpl in H.
inversion H.
rewrite H3 in *.
rewrite H0.
trivial.

elim (bool_tf (cond v)); intros; auto.
simpl; simpl in H.
rewrite H2 in *.

destruct (venv_prg_sfx v).
inversion H.
destruct (instruction_sem v c i).
apply (IHsteps v0 c);auto.
intros.

apply (H1 _ n); try omega.
admit.

destruct c0; destruct o; inversion H.
inversion H.


simpl; simpl in H.
rewrite H2 in *.

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
*)

Lemma step_cond : forall cond1 cond2 c v,
  f_step cond1 c v = f_step cond2 c v \/
  (exists st, v = FContinue st /\ cond1 st <> cond2 st).
intros.
destruct v; try (left; auto; omega).
elim (Bool.bool_dec (cond1 v) (cond2 v)); intros.
left.
simpl.
rewrite a; clear a.
auto.
right; exists v.
auto.
Qed.

Lemma step_weak : forall cond1 cond2 c v vv,
  (forall st, cond1 st = true -> cond2 st = true) ->
  f_step cond2 c v = FContinue vv ->
  f_step cond1 c v = FContinue vv.
intros.
unfold f_step in *.
destruct v; auto.
elim (bool_tf (cond1 v)); elim (bool_tf (cond2 v)); intros;
 rewrite H2 in *; rewrite H1 in *.
destruct (venv_prg_sfx v).
inversion H0.
destruct (instruction_sem v c i); auto.
inversion H0.
rewrite H in H1; congruence.
inversion H0.
Qed.

Lemma previous_step : forall cond c v vv,
  f_step cond c v = FContinue vv ->
  exists st, v = FContinue st.
intros.
destruct v; simpl in *; try inversion H.
exists v; auto.
Qed.

Lemma iter_step_weak : forall n cond1 cond2 c v vv,
  (forall st, cond1 st = true -> cond2 st = true) ->
  f_step_iter cond2 c v n = FContinue vv ->
  f_step_iter cond1 c v n = f_step_iter cond2 c v n.
induction n; intros; auto.
rewrite <- f_step_tail.
rewrite H0.
eapply step_weak.
eassumption.

elim (previous_step cond2 c (f_step_iter cond2 c v n) vv); auto.
intros.
erewrite (IHn cond1 cond2 c _ _); auto.
rewrite f_step_tail; auto.

eassumption.
rewrite f_step_tail; auto.
Qed.

Lemma iter_step_cond : forall n cond1 cond2 c v,
  f_step_iter cond1 c v n = f_step_iter cond2 c v n \/
  (exists m st, (m < n)%nat /\
   f_step_iter (fun _ => false) c v m = FContinue st /\ cond1 st <> cond2 st).
induction n; intros.
left; auto.
elim (IHn cond1 cond2 c v); intros.
rewrite <- f_step_tail.
rewrite <- f_step_tail.
rewrite H.
eelim (step_cond cond1 cond2 c); intros.
left; eassumption.
right.
elim H0; clear H0; intros.
elim H0; clear H0; intros.
exists n.
exists x.
intros; split; auto.
erewrite iter_step_weak; eauto.
intros; congruence.

elim H; clear H; intros.
elim H; clear H; intros.
elim H; clear H; intros.
elim H0; clear H0; intros.

right.

exists x; exists x0.
split; auto.
Qed.

(* Property for smallest number of steps ... *)

(* assertion iter cond .. P *)

Definition wakeup v := match v with
 | FFinish a => FContinue a
 | _ => FInvalid
end.

Definition finish v := match v with
 | FContinue a => FFinish a
 | _ => FInvalid
end.

Definition never (a:variable_env) := false.

Definition f_iter c v n := f_step_iter never c v n.

Require Import Classical.

Lemma f_iter_dec : forall cond c v,
     (forall n, f_step_iter cond c v n = f_iter c v n) \/
      not (forall n, f_step_iter cond c v n = f_iter c v n).
intros; apply classic.
Qed.

Lemma f_iter_exists : forall cond c v,
   not (forall n, f_step_iter cond c v n = f_iter c v n) ->
   exists m, f_step_iter cond c v m <> f_iter c v m.

intros.
elim (not_all_ex_not nat (fun n => f_step_iter cond c v n = f_iter c v n));
  intros; auto.
exists x; auto.
Qed.

Lemma eq_neq_absurd : forall A (a b : A), a = b -> a <> b -> False.
intuition.
Qed.

Lemma exists_smallest : forall A (P:A->Prop) (f:nat -> A) n,
  P (f n) -> exists m, P (f m) /\ forall k, (k < m)%nat -> not (P (f k)).
intros.
elim (dec_inh_nat_subset_has_unique_least_element (fun n => P (f n))); intros.
elim H0; clear H0; intros.
exists x.
elim H0; clear H0 H1; intros.
split; auto; intros.
intro.
pose (H1 k H3).
omega.
apply classic.
exists n; auto.
Qed.

Lemma iter_step_smallest : forall (P:f_result->Prop) cond c v n,
  P (f_step_iter cond c v n) ->
  exists m, P (f_step_iter cond c v m) /\
            forall k, (k < m)%nat -> not (P (f_step_iter cond c v k)).
intros.
eapply exists_smallest; eassumption.
Qed.

Lemma iter_step_cond2 : forall n cond c v,
  f_step_iter cond c v n = f_iter c v n \/
  (exists m st, (m < n)%nat /\
   f_iter c v m = FContinue st /\ cond st = true).
intros.
unfold f_iter.
eelim iter_step_cond; intros.
left; eassumption.
right.
elim H; clear H; intros.
elim H; clear H; intros.
elim H; clear H; intros.
elim H0; clear H0; intros.
exists x, x0.
split; auto.
split; auto.
unfold never in H1.
elim (bool_tf (cond x0)); auto.
Qed.

Lemma keep_going_while_false : forall cond v c n,
  (forall k, (k < n)%nat ->
     not (exists st, f_iter c v k = FContinue st /\ cond st = true)) ->
  f_step_iter cond c v n = f_iter c v n.
intros.
eelim iter_step_cond2; intros; try eassumption.
elim H0; clear H0; intros.
elim H0; clear H0; intros.
elim H0; clear H0; intros.
elim (H x H0).
exists x0.
auto.
Qed.

Lemma finish_at_first_true : forall cond v c n st,
  (forall k, (k < n)%nat ->
     not (exists st, f_iter c v k = FContinue st /\ cond st = true)) ->
  f_iter c v n = FContinue st -> cond st = true ->
  f_step_iter cond c v (S n) = FFinish st.

intros.
rewrite <- f_step_tail.
erewrite keep_going_while_false; auto.
rewrite H0.
unfold f_step.
rewrite H1; auto.
Qed.

Lemma iter_add : forall cond c v n m,
   f_step_iter cond c (f_step_iter cond c v n) m = f_step_iter cond c v (n+m)%nat.
intros.
induction n; auto.

Search (S _ + _ = _)%nat.
rewrite Nat.add_succ_l.

rewrite <- !f_step_tail.
rewrite <- IHn.
rewrite !f_step_tail.
unfold f_step_iter; fold f_step_iter.
rewrite !f_step_tail.
auto.
Qed.

Definition stop_at m c v n :=
  if Nat.ltb n (S m) then f_iter c v n else
  finish (f_iter c v m).

Lemma stop_at_cond : forall cond c v,
  (forall n, f_step_iter cond c v n = f_iter c v n) \/
  exists m, forall n, f_step_iter cond c v n = stop_at m c v n.
intros.

eelim f_iter_dec; intros.
left; eassumption.
right.
eelim f_iter_exists; intros; try eassumption.

eelim iter_step_cond; intros.

unfold f_iter in H0.
pose (eq_neq_absurd _ _ _ H1 H0).
tauto.

elim H1; clear H1; intros.
elim H1; clear H1; intros.
elim H1; clear H1; intros.
elim H2; clear H2; intros.

elim (iter_step_smallest
       (fun res => exists st, res = FContinue st /\ cond st = true)
       never c v x0); intros.

elim H4; clear H4; intros.
elim H4; clear H4; intros.
elim H4; clear H4; intros.

exists x2; intros.

clear H2.

unfold stop_at.

elim (bool_tf (n <? S x2)%nat); intros; rewrite H2.

unfold f_iter.

(* rewrite <- f_step_tail. *)
rewrite H4.

replace (f_step_iter never c v x2) with (f_step_iter cond c v x2) in H4.

elim (Nat.ltb_ge n (S x2)); intros.
pose (H7 H2).

elim (Nat.le_exists_sub _ _ l); intros.
elim H9; clear H9; intros.
rewrite H9.
rewrite <- Nat.add_succ_comm.
rewrite <- Nat.add_comm.
rewrite <- iter_add.
rewrite H4.
unfold finish.

simpl.
rewrite H6.
rewrite iter_finish.
auto.

apply keep_going_while_false; auto.
apply keep_going_while_false; intros.

elim (Nat.ltb_lt n (S x2)); intros.
apply H5.
pose (H8 H2).
omega.

exists x1.
split; auto.

unfold never in H3.
elim (bool_tf (cond x1)); auto.
Qed.

(* Something like this might make composition easy: *)
(*
f_step_iter n (wakeup (f_step_iter m)) = f_step_iter (n+m)
*)

Lemma not_stuck : forall c v st k, FFinish st = f_iter c (FContinue v) k -> False.
induction k.
cbv.
intros H; inversion H.
unfold f_iter in *.
rewrite <- f_step_tail.
destruct (f_step_iter never c (FContinue v) k); simpl; intros.
inversion H.
inversion H.

destruct (venv_prg_sfx v0); inversion H.
destruct (instruction_sem v0 c i); inversion H.
destruct c0; destruct o; inversion H.
tauto.
Qed.

Lemma stop_at_cond2 : forall cond c v k st,
  FFinish st = f_step_iter cond c (FContinue v) k ->
  exists m, forall n,
  f_step_iter cond c (FContinue v) n = stop_at m c (FContinue v) n.
intros.
eelim stop_at_cond; intros; eauto.
rewrite (H0 k) in H.

eelim not_stuck.
eassumption.
Qed.

Lemma glue_stop : forall c n1 n2 v1 v2 v3,
  FFinish v2 = stop_at n1 c (FContinue v1) (S n1) ->
  FFinish v3 = stop_at n2 c (FContinue v2) (S n2) ->
  FFinish v3 = stop_at (n1+n2)%nat c (FContinue v1) (S (n1+n2))%nat.
unfold stop_at.
Search (?a <? ?a)%nat.
intros c n1 n2 v1 v2 v3.
rewrite !Nat.ltb_irrefl.
unfold f_iter.
intros.
rewrite <- iter_add.
rewrite H0.
assert (FContinue v2 = f_step_iter never c (FContinue v1) n1).

unfold finish in H.
destruct (f_step_iter never c (FContinue v1) n1); inversion H; auto.

rewrite H1.
auto.
Qed.

Lemma stop_at_stable : forall c v m n,
  (S m <= n)%nat -> stop_at m c v n = stop_at m c v (S m).
intros.
unfold stop_at.
rewrite Nat.ltb_irrefl.

assert (n <? S m = false)%nat.

apply Nat.ltb_ge; auto.

rewrite H0.
auto.
Qed.

Lemma stop_at_stable2 : forall c m n v2 v3,
  FFinish v3 = stop_at m c (FContinue v2) n ->
  FFinish v3 = stop_at m c (FContinue v2) (S m).
intros c m n v2 v3.
unfold stop_at.
elim (bool_tf (n <? S m)%nat); intros.
rewrite H in H0.
rewrite !Nat.ltb_irrefl.
auto.
rewrite H in H0.
rewrite !Nat.ltb_irrefl.
eelim not_stuck; eassumption.
Qed.

Lemma what_was_finished : forall c v n st,
  FFinish st = stop_at n c v (S n) ->
  FContinue st = stop_at n c v n.

intros c v n st.
unfold stop_at.
rewrite !Nat.ltb_irrefl.
assert (n <? S n = true)%nat.
Search (_ <? _)%nat.
apply Nat.ltb_lt.
omega.
rewrite H.
unfold finish.
intros.
destruct (f_iter c v n); inversion H0; auto.
Qed.

Lemma finished_cond : forall cond n c v st,
  FFinish st = f_step_iter cond c (FContinue v) n ->
  cond st = true.
induction n; simpl; intros.
inversion H.
elim (bool_tf (cond v)); intros.
rewrite H0 in H.
destruct (venv_prg_sfx v).
rewrite iter_world in H.
inversion H.
destruct (instruction_sem v c i).
eapply IHn; eassumption.
destruct c0; destruct o.
rewrite iter_world in H; inversion H.
rewrite iter_world in H; inversion H.
rewrite iter_world in H; inversion H.
rewrite iter_world in H; inversion H.
rewrite iter_world in H; inversion H.
rewrite iter_world in H; inversion H.
rewrite iter_world in H; inversion H.
rewrite iter_world in H; inversion H.
rewrite iter_invalid in H; inversion H.
rewrite H0 in H.
rewrite iter_finish in H; inversion H.
trivial.
Qed.

Lemma stop_at_iter : forall v1 v2 x c y,
  FContinue v2 = stop_at x c (FContinue v1) y ->
  FContinue v2 = f_iter c (FContinue v1) y.
intros v1 v2 x c y.
unfold stop_at.
elim (bool_tf (y <? S x)%nat); intro H; rewrite H; intros; auto.
unfold finish in H0.
destruct (f_iter c (FContinue v1) x); inversion H0.
Qed.

Lemma glue_success_1 : forall cond c v st m,
  FContinue st = f_step_iter cond c v m ->
  cond st = true ->
  FFinish st = f_step_iter cond c v (S m).
intros.
rewrite <- f_step_tail.
rewrite <- H.
simpl.
rewrite H0.
trivial.
Qed.

Lemma find_back : forall cond n c v st,
   FContinue st = f_step_iter cond c v n ->
   exists st2, FContinue st2 = v.
induction n; intros.
simpl in H.
destruct v; inversion H.
eauto.
unfold f_step_iter in H; fold f_step_iter in H.
elim (IHn _ _ _ H); intros.
destruct v; simpl in H0; inversion H0.
clear H2.
elim (bool_tf (cond v)); intros.
rewrite H1 in H0.
eauto.
rewrite H1 in H0.
eauto.
Qed.

Lemma iter_step_weak2 : forall n cond c v vv,
  FContinue vv = f_step_iter cond c v n ->
  FContinue vv = f_iter c v n.
intros.
unfold f_iter.
apply eq_sym.
rewrite H.
eapply iter_step_weak; eauto.
unfold never.
congruence.
Qed.

Lemma iter_falses : forall cond m c v st,
  FContinue st = f_step_iter cond c v m ->
  forall n, (n < m)%nat ->
  exists st2, FContinue st2 = f_iter c v n /\ cond st2 = false.

intros.
pose (lt_le_S _ _ H0).

elim (Nat.le_exists_sub _ _ l); intros.
elim H1; clear H1; intros.
rewrite H1 in *.

(* rewrite <- Nat.add_succ_comm in H. *)
rewrite <- Nat.add_comm in H.
rewrite <- iter_add in H.

eelim find_back; intros; try apply H.

rewrite <- f_step_tail in H3.

eelim previous_step; eauto; intros.

rewrite H4 in *.
exists x1.
split.
eapply iter_step_weak2.
apply eq_sym; eassumption.

elim (bool_tf (cond x1)); intros; auto.
unfold f_step in H3.
rewrite H5 in H3.
inversion H3.
Qed.

Lemma glue_iter : forall cond1 cond2 c n1 n2 v1 v2 v3,
  (forall st, cond2 st = true -> cond1 st = true) ->
  FFinish v2 = f_step_iter cond1 c (FContinue v1) n1 ->
  FFinish v3 = f_step_iter cond2 c (FContinue v2) n2 ->
  exists m, FFinish v3 = f_step_iter cond2 c (FContinue v1) m.

intros.

elim (stop_at_cond2 cond1 c v1 n1 v2); intros; auto.
elim (stop_at_cond2 cond2 c v2 n2 v3); intros; auto.

pose (finished_cond _ _ _ _ _ H0).
pose (finished_cond _ _ _ _ _ H1).

assert (H0' := H0).
assert (H1' := H1).

rewrite H2 in H0'.
rewrite H3 in H1'.

pose (stop_at_stable2 _ _ _ _ _ H0').
pose (stop_at_stable2 _ _ _ _ _ H1').
pose (glue_stop _ _ _ _ _ _ e1 e2).

pose (what_was_finished _ _ _ _ e1).
pose (what_was_finished _ _ _ _ e2).

pose (stop_at_iter _ _ _ _ _ e4).
pose (stop_at_iter _ _ _ _ _ e5).

rewrite e6 in e7.
unfold f_iter in e7.
rewrite iter_add in e7.

exists (S (x+x0)).

apply glue_success_1;auto.

assert (rw1 := e4).
assert (rw2 := e5).
rewrite <- H2 in rw1.
rewrite <- H3 in rw2.
rewrite rw1 in rw2.

rewrite <- iter_add.

replace (f_step_iter cond2 c (FContinue v1) x) with
 (f_step_iter cond1 c (FContinue v1) x); auto.

apply eq_sym.
eapply iter_step_weak; eauto.
Qed.

Open Scope Z.

Definition program_lengthZ code := Z.of_N (program_length code).

Definition pc2 c v :=
  program_lengthZ (cenv_program c) -
  program_lengthZ (venv_prg_sfx v).

(*
Lemma cond_steps_compare : forall cond1 cond2 c v x y,
  (forall st, cond2 st = true -> cond1 st = true) ->
  (forall n : nat, f_step_iter cond1 c v n = stop_at x c v n) ->
  (forall n : nat, f_step_iter cond2 c v n = stop_at y c v n) ->
  (x <= y)%nat.
intros.

elim (Nat.le_gt_cases x y); auto; intros.

pose (lt_le_S _ _ H2).

elim (Nat.le_exists_sub _ _ l); intros.
elim H3; clear H3; intros.
rewrite H3 in H0.
clear H4 H3 l H2.
unfold stop_at in *.
*)

Definition in_locZ v c loc :=
  Z.eqb (loc + program_lengthZ v.(venv_prg_sfx))
          (program_lengthZ c.(cenv_program)).


Lemma update_pc : forall c v vv len,
  in_locZ vv c (pc2 c v + len) = true ->
  pc2 c v + len = pc2 c vv.

intros.
unfold pc2 in *.
unfold in_locN in *.

eelim Z.eqb_eq; intros.

pose (H0 H).
omega.
Qed.

Definition in_code c v := exists lst, cenv_program c = lst ++ venv_prg_sfx v.

Lemma program_lengthZ_app : forall c1 c2,
  program_lengthZ c1 + program_lengthZ c2 = program_lengthZ (c1 ++ c2).
unfold program_lengthZ.
intros.
rewrite <- program_length_app.

rewrite N2Z.inj_add.
trivial.
Qed.

Lemma Zeqb_eq : forall n m : Z, (n =? m) = true -> n = m.
intros; eelim Z.eqb_eq; eauto.
Qed.

Lemma stay_in_code : forall cond c v m st,
  in_code c v ->
  FFinish st = f_step_iter cond c (FContinue v) m ->
  in_code c st.

admit.
Admitted.

Lemma app_cons : forall A l (a:A), a::l = (a::nil) ++ l.
induction l; eauto.
Qed.

Lemma program_length_nil : program_lengthZ nil = 0.
auto.
Qed.

Lemma program_length_i : forall i, program_lengthZ (i :: nil) > 0.
intros.
destruct i; unfold program_lengthZ; simpl; omega.
Qed.

Lemma program_length_0 : forall code, program_lengthZ code >= 0.
unfold program_lengthZ.
intros.
apply Z.le_ge.
apply N2Z.is_nonneg.
Qed.

Lemma bad_length : forall i code,
  program_lengthZ (i :: code) = program_lengthZ nil -> False.
intros. 
rewrite app_cons in H.
rewrite <- program_lengthZ_app in H.
pose (program_length_0 code).

rewrite program_length_nil in H.

pose (program_length_i i).
omega.
Qed.

Lemma cons_eq : forall A (a:A) l1 l2, l1 = l2 -> a::l1 = a::l2.
congruence.
Qed.

Lemma list_prefix : forall A (code1 code2 post1 post2: list A),
  code1 ++ post1 = code2 ++ post2 ->
  length code1 = length code2 ->
  code1 = code2.
induction code1.
destruct code2; auto.
simpl; intros.
inversion H0.
destruct code2.
simpl; intros.
inversion H0.
intros.
simpl in H0.
inversion H0.
inversion H.
apply cons_eq.
eapply IHcode1; eauto.
Qed.

Lemma rev_eq : forall A (l1 l2: list A),
  rev l1 = rev l2 ->
  l1 = l2.
intros.
rewrite <- rev_involutive.
rewrite <- rev_involutive at 1.
rewrite H.
auto.
Qed.

Lemma list_postfix : forall A (code1 code2 pre1 pre2: list A),
  pre1 ++ code1 = pre2 ++ code2 ->
  length code1 = length code2 ->
  code1 = code2.
intros.
apply rev_eq.
eapply list_prefix.
rewrite <- !rev_app_distr.
apply rev_eq.
rewrite !rev_involutive.
eassumption.
rewrite !rev_length.
auto.
Qed.


Lemma program_pre_length : forall code1 code2 post1 post2,
  code1 ++ post1 = code2 ++ post2->
  program_lengthZ code1 = program_lengthZ code2 ->
  length code1 = length code2.
induction code1.
destruct code2; auto.
simpl; intros.
eelim bad_length; eauto.

destruct code2; auto.
simpl; intros.
eelim bad_length; eauto.
simpl.
intros.
apply eq_S.
eapply IHcode1.
inversion H.
eauto.
inversion H.
rewrite H2 in H0.
rewrite app_cons in H0.
rewrite (app_cons _ code2 i) in H0.
rewrite <- !program_lengthZ_app in H0.
omega.
Qed.


Lemma program_equality : forall code1 code2 pre1 pre2,
  pre1 ++ code1 = pre2 ++ code2 ->
  program_lengthZ code1 = program_lengthZ code2 ->
  code1 = code2.

induction code1.
destruct code2; auto.

intros.

eelim bad_length; eauto.

destruct code2; intros.

eelim bad_length; eauto.

assert (a = i).

assert ((pre1 ++ a :: nil) ++ code1 = (pre2 ++ i :: nil) ++ code2).

pose (IHcode1 code2 (pre1 ++ a ::nil) (pre2 ++ i::nil)).

admit.
rewrite H1 in *.

apply cons_eq.
eapply IHcode1.

rewrite app_cons in H.
replace (i :: code2) with ((i :: nil) ++ code2) in H.
rewrite app_assoc in H.
rewrite app_assoc in H at 1.
apply H.
auto.

rewrite app_cons in H0.
replace (i :: code2) with ((i :: nil) ++ code2) in H0.
rewrite <- !program_lengthZ_app in H0.
omega.
auto.
Admitted.


(* Needs to specify that it stays in fragment *)
Lemma compose_simple_fragments :
  forall (Pre P2 Post: variable_env -> Prop) c steps1 steps2 v code1 code2 rest,
  v.(venv_prg_sfx) = code1 ++ code2 ++ rest -> in_code c v -> 
  (forall v1 rest1 c1,
     v1.(venv_prg_sfx) = code1 ++ rest1 -> 
     Pre v1 ->
     exists vv, P2 vv /\
     in_locZ vv c1 (pc2 c v1 + program_lengthZ code1) = true /\
     FFinish vv = f_step_iter (fun v =>
       in_locZ v c1 (pc2 c v1 + program_lengthZ code1) ||
       in_locZ v c1 (pc2 c v1 + program_lengthZ code1 + program_lengthZ code2))%bool
       c (FContinue v1) steps1) ->
  (forall v2 rest2 c2,
     v2.(venv_prg_sfx) = code2 ++ rest2 -> 
     P2 v2 ->
     exists vv, Post vv /\
     FFinish vv =
       f_step_iter (fun v => in_locZ v c2 (pc2 c v2 + program_lengthZ code2))
             c (FContinue v2) steps2) ->
  Pre v -> exists vv, Post vv /\
  exists steps3, FFinish vv =
    f_step_iter (fun v' => in_locZ v' c (pc2 c v + program_lengthZ code1 + program_lengthZ code2))
        c (FContinue v) steps3.
intros Pre P2 Post c steps1 steps2 v code1 code2 rest H H_incode.
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
pose (fun v : variable_env => in_locZ v c (pc2 c x + program_lengthZ code2)).
replace (fun v : variable_env => in_locZ v c (pc2 c x + program_lengthZ code2))
  with b in H6; auto.
pose (fun v0 : variable_env =>
        (in_locZ v0 c (pc2 c v + program_lengthZ code1) ||
 in_locZ v0 c (pc2 c v + program_lengthZ code1 + program_lengthZ code2))%bool).
replace (fun v0 : variable_env =>
        (in_locZ v0 c (pc2 c v + program_lengthZ code1) ||
 in_locZ v0 c (pc2 c v + program_lengthZ code1 + program_lengthZ code2))%bool)
   with b0 in H4; auto.
elim (glue_iter b0 b c steps1 steps2 v x x0); intros; auto.

assert (pc2 c v + program_lengthZ code1 = pc2 c x).

apply update_pc; auto.

rewrite H7.
exists x1.
apply H1.
unfold b0.
unfold b in H1.

assert (pc2 c v + program_lengthZ code1 = pc2 c x).
apply update_pc; auto.

rewrite H7.
rewrite H1.
rewrite Bool.orb_true_r.
trivial.

clear H1.

assert (in_code c x).
eapply stay_in_code; eauto.

pose (update_pc _ _ _ _ H3).

elim H_incode; intros.
elim H1; intros.
rewrite H in H5.
unfold in_locZ in H3.
unfold pc2 in H3.

assert (program_lengthZ code1 + program_lengthZ (venv_prg_sfx x) =
  program_lengthZ (venv_prg_sfx v)).

pose (Zeqb_eq _ _ H3).
omega.

rewrite H5 in H6.
rewrite H in H7.


rewrite <- program_lengthZ_app in H7.

assert (program_lengthZ (venv_prg_sfx x) = program_lengthZ (code2 ++ rest)).
omega.

eapply program_equality; eauto.

apply eq_sym.

replace (x0 ++ code1 ++ code2 ++ rest) with
        ((x0 ++ code1) ++ code2 ++ rest) in H6.

eapply H6.

rewrite <- app_assoc.
auto.
Qed.

End Fragment.

