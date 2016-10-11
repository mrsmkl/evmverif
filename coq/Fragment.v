

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
End Fragment.

