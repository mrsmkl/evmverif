

Require Import Word NArith.
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
      if exit_point v then
        FragmentContinue v 
      else
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

End Fragment.

