(* EVM Contract Behavior Formalization *)
(* for Coq 8.5pl1 *)

(* Yoichi Hirai i@yoichihirai.com
   Creative Commons Attribution-ShareAlike 4.0 International License *)

(* This is just a sketch of an idea put together on a weekend.
   In the interactive theorem prover Coq, I (re)started reasoning
   about a contract’s behaviour where it can be called, returned
   from a call, and of course re-entered.

   My first example is a contract that always returns, for which I
   - wrote a specification [always_return]
   - wrote some EVM code [example1_program]
   - proved that the code satisfies the specification. [example1_spec_impl_match]

   Don’t take it seriously: I haven’t checked anything against the real implementation.

   - explore other strategies modelling the infinite process
     (an Ethereum contract goes through unlimited number of events),
   - translate more parts of the yellow paper: more instructions, and the gas economics
   - check the translation against real blockchain data
   - verify gradually more complex contracts
   - develop proof methodology.
*)

(* Gas is not considered among many things.  A contract in reality dies more often than described here. *)


(***
 *** Some basic <del>definitions</del> assumptions
 ***)

(* Here I'm being lazy and assuming that these things exist.
 * I hope these don't enable us to prove 0 = 1.
 *)


(* This module can be instantiated into some concrete ways and some more abstract ways. *)
(* A word can be a tuple of 256 booleans. *)
(* Alternatively a word can be thought of as some abstract values.
 * This would be interesting in bytecode analysis tools.
 *)
(* Many aspects of the EVM semantics do not care how words are represented. *)

Require Import NArith.
Require FMapList.
Require Import OrderedType.

Module Type Word.

  Parameter word : Type.

  Parameter word_eq : word -> word -> bool.
  Parameter word_add : word -> word -> word.
  Parameter word_sub : word -> word -> word.
  Parameter word_one : word.
  Parameter word_zero : word.
  Parameter word_iszero : word -> bool.
  (* TODO: state correctness of word_iszero *)
  Parameter word_smaller : word -> word -> bool.
  Parameter word_of_N : N -> word.
  Parameter N_of_word : word -> N.

  Open Scope N_scope.
  Parameter N_of_word_of_N :
    (* TODO: This 10000 is a bit arbitrary. *)
  forall (n : N), n < 10000 -> N_of_word (word_of_N n) = n.

  Parameter byte : Type.
  Parameter address : Type.
  Parameter address_of_word : word -> address.

  Parameter word_nth_byte : word -> nat -> byte.

  (* list of bytes [a; b; c] as (a * 256 + b) * 256 + c *)
  Parameter word_of_bytes : list byte -> word.

  Require Import Coq.Lists.List.
  Import ListNotations.
  Open Scope list_scope.

  Parameter words_of_nth_bytes :
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

  Parameter event : Type. (* logged events *)


  (* These depends on the choice of word.
   * In the concrete case, these can be MSet or FSet.
   *)
  Parameter memory_state : Type. (* For now I don't use the memory *)
  Parameter empty_memory : memory_state.
  Parameter cut_memory : word -> word -> memory_state -> list byte.
  Parameter cut_memory_zero_nil :
    forall start m, cut_memory start word_zero m = nil.

  Parameter storage : Type.
  Parameter storage_load : storage -> word -> word.
  Arguments storage_load idx s /.

  Parameter storage_store : word (* idx *) -> word (* value *) -> storage -> storage.

  Parameter empty_storage : storage.
  Parameter empty_storage_empty : forall idx : word,
      is_true (word_iszero (storage_load empty_storage idx)).

End Word.

Module ContractSem (W : Word).
Export W.

Definition bool_to_word (b : bool) :=
  if b then word_one else word_zero.

Arguments bool_to_word b /.

Open Scope list_scope.

Definition drop_one_element {A : Type} (lst : list A) :=
  match lst with
  | nil => nil
  | _ :: tl => tl
  end.

(***
 *** Some abstract view over EVM
 ***)

(** This part is hugely incomplete.  It misses many instructions and
    gas economy.  They will be added as necessary. *)

(* An element of type [call_arguments] describes
   arguments that an execution can attach to
   [CALL] *)
Record call_arguments :=
    { callarg_gaslimit    : word
    ; callarg_code        : address
    ; callarg_recipient   : address
    ; callarg_value       : word
    ; callarg_data        : list byte
    ; callarg_output_begin : word
    ; callarg_output_size : word
    }.

(* An element of type [return_result] is a sequence of bytes that
   [RETURN] can return. *)
Definition return_result := list byte.

(* An element of type [call_env] describes
   an environment where contract is executed
 *)
Record call_env :=
  { callenv_gaslimit : word
  ; callenv_value : word
  ; callenv_data : list byte
  ; callenv_caller : address
  ; callenv_timestap : word
  ; callenv_blocknum : word
  ; callenv_balance : address -> word
  }.


Inductive contract_action :=
| ContractCall : call_arguments -> contract_action
  (* [Call args continuation] is the behavior of [CALL] instruction
      together with all behaviors shown by the account after the [CALL].
     [args] represents the parameters of a call.
     [continuation] represents the behavior shown after the [CALL]
     instruction.  See the comment at [after_call_behavior].
   *)
| ContractFail : contract_action
  (* [Fail] is the behavior of runtime errors (e.g. jumping to an invalid
     program counter / lack of gas *)
| ContractSuicide : contract_action
| ContractReturn : return_result (* returned data *) -> contract_action.
  (* [Return ret next] is the behavior of a [RETURN], [STOP] instruction.
     Upon the next call with [env], [next env] will be the contract behavior.
   *)


(* An element of type [response_to_world] describes a strategy of a contract
   that can respond when
   1. it is called from the world
   2. it receives a callee return from the world
   3. it receives a callee failure from the world.
   Initially, when the contract has not called any other accounts,
   the points 2. and 3. are useless.
 *)
CoInductive response_to_world :=
| Respond :
    (call_env -> contract_behavior) (* what to do if called / or re-entered *) ->
    (return_result -> contract_behavior) (* what to do if the callee returns (if exists) *) ->
    (contract_behavior) (* what to do if the callee's execution fails *) ->
    response_to_world


(* An element of type [contract_behavior] describes a behavior of an
   already called contract.  A contract has four ways of giving the
   control back to the world.
   1. returning
   2. failing
   3. commiting suicide
   4. calling some account
 *)
with contract_behavior :=
| ContractAction : contract_action -> response_to_world -> contract_behavior
.


(* A useful function for reasoning.
   I was looking at http://adam.chlipala.net/cpdt/html/Coinductive.html
   around [frob].
 *)
Definition contract_action_expander (ca : contract_behavior) :=
  match ca with ContractAction a b => ContractAction a b end.

Definition response_expander (r : response_to_world) :=
  match r with Respond f g h => Respond f g h end.

Lemma contract_action_expander_eq :
  forall ca, contract_action_expander ca = ca.
Proof.
  intro ca.
  case ca.
  auto.
Qed.

Lemma response_expander_eq :
  forall r, r = response_expander r.
Proof.
  intro r.
  case r.
  auto.
Qed.

(********* What the world does on an account ***********)

Inductive world_action :=
| WorldCall : call_env -> world_action
| WorldRet  : return_result -> world_action
| WorldFail : world_action
.

Definition world := list world_action.


(********
 When [world] and [respond_to_world] meet,
 they produce a sequence of events *)

Inductive action :=
| ActionByWorld : world_action -> action
| ActionByContract : contract_action -> action.

Definition history := list action.


(******** World and the contract interact to produce a history ****)

Fixpoint specification_run (w : world) (r : response_to_world) : history :=
  match w, r with
  | nil, _ => nil
  | WorldCall call :: world_cont, Respond f _ _ =>
    match f call with
    | ContractAction cact contract_cont =>
      ActionByWorld (WorldCall call) ::
      ActionByContract cact ::
      specification_run world_cont contract_cont
    end
  | WorldRet ret :: world_cont, Respond _ r _ =>
    match (r ret) with
      ContractAction cact contract_cont =>
      ActionByWorld (WorldRet ret) ::
      ActionByContract cact ::
      specification_run world_cont contract_cont
    end
  | WorldFail :: world_cont, Respond _ _ (ContractAction cact contract_cont) =>
    ActionByWorld WorldFail ::
    ActionByContract cact ::
    specification_run world_cont contract_cont
  end.

(***
 *** Some more concrete view on EVM.
 *** This part is for interpreting bytecodes in terms of the abstract view above.
 ***)

(**
 ** Instructions
 **)

Inductive instruction :=
| PUSH1 : word -> instruction
| SLOAD
| SSTORE
| JUMP
| JUMPI
| JUMPDEST
| CALLDATASIZE
| ADD
| SUB
| ISZERO
| CALL
| RETURN
| STOP
| DUP1
| POP
.

(**
 ** Program
 **)

Definition program := list instruction.

Print N.

Require Import Recdef.

Function drop_bytes (prog : list instruction) (bytes : N)
         :=
  match prog, bytes with
  | _, N0 => prog
  | PUSH1 v :: tl, _ =>
    drop_bytes tl (bytes - 2)
  | _ :: tl, _ =>
    drop_bytes tl (bytes - 1)
  | nil, _ => nil
  end.


(**
 ** Execution Environments
 **)

Record variable_env :=
  { venv_stack : list word
  ; venv_memory : memory_state
  ; venv_storage : storage
  ; venv_prg_sfx : list instruction
  ; venv_balance : address -> word (* does this blong here?*)
  ; venv_caller : address
  ; venv_value_sent : word
  (* TODO: add the sequence of executed instructions.
     would be useful for calculating the gas *)

  (* These are necessary when throwing. *)
  ; venv_storage_at_call : storage
  ; venv_balance_at_call : address -> word

  (* TODO: use venv_balance_at_call somewhere *)
  }.

(* [update_balance adr v original] is similar to [original] except
   that [adr] is mapped to [v].
*)
Axiom update_balance : address -> word -> (address -> word) -> (address -> word).

Record constant_env :=
  { cenv_program : list instruction;
    cenv_this : address
  }.


(** Initialize variable_env variable_env . *)
Definition init_variable_env (s : storage) (bal : address -> word)
           (caller : address)
           (cenv : constant_env) (value : word) :=
  {|
    venv_stack := nil ;
    venv_memory := empty_memory ;
    venv_prg_sfx := cenv.(cenv_program) ;
    venv_storage := s ;
    venv_balance := bal ;
    venv_caller := caller ;
    venv_value_sent := value ;
    venv_storage_at_call := s ;
    venv_balance_at_call := bal ;
  |}.


(**
 **  Meaning of an instruction.
 **)

Inductive instruction_result :=
| InstructionContinue : variable_env -> instruction_result
| InstructionToWorld : contract_action -> option variable_env (* to be pushed into the call stack *) -> instruction_result
.

Definition instruction_failure_result :=
  InstructionToWorld ContractFail None.

Definition instruction_return_result (x: return_result) :=
  InstructionToWorld (ContractReturn x) None.


Definition venv_update_stack (new_stack : list word) (v : variable_env) :=
  {|
    venv_stack := new_stack ;
    venv_memory := v.(venv_memory) ;
    venv_storage := v.(venv_storage) ;
    venv_prg_sfx := v.(venv_prg_sfx) ;
    venv_balance := v.(venv_balance) ;
    venv_caller := v.(venv_caller) ;
    venv_value_sent := v.(venv_value_sent) ;
    venv_storage_at_call := v.(venv_storage_at_call) ;
    venv_balance_at_call := v.(venv_balance_at_call)
  |}.

Arguments venv_update_stack new_stack v /.

Definition venv_advance_pc (v : variable_env) :=
  {|
    venv_stack := v.(venv_stack) ;
    venv_memory := v.(venv_memory) ;
    venv_storage := v.(venv_storage) ;
    venv_prg_sfx := drop_one_element v.(venv_prg_sfx) ;
    venv_balance := v.(venv_balance) ;
    venv_caller := v.(venv_caller) ;
    venv_value_sent := v.(venv_value_sent) ;
    venv_storage_at_call := v.(venv_storage_at_call) ;
    venv_balance_at_call := v.(venv_balance_at_call)
  |}.

Arguments venv_advance_pc v /.

Require Import List.

Fixpoint venv_pop_stack (n : nat) (v : variable_env) :=
  match n with
  | O => v
  | S m =>
    venv_update_stack
      (tl v.(venv_stack))
      (venv_pop_stack m v)
  end.

Definition venv_stack_top (v : variable_env) : option word :=
  match v.(venv_stack) with
  | h :: _ => Some h
  | _ => None
  end.

Definition venv_change_sfx (pos : N) (v : variable_env)
  (c : constant_env) : variable_env :=
  {|
    venv_stack := v.(venv_stack) ;
    venv_memory := v.(venv_memory);
    venv_storage := v.(venv_storage);
    venv_prg_sfx := drop_bytes c.(cenv_program) pos ;
    venv_balance := v.(venv_balance);
    venv_caller := v.(venv_caller);
    venv_value_sent := v.(venv_value_sent);
    venv_storage_at_call := v.(venv_storage_at_call) ;
    venv_balance_at_call := v.(venv_balance_at_call)
  |}.

Arguments venv_change_sfx pos v c /.

Definition function_update (addr : word) (val : word) (f : word -> word) : (word -> word) :=
  fun x => (if word_eq x addr then val else f x).

Definition venv_update_storage (addr : word) (val : word) (v : variable_env)
           : variable_env :=
  {|
    venv_stack := v.(venv_stack) ;
    venv_memory := v.(venv_memory);
    venv_storage := storage_store addr val v.(venv_storage);
    venv_prg_sfx := v.(venv_prg_sfx);
    venv_balance := v.(venv_balance);
    venv_caller := v.(venv_caller);
    venv_value_sent := v.(venv_value_sent);
    venv_storage_at_call := v.(venv_storage_at_call) ;
    venv_balance_at_call := v.(venv_balance_at_call)
  |}.

Definition venv_first_instruction (v : variable_env) : option instruction :=
  hd_error v.(venv_prg_sfx).

(** a general functoin for defining an instruction that
    pushes one element to the stack *)

Definition stack_0_0_op (v : variable_env) (c : constant_env)
  : instruction_result :=
  InstructionContinue (venv_advance_pc v).

Definition stack_0_1_op (v : variable_env) (c : constant_env) (w : word) : instruction_result :=
  InstructionContinue
    (venv_advance_pc (venv_update_stack (w :: v.(venv_stack)) v)).


(* These are just assumed for my laziness. *)
Definition stack_1_1_op (v: variable_env) (c : constant_env)
                    (f : word -> word) : instruction_result :=
  match v.(venv_stack) with
    | nil => instruction_failure_result
    | h :: t =>
      InstructionContinue
        (venv_advance_pc (venv_update_stack (f h :: t) v))
  end.

Definition stack_1_2_op (v: variable_env) (c : constant_env)
           (f : word -> (word (* new head *) * word (* new second*) ))
  : instruction_result :=
  match v.(venv_stack) with
    | nil => instruction_failure_result
    | h :: t =>
      match f h with
        (new0, new1) =>
        InstructionContinue
          (venv_advance_pc (venv_update_stack (new0 :: new1 :: t) v))
      end
  end.

Definition stack_2_1_op (v : variable_env) (c : constant_env)
                    (f : word -> word -> word) : instruction_result :=
  match v.(venv_stack) with
    | operand0 :: operand1 :: rest =>
      InstructionContinue (venv_advance_pc
                             (venv_update_stack (f operand0 operand1 :: rest) v))
    | _ => instruction_failure_result
  end.

Definition sload (v : variable_env) (idx : word) : word :=
  storage_load v.(venv_storage) idx.

Arguments sload v idx /.

Definition sstore (v : variable_env) (c : constant_env) : instruction_result :=
  match v.(venv_stack) with
    | addr :: val :: stack_tail =>
      InstructionContinue
        (venv_advance_pc
           (venv_update_stack stack_tail
                              (venv_update_storage addr val v)))
    | _ => instruction_failure_result
  end.

Definition jump (v : variable_env) (c : constant_env) : instruction_result :=
  match venv_stack_top v with
  | None => instruction_failure_result
  | Some pos =>
    let v_new := venv_change_sfx (N_of_word pos) (venv_pop_stack 1 v) c in
    match venv_first_instruction v_new with
    | Some JUMPDEST =>
        InstructionContinue v_new
    | _ => instruction_failure_result
    end
  end.

Arguments jump v c /.

Definition jumpi (v : variable_env) (c : constant_env) : instruction_result :=
  match v.(venv_stack) with
  | pos :: cond :: rest =>
    if word_iszero cond then
      InstructionContinue (venv_advance_pc (venv_pop_stack 2 v))
    else
      jump (venv_pop_stack 1 v) c (* this has to change when gas is considered *)
  | _ => instruction_failure_result
  end.

Arguments jumpi v c /.


Axiom datasize : variable_env -> word.

Definition call (v : variable_env) (c : constant_env) : instruction_result :=
  match v.(venv_stack) with
  | e0 :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: rest =>
    if word_smaller (v.(venv_balance) (c.(cenv_this))) e2 then
      InstructionToWorld ContractFail None
    else
    InstructionToWorld
      (ContractCall
         {|
           callarg_gaslimit := e0 ;
           callarg_code := address_of_word e1 ;
           callarg_recipient := address_of_word e1 ;
           callarg_value := e2 ;
           callarg_data := cut_memory e3 e4 v.(venv_memory) ;
           callarg_output_begin := e5 ;
           callarg_output_size := e6 ;
         |})
      (Some
         {|
           venv_stack := rest;
           venv_memory := v.(venv_memory);
           venv_storage := v.(venv_storage);
           venv_prg_sfx := drop_one_element (v.(venv_prg_sfx));
           venv_balance :=
             (update_balance (address_of_word e1)
                             (word_add (v.(venv_balance) (address_of_word e1)) e3)
             (update_balance c.(cenv_this)
                (word_sub (v.(venv_balance) (c.(cenv_this))) e3) v.(venv_balance)));
           venv_caller := v.(venv_caller);
           venv_value_sent := v.(venv_value_sent) ;
           venv_storage_at_call := v.(venv_storage_at_call) ;
           venv_balance_at_call := v.(venv_balance_at_call)
         |}
      )
  | _ =>
    InstructionToWorld ContractFail None (* this environment should disappear *)
  end.

Arguments call v c /.


Definition venv_returned_bytes v :=
  match v.(venv_stack) with
    | e0 :: e1 :: _ => cut_memory e0 e1 (v.(venv_memory))
    | _ => nil
  end.

Arguments venv_returned_bytes v /.

Definition ret (v : variable_env) (c : constant_env) : instruction_result :=
  InstructionToWorld (ContractReturn (venv_returned_bytes v)) None.

Definition stop (v : variable_env) (c : constant_env) : instruction_result :=
  InstructionToWorld (ContractReturn nil) None.

Definition pop (v : variable_env) (c : constant_env) : instruction_result :=
  InstructionContinue
    (venv_advance_pc (venv_update_stack
       (tail v.(venv_stack))
       v)).

Require Import Coq.Program.Basics.

Definition instruction_sem (v : variable_env) (c : constant_env) (i : instruction)
  : instruction_result :=
  match i with
  | PUSH1 w => stack_0_1_op v c w
  | SLOAD => stack_1_1_op v c (sload v)
  | SSTORE => sstore v c
  | JUMPI => jumpi v c
  | JUMP => jump v c
  | JUMPDEST => stack_0_0_op v c
  | CALLDATASIZE => stack_0_1_op v c (datasize v)
  | ADD => stack_2_1_op v c word_add
  | SUB => stack_2_1_op v c word_sub
  | ISZERO => stack_1_1_op v c (compose bool_to_word word_iszero)
  | CALL => call v c
  | RETURN => ret v c
  | STOP => stop v c
  | DUP1 => stack_1_2_op v c (fun a => (a, a))
  | POP => pop v c
  end.

Inductive program_result :=
| ProgramStepRunOut : program_result
| ProgramToWorld : contract_action ->
                   storage (* updated storage *) ->
                   (address -> word) (* updated balance *) ->
                   option variable_env (* to be pushed in the call stack *) -> program_result.


Fixpoint program_sem (v : variable_env) (c :constant_env) (steps : nat)
  : program_result :=
  match steps with
    | O => ProgramStepRunOut
    | S remaining_steps =>
      match v.(venv_prg_sfx) with
      | nil => ProgramToWorld ContractFail v.(venv_storage_at_call) v.(venv_balance_at_call) None
      | i :: _ =>
        match instruction_sem v c i with
        | InstructionContinue new_v =>
          program_sem new_v c remaining_steps
        | InstructionToWorld ContractFail opt_pushed_v =>
          ProgramToWorld ContractFail v.(venv_storage_at_call) v.(venv_balance_at_call) opt_pushed_v
        | InstructionToWorld a opt_pushed_v =>
          ProgramToWorld a v.(venv_storage) v.(venv_balance) opt_pushed_v
        (* TODO: change the balance when suicide *)
        end
      end
  end.


(****** This program semantics has to be lifted to a history *****)

Record account_state :=
  { account_address : address
  ; account_storage : storage
  ; account_code : list instruction
  ; account_ongoing_calls : list variable_env
  }.

Definition account_state_update_storage new_st orig :=
  {| account_address := orig.(account_address);
     account_code    := orig.(account_code);
     account_storage := new_st;
     account_ongoing_calls := orig.(account_ongoing_calls)
  |}.

Arguments account_state_update_storage new_st orig /.

(** The ideas is that an account state defines a response_to_world **)

Definition build_venv_called (a : account_state) (env : call_env) :
  variable_env :=
  {|
      venv_stack := nil ;
      venv_memory := empty_memory;
      venv_prg_sfx := a.(account_code) ;
      venv_storage := a.(account_storage) ;
      venv_balance := env.(callenv_balance) ;
      venv_caller := env.(callenv_caller) ;
      venv_value_sent := env.(callenv_value) ;
      venv_storage_at_call := a.(account_storage) ;
      venv_balance_at_call := env.(callenv_balance)
   |}.

Arguments build_venv_called a env /.

Definition build_cenv (a : account_state) :
    constant_env :=
    {|
      cenv_program := a.(account_code) ;
      cenv_this := a.(account_address)
   |}.


(* TODO: update the storage according to a *)
(* TODO: udpate the balance according to return_result *)
Definition build_venv_returned
  (a : account_state) (r : return_result) : option variable_env :=
  match a.(account_ongoing_calls) with
  | nil => None
  | recovered :: _ =>
    Some (venv_update_stack (word_one :: recovered.(venv_stack)) recovered)
         (* TODO: actually, need to update the memory *)
  end.

Arguments build_venv_returned a r /.

(* Since the callee failed, the balance should not be updated. *)
Definition build_venv_fail
           (a : account_state) : option variable_env :=
  match a.(account_ongoing_calls) with
  | nil => None
  | recovered :: _ =>
    Some (venv_update_stack (word_zero :: recovered.(venv_stack)) recovered)
  end.

Arguments build_venv_fail a /.

Definition account_state_pop_ongoing_call (orig : account_state) :=
  {| account_address := orig.(account_address);
     account_storage := orig.(account_storage);
     account_code := orig.(account_code);
     account_ongoing_calls := tail (orig.(account_ongoing_calls))
  |}.

Arguments account_state_pop_ongoing_call orig /.

(* TODO: use venv widely and remove other arguments *)
Definition update_account_state (prev : account_state) (act: contract_action)
           (st : storage) (bal : address -> word)
           (v_opt : option variable_env) : account_state :=
  account_state_update_storage st
        match v_opt with
        | None =>
          prev
        | Some pushed =>
          {|
            account_address := prev.(account_address) ;
            account_storage := pushed.(venv_storage) ;
            account_code := prev.(account_code) ;
            account_ongoing_calls := pushed :: prev.(account_ongoing_calls)
          |}
        end.

(* [program_result_approximate a b] holds when
   a is identical to b or a still needs more steps *)
Definition program_result_approximate (a : program_result) (b : program_result)
:=
  a = ProgramStepRunOut \/ a = b
  (* TODO: this [a = b] has to be weakened up to 2^256 in many places *).

Definition respond_to_call_correctly c a account_state_responds_to_world :=
      (forall (callenv : call_env)
          act continuation,
          c callenv = ContractAction act continuation ->
          exists pushed_venv, exists st, exists bal,
            (forall steps, program_result_approximate
             (program_sem (build_venv_called a callenv)
                          (build_cenv a) steps)
             (ProgramToWorld act st bal pushed_venv)) /\
              account_state_responds_to_world
                (account_state_update_storage st (update_account_state a act st bal pushed_venv))
                                          continuation).

Definition respond_to_return_correctly (r : return_result -> contract_behavior)
           (a : account_state)
           (account_state_responds_to_world : account_state -> response_to_world -> Prop) :=
  forall (rr : return_result) venv continuation act,
     Some venv = build_venv_returned a rr ->
     r rr = ContractAction act continuation ->
     exists pushed_venv, exists st, exists bal,
     (forall steps,
         program_result_approximate (program_sem venv (build_cenv a) steps)
                                    (ProgramToWorld act st bal pushed_venv))
     /\
    account_state_responds_to_world
      (update_account_state (account_state_pop_ongoing_call a) act st bal pushed_venv)
                                    continuation.

Definition respond_to_fail_correctly (f : contract_behavior)
           (a : account_state)
           (account_state_responds_to_world : account_state -> response_to_world -> Prop) :=
  forall venv continuation act,
     Some venv = build_venv_fail a ->
     f = ContractAction act continuation ->
     exists pushed_venv, exists st, exists bal,
     (forall steps,
         program_result_approximate (program_sem venv (build_cenv a) steps)
                                    (ProgramToWorld act st bal pushed_venv))
     /\
    account_state_responds_to_world
      (update_account_state (account_state_pop_ongoing_call a) act st bal pushed_venv)
                                    continuation.



CoInductive account_state_responds_to_world :
  account_state -> response_to_world -> Prop :=
| AccountStep :
    forall (a : account_state)
           (c : call_env -> contract_behavior)
           (r : return_result -> contract_behavior) f,
      respond_to_call_correctly c a account_state_responds_to_world ->
      respond_to_return_correctly r a account_state_responds_to_world ->
      respond_to_fail_correctly f a account_state_responds_to_world ->
    account_state_responds_to_world a (Respond c r f)
.

End ContractSem.


Module AbstractExamples (W : Word).
  Module C := (ContractSem W).
  Import C.
(**** Now we are able to specify contractsin terms of how they behave over
      many invocations, returns from calls and even re-entrance! ***)

(* Example 0: a contract that always fails *)
CoFixpoint always_fail :=
  ContractAction ContractFail
                 (Respond (fun _ => always_fail)
                          (fun _ => always_fail)
                          always_fail).

(* Example 1: a contract that always returns *)
CoFixpoint always_return x :=
  ContractAction (ContractReturn x)
         (Respond (fun (_ : call_env) => always_return x)
                  (fun (_ : return_result) => always_return x)
                  (always_return x)).

(* Example 2: a contract that calls something and then returns, but fails on re-entrance *)

Section FailOnReentrance.

Variable something_to_call : call_arguments.

CoFixpoint call_but_fail_on_reentrance (depth : nat) :=
  match depth with
  | O =>
    Respond
      (fun _ =>
         ContractAction (ContractCall something_to_call)
              (call_but_fail_on_reentrance (S O)))
      (fun _ => ContractAction ContractFail (call_but_fail_on_reentrance O))
      (ContractAction ContractFail (call_but_fail_on_reentrance O))
  | S O => (* now the callee responds or reenters *)
    Respond
      (fun _ => ContractAction ContractFail (call_but_fail_on_reentrance (S O)))
      (fun retval => ContractAction (ContractReturn retval) (call_but_fail_on_reentrance O))
      (ContractAction ContractFail (call_but_fail_on_reentrance O))
  | S (S n) =>
    Respond
      (fun _ => ContractAction ContractFail (call_but_fail_on_reentrance (S (S n))))
      (fun retval => ContractAction ContractFail (call_but_fail_on_reentrance (S n)))
      (ContractAction ContractFail (call_but_fail_on_reentrance (S n)))
  end.

End FailOnReentrance.

(******* Example 3.
  When re-entrance happens to the contract at example 2. ***)

Section Example3.

  Variable e : call_env.
  Variable a : call_arguments.

  Let example3_world :=
    WorldCall e :: WorldCall e :: nil.

  Let example2_contract :=
    call_but_fail_on_reentrance a 0.

  Let example3_history := specification_run example3_world example2_contract.

  Eval compute in example3_history.
(*
     = ActionByWorld (WorldCall e)
       :: ActionByContract (ContractCall a)
          :: ActionByWorld (WorldCall e)
             :: ActionByContract ContractFail :: nil
     : history

*)

End Example3.

Section Example0Continue.

  Definition spec_example_0 : response_to_world :=
    Respond
      (fun _ => always_fail)
      (fun _ => always_fail)
      always_fail.

  Variable example0_address : address.

  Definition example0_program :=
    PUSH1 (word_of_N 0) ::
    JUMP :: nil.

  Definition example0_account_state :=
    {| account_address := example0_address ;
       account_storage := empty_storage ;
       account_code := example0_program ;
       account_ongoing_calls := nil |}.


  Require Coq.Setoids.Setoid.

  Lemma always_fail_eq :
    forall act continuation,
      always_fail = ContractAction act continuation ->
      act = ContractFail /\
      continuation = Respond (fun _ => always_fail)
                             (fun _ => always_fail)
                             always_fail.
  Proof.
    intros ? ?.
    rewrite <- (contract_action_expander_eq always_fail) at 1.
    intro H.
    inversion H.
    auto.
  Qed.

  (** learned from https://github.com/uwplse/verdi/blob/master/PROOF_ENGINEERING.md **)
  Ltac always_fail_tac :=
    match goal with
      [ H: always_fail = ContractAction ?act ?continuation |- _ ] =>
      apply always_fail_eq in H; destruct H; subst
    end.

  Theorem example0_spec_impl_match :
    account_state_responds_to_world
      example0_account_state spec_example_0.
  Proof.
    cofix.
    apply AccountStep.
    {
      intros ? ? ? ?.
      always_fail_tac.
      eexists.
      eexists.
      eexists.
      split.
      {
        intros steps.
        case steps as [ | steps]; [ try left; auto | ].
        case steps as [ | steps]; [ try left; auto | ].
        simpl.
        unfold jump; simpl.
        unfold build_venv_called; simpl.
        unfold venv_update_stack; simpl.
        unfold venv_change_sfx; simpl.
        unfold venv_first_instruction; simpl.
        rewrite N_of_word_of_N.
        { simpl.
          right.
          auto. }
        reflexivity.
      }
      {
        assumption.
      }
    }
    {
      unfold respond_to_return_correctly.
      intros rr venv continuation act.
      unfold example0_account_state.
      unfold build_venv_returned.
      simpl.
      congruence.
    }
    {
      unfold respond_to_fail_correctly.
      intros venv continuation act.
      unfold example0_account_state.
      unfold build_venv_fail.
      simpl.
      congruence.
    }
  Qed.

End Example0Continue.


Section Example1Continue.
(*** prove that example 1 has an implementation  *)

  Definition return_result_nil : return_result := nil.
  Definition action_example_1 :=
    always_return return_result_nil.

  Definition spec_example_1 : response_to_world :=
    Respond
      (fun _ => action_example_1)
      (fun _ => action_example_1)
      action_example_1.

  Variable example1_address : address.

  Definition example1_program : list instruction :=
    PUSH1 word_zero ::
    PUSH1 word_zero ::
    RETURN ::
    nil.

  Definition example1_account_state :=
    {| account_address := example1_address ;
       account_storage := empty_storage ;
       account_code := example1_program ;
       account_ongoing_calls := nil |}.

  Lemma always_return_def :
    forall x,
      always_return x =
      ContractAction (ContractReturn x)
                     (Respond (fun (_ : call_env) => always_return x)
                              (fun (_ : return_result) => always_return x)
                              (always_return x)).
  Proof.
    intro x.
    rewrite <- (contract_action_expander_eq (always_return x)) at 1.
    auto.
  Qed.

  Lemma always_return_eq :
    forall act continuation x,
      always_return x = ContractAction act continuation ->
      act = ContractReturn x /\
      continuation = Respond (fun _ => always_return x)
                             (fun _ => always_return x)
                             (always_return x).
  Proof.
    intros ? ? ?.
    rewrite always_return_def at 1.
    intro H.
    inversion H; subst.
    auto.
  Qed.

  (** learned from https://github.com/uwplse/verdi/blob/master/PROOF_ENGINEERING.md **)
  Ltac always_return_tac :=
    match goal with
      [ H: always_return ?x = ContractAction ?act ?continuation |- _ ] =>
      apply always_return_eq in H; destruct H; subst
    end.



  Theorem example1_spec_impl_match :
    account_state_responds_to_world
      example1_account_state spec_example_1.
  Proof.
    cofix.
    apply AccountStep.
    { (* call case *)
      unfold respond_to_call_correctly.
      intros.
      eexists.
      eexists.
      eexists.
      split.
      {
        intro.
        case steps as [|steps]; [left; auto | ].
        case steps as [|steps]; [left; auto | ].
        case steps as [|steps]; [left; auto | ].
        unfold action_example_1 in H.
        always_return_tac.
        right.
        simpl.
        f_equal.
        f_equal.
        rewrite cut_memory_zero_nil.
        auto.
      }
      {
        unfold action_example_1 in H.
        always_return_tac.
        apply example1_spec_impl_match.
      }
    }
    {
      intros ? ? ? ?.
      simpl.
      congruence.
    }
    {
      intros ? ? ?.
      simpl.
      congruence.
    }
  Qed.

End Example1Continue.

End AbstractExamples.


Require Import Cyclic.Abstract.CyclicAxioms.
Require Import Coq.Lists.List.

  Require Import ZArith.

  Require BinNums.
  Require Cyclic.ZModulo.ZModulo.


Module ConcreteWord <: Word.

  Module WLEN <: Cyclic.ZModulo.ZModulo.PositiveNotOne.
    Import BinNums.

    Definition p : positive := xO (xO (xO (xO (xO (xO (xO (xO xH))))))).
    Lemma not_one : p <> 1%positive.
      unfold p.
      congruence.
    Qed.
  End WLEN.

  Module BLEN <: Cyclic.ZModulo.ZModulo.PositiveNotOne.
    Import BinNums.

    Definition p : positive := xO (xO (xO xH)).
    Lemma not_one : p <> 1%positive.
      unfold p.
      congruence.
    Qed.
  End BLEN.

  Module ALEN <: Cyclic.ZModulo.ZModulo.PositiveNotOne.
    Import BinNums.

    Definition p : positive := 160.
    Lemma not_one : p <> 1%positive.
      unfold p.
      congruence.
    Qed.
  End ALEN.

  Module W := Cyclic.ZModulo.ZModulo.ZModuloCyclicType WLEN.

  Module B := Cyclic.ZModulo.ZModulo.ZModuloCyclicType BLEN.

  Module A := Cyclic.ZModulo.ZModulo.ZModuloCyclicType ALEN.

  Definition word := W.t.

  Print W.ops.

  Definition word_eq (a : W.t) (b : W.t) :=
    match ZnZ.compare a b with Eq => true | _ => false end.

  Definition word_add (a b : W.t) :=
    ZnZ.add a b.

  Arguments word_add a b /.

  Definition word_sub := ZnZ.sub.

  Definition word_one := ZnZ.one.

  Definition word_zero := ZnZ.zero.

  Definition word_iszero := ZnZ.eq0.

  Definition word_smaller a b :=
    match ZnZ.compare a b with Lt => true | _ => false end.

  Definition word_of_N := Z.of_N.

  Definition N_of_word w := Z.to_N (ZnZ.to_Z w).

  Open Scope N_scope.
  Lemma N_of_word_of_N :
    forall (n : N), n < 10000 -> N_of_word (word_of_N n) = n.
  Proof.
    intros n nsmall.
    unfold N_of_word.
    unfold word_of_N.
    unfold ZnZ.to_Z.
    simpl.
    unfold ZModulo.to_Z.
    unfold ZModulo.wB.
    unfold WLEN.p.
    unfold DoubleType.base.
    rewrite Z.mod_small.
    { rewrite N2Z.id.
      reflexivity. }
    split.
    {
      apply N2Z.is_nonneg.
    }
    {
      eapply Z.lt_trans.
      { apply N2Z.inj_lt.
        eassumption. }
      vm_compute; auto.
    }
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
        rewrite ZModulo.spec_compare.
        rewrite Z.compare_refl.
        auto.
      Qed.

      Lemma eq_sym : forall x y : t, eq x y -> eq y x.
      Proof.
        intros ? ?.
        simpl.
        unfold word_eq. simpl.
        rewrite !ZModulo.spec_compare.
        rewrite <-Zcompare_antisym.
        simpl.
        set (r := (ZModulo.to_Z ALEN.p y ?= ZModulo.to_Z ALEN.p x)%Z).
        case r; unfold CompOpp; auto.
      Qed.

      Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
      Proof.
        intros ? ? ?.
        unfold eq.
        unfold word_eq.
        simpl.
        rewrite !ZModulo.spec_compare.
        set (xy := (ZModulo.to_Z ALEN.p x ?= ZModulo.to_Z ALEN.p y)%Z).
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
        rewrite !ZModulo.spec_compare.
        case_eq (ZModulo.to_Z ALEN.p x ?= ZModulo.to_Z ALEN.p y)%Z; try congruence.
        case_eq (ZModulo.to_Z ALEN.p y ?= ZModulo.to_Z ALEN.p z)%Z; try congruence.
        Search _ (_ ?= _)%Z.
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
        case_eq (ZModulo.compare ALEN.p x y); congruence.
      Qed.

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

        rewrite ZModulo.spec_compare in *.

        case_eq (ZModulo.to_Z ALEN.p y ?= ZModulo.to_Z ALEN.p x)%Z; try congruence.

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


  Definition raw_byte := B.t.
  Inductive byte' :=
  | ByteRaw : raw_byte -> byte'
  | ByteOfWord : word -> nat -> byte'
  .
  Definition byte := byte'.

  Definition address := A.t.

  Definition address_of_word (w : word) : address := w.

  Definition word_nth_byte (w : word) (n : nat) : byte :=
    ByteOfWord w n.

  Axiom word_of_bytes : list byte -> word.

  Open Scope list_scope.

  Import ListNotations.
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
  Admitted.

  Axiom event : Set.

  Axiom memory_state : Set.
  Axiom empty_memory : memory_state.
  Axiom cut_memory : word -> word -> memory_state -> list byte.
  Axiom cut_memory_zero_nil :
    forall start m, cut_memory start word_zero m = nil.

  Module ST := FMapList.Make WordOrdered.

  Definition storage := ST.t word.

  Eval compute in ST.key.

  Definition storage_load (m : storage) (k : word) : word :=
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
      is_true (word_iszero (storage_load empty_storage idx)).
  Proof.
    intro idx.
    compute.
    auto.
  Qed.

  Print Universes.

End ConcreteWord.


Module ExamplesOnConcreteWord.

  Module ConcreteSem := (ContractSem ConcreteWord).
  Include ConcreteSem.

  Definition example2_program : program :=
    PUSH1 (word_of_N 0) ::
    SLOAD ::
    DUP1 ::
    PUSH1 (word_of_N 2) ::
    JUMPI ::
    PUSH1 (word_of_N 1) ::
    ADD ::
    PUSH1 (word_of_N 0) ::
    SSTORE ::
    PUSH1 (word_of_N 0) ::
    (* TODO: change some of these arguments to value, address *)
    PUSH1 (word_of_N 0) ::
    PUSH1 (word_of_N 0) ::
    PUSH1 (word_of_N 0) ::
    PUSH1 (word_of_N 0) ::
    PUSH1 (word_of_N 0) ::
    CALL ::
    ISZERO ::
    PUSH1 (word_of_N 0) ::
    JUMPI ::
    PUSH1 (word_of_N 0) ::
    PUSH1 (word_of_N 0) ::
    SSTORE ::
    STOP ::
    nil.

  Variable example2_address : address.

  Definition example2_depth_n_state  (n : word) (st : account_state) :=
    (n = 0%Z /\
       st.(account_address) = example2_address /\
       is_true (ST.equal word_eq (st.(account_storage)) empty_storage) /\
       st.(account_code) = example2_program /\
       st.(account_ongoing_calls) = nil ) \/
     (n = 1%Z /\
      st.(account_code) = example2_program /\
      storage_load (account_storage st) 0%Z = 1%Z /\
      st.(account_address) = example2_address /\
      is_true (ST.equal word_eq (storage_store 0%Z 0%Z st.(account_storage)) empty_storage)  /\
      exists ve, (st.(account_ongoing_calls) = ve :: nil /\
             ve.(venv_prg_sfx) =
    ISZERO ::
    PUSH1 (word_of_N 0) ::
    JUMPI ::
    PUSH1 (word_of_N 0) ::
    PUSH1 (word_of_N 0) ::
    SSTORE ::
    STOP ::
    nil
                  /\
                  is_true (ST.equal word_eq (storage_store 0%Z 0%Z ve.(venv_storage)) empty_storage) /\
   is_true (ST.equal word_eq (venv_storage_at_call ve) empty_storage))
     )
  .


Definition something_to_call :=
     {|
     callarg_gaslimit := 0%Z;
     callarg_code := address_of_word 0%Z;
     callarg_recipient := address_of_word 0%Z;
     callarg_value := 0%Z;
     callarg_data := cut_memory 0%Z 0%Z empty_memory;
     callarg_output_begin := 0%Z;
     callarg_output_size := storage_load empty_storage 0%Z |}.

(* TODO: remove duplicate somehow *)
CoFixpoint call_but_fail_on_reentrance (depth : word) :=
  if word_eq word_zero depth then
    Respond
      (fun _ =>
         ContractAction (ContractCall something_to_call)
              (call_but_fail_on_reentrance word_one))
      (fun _ => ContractAction ContractFail (call_but_fail_on_reentrance word_zero))
      (ContractAction ContractFail (call_but_fail_on_reentrance word_zero))
  else if word_eq word_one depth then
    Respond
      (fun _ => ContractAction ContractFail (call_but_fail_on_reentrance word_one))
      (fun _ => ContractAction (ContractReturn nil) (call_but_fail_on_reentrance word_zero))
      (ContractAction ContractFail (call_but_fail_on_reentrance word_zero))
  else
    Respond
      (fun _ => ContractAction ContractFail (call_but_fail_on_reentrance depth))
      (fun retval => ContractAction ContractFail (call_but_fail_on_reentrance (word_sub depth word_one)))
      (ContractAction ContractFail (call_but_fail_on_reentrance (word_sub depth word_one))).

  Lemma call_but_fail_on_reentrace_0_eq :
    call_but_fail_on_reentrance 0%Z =
    Respond
      (fun _ =>
         ContractAction (ContractCall something_to_call)
              (call_but_fail_on_reentrance word_one))
      (fun _ => ContractAction ContractFail (call_but_fail_on_reentrance word_zero))
      (ContractAction ContractFail (call_but_fail_on_reentrance word_zero)).
  Proof.
    rewrite (response_expander_eq (call_but_fail_on_reentrance 0%Z)).
    auto.
  Qed.

  Lemma call_but_fail_on_reentrace_1_eq :
    call_but_fail_on_reentrance 1%Z =
    Respond
      (fun _ => ContractAction ContractFail (call_but_fail_on_reentrance word_one))
      (fun retval => ContractAction (ContractReturn nil) (call_but_fail_on_reentrance word_zero))
      (ContractAction ContractFail (call_but_fail_on_reentrance word_zero)).
  Proof.
    rewrite (response_expander_eq (call_but_fail_on_reentrance 1%Z)).
    auto.
  Qed.

  Definition example2_spec (depth: word) : response_to_world :=
    call_but_fail_on_reentrance depth.

  Lemma update_remove_eq :
    forall orig,
      is_true (ST.equal word_eq orig empty_storage) ->
      is_true
        (ST.equal word_eq
                  (storage_store 0%Z 0%Z (ST.add 0%Z 1%Z orig))
                  empty_storage).
  Proof.
    intros orig nst2.
    apply ST.equal_1.
    split.
    {
      intro k.
      Search ST.Raw.PX.In.
      unfold storage_store.
      simpl.
      split.
      { intro H.
        apply False_ind.
        case_eq (word_eq k 0%Z).
        { intro k0.
          apply ST.Raw.remove_1 in H; auto.
          { apply ST.Raw.add_sorted.
            apply ST.sorted. }
          apply ST.E.eq_sym.
          assumption.
        }
        {
          intro neq.
          unfold ST.Raw.PX.In in H.
          case H as [e H].
          Search _ ST.Raw.PX.MapsTo.
          apply ST.Raw.remove_3 in H.
          {
            Search _ ST.Raw.PX.MapsTo.
            apply ST.Raw.add_3 in H.
            {
              apply ST.equal_2 in nst2.
              case nst2 as [I _].
              generalize (I k).
              unfold ST.Raw.PX.In.
              intro I'.
              case I' as [I0 _].
              simpl in I0.
              Search _ ST.Raw.empty.
              case I0.
              {
                exists e.
                apply H.
              }
              {
                intros x J.
                eapply ST.Raw.empty_1.
                apply J.
              }
            }
            {
              intro K.
              apply ST.E.eq_sym in K.
              congruence.
            }
          }
          {
            Search Sorted.
            apply ST.Raw.add_sorted.
            apply ST.sorted.
          }
        }
      }
      {
        intro H.
        apply False_ind.
        case H.
        intros x Hx.
        apply (ST.Raw.empty_1 Hx).
      }
    }
    {
      intros k e e' H I.
      apply False_ind.
      generalize I.
      unfold empty_storage.
      generalize (ST.empty_1 I).
      auto.
    }
  Qed.

  Theorem example2_spec_impl_match :
    forall st n,
          example2_depth_n_state n st ->
          account_state_responds_to_world
            st (example2_spec n%Z).
  Proof.
    cofix.
    intros st n n_state.
    case n_state.
    {
      intro nst.
      destruct nst as [nst0 nst1].
      case nst1 as [nst1 nst2].
      case nst2 as [nst2 nst3].
      case nst3 as [nst3 nst4].
      subst.
      clear n_state.
      subst.
      unfold example2_spec.
      rewrite call_but_fail_on_reentrace_0_eq.
      apply AccountStep.
      {
        unfold respond_to_call_correctly.
        intros ce a con next.
        eexists.
        eexists.
        eexists.
        split.
        {
          intro s.
          simpl.
          rewrite nst3.
          repeat (case s as [| s]; [ solve [left; auto] | ]).
          assert (stl : forall idx, storage_load (account_storage st) idx = storage_load empty_storage idx).
          {
            intro idx.
            unfold storage_load.
            apply ST.equal_2 in nst2.
            unfold ST.Equivb in nst2.
            unfold ST.Raw.Equivb in nst2.
            simpl.
            case_eq (ST.find (elt:=word) idx (account_storage st)); auto.
            intros w H.
            apply ST.find_2 in H.
            Search _ ST.MapsTo.
            apply False_ind.
            Search _ ST.In.
            assert (ST.Raw.PX.In idx (ST.this (account_storage st))) as K.
            {
              unfold ST.Raw.PX.In.
              exists w.
              assumption.
            }
            case nst2 as [EE _].
            rewrite EE in K.
            unfold ST.Raw.PX.In in K.
            case K.
            intros content K'.
            apply (@ST.Raw.empty_1 word idx content).
            assumption.
          }
          simpl.
          rewrite !stl.
          unfold storage_load.
          unfold empty_storage.
          simpl.
          repeat (case s as [| s]; [ solve [left; auto] | ]).
          simpl.

          assert (H : word_smaller (callenv_balance ce (account_address st)) 0%Z = false).
          {
            unfold word_smaller.
            simpl.
            rewrite ZModulo.spec_compare.
            assert (0 <= ZModulo.to_Z ALEN.p (callenv_balance ce (account_address st)))%Z.
            {
              apply (ZModulo.spec_to_Z_1).
              unfold ALEN.p.
              congruence.
            }
            case_eq (ZModulo.to_Z ALEN.p (callenv_balance ce (account_address st))
      ?= ZModulo.to_Z ALEN.p 0)%Z; try congruence.
            Search (_ ?= _)%Z.
            rewrite Z.compare_nge_iff.
            intro H'.
            apply False_ind.
            apply H'.
            apply H.
          }
          rewrite H.
          right.
          f_equal.
          rewrite <- contract_action_expander_eq in next at 1.
          inversion next; subst.
          auto.
        }
        {
          simpl.
          rewrite <- contract_action_expander_eq in next at 1.
          inversion next; subst.
          simpl.
          unfold storage_load.
          unfold storage_store.
          unfold empty_storage.
          simpl.
          apply example2_spec_impl_match.
          unfold example2_depth_n_state.
          right.
          split; auto.
          simpl.
          split; auto.
          split.
          {
            unfold storage_load.
            erewrite ST.find_1.
            { eauto. }
            apply ST.add_1.
            auto.
          }
          split; auto.
          split.
          {
            apply update_remove_eq.
            assumption.
          }
          eexists; eauto.
          split.
          {
            rewrite nst4.
            eauto.
          }
          {
            split; auto.
            split; auto.
            simpl.


            apply update_remove_eq.
            assumption.

          }

       (* this place should be come harder and harder as I specify the
           * state at depth 1
           *)
        }
      }
      {
        unfold respond_to_return_correctly.
        intros ? ? ? ?.
        unfold build_venv_returned.
        rewrite nst4.
        congruence.
      }
      {
        intros ? ? ?.
        simpl.
        rewrite nst4.
        congruence.
      }
    }
    {
      intros H.
      destruct H as [n1 st_code].
      destruct st_code as [st_code st_load].
      destruct st_load as [st_load st_ongoing].
      subst.
      unfold example2_spec.
      rewrite call_but_fail_on_reentrace_1_eq.
      apply AccountStep.
      { (* call *)
        intros callenv act continuation H.
        inversion H; subst.
        clear H.
        eexists.
        eexists.
        eexists.
        unfold build_venv_called.
        rewrite st_code.
        split.
        {
          intro s.
          repeat (case s as [| s]; [ solve [left; auto] | ]).
          simpl.
          unfold jumpi.
          simpl.
          rewrite st_load.
          simpl.
          unfold jump.
          simpl.
          unfold venv_first_instruction.
          rewrite st_code.
          simpl.
          right.
          eauto.
        }
        {
          apply example2_spec_impl_match.
          unfold example2_depth_n_state.
          right.
          split; auto.
        }
      }
      { (* return *)
        unfold respond_to_return_correctly.
        intros rr venv cont act.
        elim st_ongoing.
        intros prev prevH.
        case prevH as [st_str prevH].
        case prevH as [prevH prevH'].
        case prevH' as [prevH' prevH''].
        case prevH'' as [prevH'' prevH'''].
        simpl.
        rewrite prevH'.
        intro H.
        inversion H; subst.
        clear H.
        intros act_cont_eq.
        eexists.
        eexists.
        eexists.
        split.
        {
          intro s.
          rewrite prevH''.
          repeat (case s as [| s]; [ solve [left; auto] | ]).
          simpl.
          right.
          f_equal.
          inversion act_cont_eq.
          auto.
        }
        {
          inversion act_cont_eq.
          apply example2_spec_impl_match.
          unfold example2_depth_n_state.
          left.
          repeat (split; auto); tauto.
        }
      }
      {
        unfold respond_to_fail_correctly.
        intros venv cont act.
        case st_ongoing as [st_addr st_ongoing].
        case st_ongoing as [st_storage st_ongoing].
        case st_ongoing as [ve veH].
        case veH as [st_ongoing ve_sfx].
        case ve_sfx as [ve_sfx ve_str].
        simpl.
        rewrite st_ongoing.
        intro venvH.
        inversion venvH; subst.
        clear venvH.
        intro act_cont_H.
        inversion act_cont_H; subst.
        clear act_cont_H.
        eexists.
        eexists.
        eexists.
        split.
        {
          intro s.
          rewrite ve_sfx.
          repeat (case s as [| s]; [ solve [left; auto] | ]).
          simpl.
          unfold compose.
          rewrite st_code.
          simpl.
          right.
          f_equal.
        }
        { (* update_account_state with contract_fail  *)
          simpl.
          apply example2_spec_impl_match.
          unfold example2_depth_n_state.
          left.
          repeat split; auto; tauto.
        }
      }
    }
  Qed.

End ExamplesOnConcreteWord.
