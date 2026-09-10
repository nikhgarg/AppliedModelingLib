import LOS02CombinatorialAuctions.EdgeListNativeEncoding
import AppliedModelingLib.Algorithms.Complexity.TuringMachine

/-!
# Native TM2 edge-list-to-incidence transducer

This is the concrete machine counterpart of the source's direct reduction in
the proof of Theorem 6.1.  It reads a unary vertex-count header and a stream
of unary ordered-edge endpoint pairs.  For each edge `(u, w)`, it emits the two
incidence records `(u, u, w)` and `(w, u, w)`.  A final stack transfer restores
the streamed output order.

The source's hardness consequence still additionally needs its variable-
threshold Karp and Håstad bridges.  This module establishes only the actual
finite machine required for the reduction's binary map; the fixed-threshold
semantic decision bridge is developed in `EdgeListNativeSemantics`.
-/

namespace LOS02CombinatorialAuctions
namespace EdgeListNativeMachine

open AppliedModelingLib.Complexity
open Turing
open Turing.TM2.Stmt

/-- Finite-control phases for the unary edge-list incidence transducer. -/
inductive Phase where
  | header
  | firstEndpoint
  | secondEndpoint
  | emitFirstU
  | emitSecondU
  | emitFirstW
  | emitSecondW
  | emitThirdU
  | emitThirdW
  | transfer
  deriving DecidableEq, Fintype

/-- A finite nine-stack TM2 machine for the source's streamed direct
edge-to-incidence construction.  Stack `0` is input, stack `1` accumulates the
reverse output, stacks `2`--`4` store three copies of `u`, stacks `5`--`7`
store three copies of `w`, and stack `8` is the final output. -/
def machine : FinTM2 where
  K := Fin 9
  k₀ := 0
  k₁ := 8
  Γ := fun _ => Bool
  Λ := Phase
  main := .header
  σ := Option Bool
  initialState := none
  m
    | .header =>
      pop 0 (fun _ bit => bit)
        (branch Option.isSome
          (branch (fun state => state.getD false)
            (push 1 (fun state => state.getD false) (goto fun _ => .header))
            (push 1 (fun state => state.getD false) (goto fun _ => .firstEndpoint)))
          halt)
    | .firstEndpoint =>
      pop 0 (fun _ bit => bit)
        (branch Option.isSome
          (branch (fun state => state.getD false)
            (push 2 (fun state => state.getD false)
              (push 3 (fun state => state.getD false)
                (push 4 (fun state => state.getD false) (goto fun _ => .firstEndpoint))))
            (goto fun _ => .secondEndpoint))
          (goto fun _ => .transfer))
    | .secondEndpoint =>
      pop 0 (fun _ bit => bit)
        (branch Option.isSome
          (branch (fun state => state.getD false)
            (push 5 (fun state => state.getD false)
              (push 6 (fun state => state.getD false)
                (push 7 (fun state => state.getD false) (goto fun _ => .secondEndpoint))))
            (goto fun _ => .emitFirstU))
          (goto fun _ => .transfer))
    | .emitFirstU =>
      pop 2 (fun _ bit => bit)
        (branch Option.isSome
          (push 1 (fun state => state.getD false) (goto fun _ => .emitFirstU))
          (push 1 (fun _ => false) (goto fun _ => .emitSecondU)))
    | .emitSecondU =>
      pop 3 (fun _ bit => bit)
        (branch Option.isSome
          (push 1 (fun state => state.getD false) (goto fun _ => .emitSecondU))
          (push 1 (fun _ => false) (goto fun _ => .emitFirstW)))
    | .emitFirstW =>
      pop 5 (fun _ bit => bit)
        (branch Option.isSome
          (push 1 (fun state => state.getD false) (goto fun _ => .emitFirstW))
          (push 1 (fun _ => false) (goto fun _ => .emitSecondW)))
    | .emitSecondW =>
      pop 6 (fun _ bit => bit)
        (branch Option.isSome
          (push 1 (fun state => state.getD false) (goto fun _ => .emitSecondW))
          (push 1 (fun _ => false) (goto fun _ => .emitThirdU)))
    | .emitThirdU =>
      pop 4 (fun _ bit => bit)
        (branch Option.isSome
          (push 1 (fun state => state.getD false) (goto fun _ => .emitThirdU))
          (push 1 (fun _ => false) (goto fun _ => .emitThirdW)))
    | .emitThirdW =>
      pop 7 (fun _ bit => bit)
        (branch Option.isSome
          (push 1 (fun state => state.getD false) (goto fun _ => .emitThirdW))
          (push 1 (fun _ => false) (goto fun _ => .firstEndpoint)))
    | .transfer =>
      pop 1 (fun _ bit => bit)
        (branch Option.isSome
          (push 8 (fun state => state.getD false) (goto fun _ => .transfer))
          halt)

/-- An explicit configuration for the nine-stack edge-list machine. -/
def config (label : Option Phase) (state : Option Bool)
    (input reversedOutput firstU secondU thirdU firstW secondW thirdW output : List Bool) :
    Turing.TM2.Cfg (fun _ : Fin 9 => Bool) Phase (Option Bool) where
  l := label
  var := state
  stk := Function.update
    (Function.update
      (Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update
                (Function.update
                  (Function.update (fun _ => []) 0 input) 1 reversedOutput) 2 firstU) 3 secondU)
                4 thirdU) 5 firstW) 6 secondW) 7 thirdW) 8 output

theorem initList_eq_config (input : List Bool) :
    Turing.initList machine input =
      config (some .header) none input [] [] [] [] [] [] [] [] := by
  simp [Turing.initList, config, machine]
  congr 2
  funext k
  fin_cases k <;> simp

theorem haltList_eq_config (output : List Bool) :
    Turing.haltList machine output =
      config none none [] [] [] [] [] [] [] [] output := by
  simp [Turing.haltList, config, machine]
  congr 2
  funext k
  fin_cases k <;> simp

theorem header_step_true (state : Option Bool)
    (input reversedOutput firstU secondU thirdU firstW secondW thirdW output : List Bool) :
    machine.step
      (config (some .header) state (true :: input) reversedOutput
        firstU secondU thirdU firstW secondW thirdW output) =
      some (config (some .header) (some true) input (true :: reversedOutput)
        firstU secondU thirdU firstW secondW thirdW output) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

theorem header_step_false (state : Option Bool)
    (input reversedOutput firstU secondU thirdU firstW secondW thirdW output : List Bool) :
    machine.step
      (config (some .header) state (false :: input) reversedOutput
        firstU secondU thirdU firstW secondW thirdW output) =
      some (config (some .firstEndpoint) (some false) input (false :: reversedOutput)
        firstU secondU thirdU firstW secondW thirdW output) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

theorem firstEndpoint_step_true (state : Option Bool)
    (input reversedOutput firstU secondU thirdU firstW secondW thirdW output : List Bool) :
    machine.step
      (config (some .firstEndpoint) state (true :: input) reversedOutput
        firstU secondU thirdU firstW secondW thirdW output) =
      some (config (some .firstEndpoint) (some true) input reversedOutput
        (true :: firstU) (true :: secondU) (true :: thirdU)
        firstW secondW thirdW output) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

theorem firstEndpoint_step_false (state : Option Bool)
    (input reversedOutput firstU secondU thirdU firstW secondW thirdW output : List Bool) :
    machine.step
      (config (some .firstEndpoint) state (false :: input) reversedOutput
        firstU secondU thirdU firstW secondW thirdW output) =
      some (config (some .secondEndpoint) (some false) input reversedOutput
        firstU secondU thirdU firstW secondW thirdW output) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

theorem firstEndpoint_step_nil (state : Option Bool)
    (reversedOutput firstU secondU thirdU firstW secondW thirdW output : List Bool) :
    machine.step
      (config (some .firstEndpoint) state [] reversedOutput
        firstU secondU thirdU firstW secondW thirdW output) =
      some (config (some .transfer) none [] reversedOutput
        firstU secondU thirdU firstW secondW thirdW output) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

theorem secondEndpoint_step_true (state : Option Bool)
    (input reversedOutput firstU secondU thirdU firstW secondW thirdW output : List Bool) :
    machine.step
      (config (some .secondEndpoint) state (true :: input) reversedOutput
        firstU secondU thirdU firstW secondW thirdW output) =
      some (config (some .secondEndpoint) (some true) input reversedOutput
        firstU secondU thirdU (true :: firstW) (true :: secondW) (true :: thirdW) output) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

theorem secondEndpoint_step_false (state : Option Bool)
    (input reversedOutput firstU secondU thirdU firstW secondW thirdW output : List Bool) :
    machine.step
      (config (some .secondEndpoint) state (false :: input) reversedOutput
        firstU secondU thirdU firstW secondW thirdW output) =
      some (config (some .emitFirstU) (some false) input reversedOutput
        firstU secondU thirdU firstW secondW thirdW output) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

theorem emitFirstU_step_cons (state : Option Bool) (bit : Bool)
    (input reversedOutput firstU secondU thirdU firstW secondW thirdW output : List Bool) :
    machine.step
      (config (some .emitFirstU) state input reversedOutput
        (bit :: firstU) secondU thirdU firstW secondW thirdW output) =
      some (config (some .emitFirstU) (some bit) input (bit :: reversedOutput)
        firstU secondU thirdU firstW secondW thirdW output) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

theorem emitFirstU_step_nil (state : Option Bool)
    (input reversedOutput secondU thirdU firstW secondW thirdW output : List Bool) :
    machine.step
      (config (some .emitFirstU) state input reversedOutput
        [] secondU thirdU firstW secondW thirdW output) =
      some (config (some .emitSecondU) none input (false :: reversedOutput)
        [] secondU thirdU firstW secondW thirdW output) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

theorem emitSecondU_step_cons (state : Option Bool) (bit : Bool)
    (input reversedOutput firstU secondU thirdU firstW secondW thirdW output : List Bool) :
    machine.step
      (config (some .emitSecondU) state input reversedOutput
        firstU (bit :: secondU) thirdU firstW secondW thirdW output) =
      some (config (some .emitSecondU) (some bit) input (bit :: reversedOutput)
        firstU secondU thirdU firstW secondW thirdW output) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

theorem emitSecondU_step_nil (state : Option Bool)
    (input reversedOutput firstU thirdU firstW secondW thirdW output : List Bool) :
    machine.step
      (config (some .emitSecondU) state input reversedOutput
        firstU [] thirdU firstW secondW thirdW output) =
      some (config (some .emitFirstW) none input (false :: reversedOutput)
        firstU [] thirdU firstW secondW thirdW output) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

theorem emitFirstW_step_cons (state : Option Bool) (bit : Bool)
    (input reversedOutput firstU secondU thirdU firstW secondW thirdW output : List Bool) :
    machine.step
      (config (some .emitFirstW) state input reversedOutput
        firstU secondU thirdU (bit :: firstW) secondW thirdW output) =
      some (config (some .emitFirstW) (some bit) input (bit :: reversedOutput)
        firstU secondU thirdU firstW secondW thirdW output) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

theorem emitFirstW_step_nil (state : Option Bool)
    (input reversedOutput firstU secondU thirdU secondW thirdW output : List Bool) :
    machine.step
      (config (some .emitFirstW) state input reversedOutput
        firstU secondU thirdU [] secondW thirdW output) =
      some (config (some .emitSecondW) none input (false :: reversedOutput)
        firstU secondU thirdU [] secondW thirdW output) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

theorem emitSecondW_step_cons (state : Option Bool) (bit : Bool)
    (input reversedOutput firstU secondU thirdU firstW secondW thirdW output : List Bool) :
    machine.step
      (config (some .emitSecondW) state input reversedOutput
        firstU secondU thirdU firstW (bit :: secondW) thirdW output) =
      some (config (some .emitSecondW) (some bit) input (bit :: reversedOutput)
        firstU secondU thirdU firstW secondW thirdW output) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

theorem emitSecondW_step_nil (state : Option Bool)
    (input reversedOutput firstU secondU thirdU firstW thirdW output : List Bool) :
    machine.step
      (config (some .emitSecondW) state input reversedOutput
        firstU secondU thirdU firstW [] thirdW output) =
      some (config (some .emitThirdU) none input (false :: reversedOutput)
        firstU secondU thirdU firstW [] thirdW output) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

theorem emitThirdU_step_cons (state : Option Bool) (bit : Bool)
    (input reversedOutput firstU secondU thirdU firstW secondW thirdW output : List Bool) :
    machine.step
      (config (some .emitThirdU) state input reversedOutput
        firstU secondU (bit :: thirdU) firstW secondW thirdW output) =
      some (config (some .emitThirdU) (some bit) input (bit :: reversedOutput)
        firstU secondU thirdU firstW secondW thirdW output) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

theorem emitThirdU_step_nil (state : Option Bool)
    (input reversedOutput firstU secondU firstW secondW thirdW output : List Bool) :
    machine.step
      (config (some .emitThirdU) state input reversedOutput
        firstU secondU [] firstW secondW thirdW output) =
      some (config (some .emitThirdW) none input (false :: reversedOutput)
        firstU secondU [] firstW secondW thirdW output) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

theorem emitThirdW_step_cons (state : Option Bool) (bit : Bool)
    (input reversedOutput firstU secondU thirdU firstW secondW thirdW output : List Bool) :
    machine.step
      (config (some .emitThirdW) state input reversedOutput
        firstU secondU thirdU firstW secondW (bit :: thirdW) output) =
      some (config (some .emitThirdW) (some bit) input (bit :: reversedOutput)
        firstU secondU thirdU firstW secondW thirdW output) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

theorem emitThirdW_step_nil (state : Option Bool)
    (input reversedOutput firstU secondU thirdU firstW secondW output : List Bool) :
    machine.step
      (config (some .emitThirdW) state input reversedOutput
        firstU secondU thirdU firstW secondW [] output) =
      some (config (some .firstEndpoint) none input (false :: reversedOutput)
        firstU secondU thirdU firstW secondW [] output) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

theorem transfer_step_cons (state : Option Bool) (bit : Bool)
    (reversedOutput output : List Bool) :
    machine.step
      (config (some .transfer) state [] (bit :: reversedOutput)
        [] [] [] [] [] [] output) =
      some (config (some .transfer) (some bit) [] reversedOutput
        [] [] [] [] [] [] (bit :: output)) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

theorem transfer_step_nil (state : Option Bool) (output : List Bool) :
    machine.step
      (config (some .transfer) state [] [] [] [] [] [] [] [] output) =
      some (config none none [] [] [] [] [] [] [] [] output) := by
  simp [machine, config, Turing.FinTM2.step, Turing.TM2.step]
  congr 2
  funext k
  fin_cases k <;> simp

/-- The one-step witness shared by the structured execution proofs below. -/
def oneStep {α : Type} (f : α → Option α) (a b : α) (h : f a = some b) :
    StateTransition.EvalsToInTime f a (some b) 1 :=
  BooleanListMap.oneStep f a b h

@[simp] theorem replicate_append_singleton (bit : Bool) (index : Nat) :
    List.replicate index bit ++ [bit] = List.replicate (index + 1) bit := by
  induction index with
  | zero => rfl
  | succ index ih =>
      simpa [List.replicate_succ, Nat.succ_eq_add_one] using congrArg (List.cons bit) ih

@[simp] theorem unaryIndexEncode_eq_replicate (index : Nat) :
    unaryIndexEncode index = List.replicate index true ++ [false] := by
  induction index with
  | zero => rfl
  | succ index ih =>
      simpa [unaryIndexEncode, List.replicate_succ] using congrArg (List.cons true) ih

@[simp] theorem unaryIndexEncode_reverse (index : Nat) :
    (unaryIndexEncode index).reverse = false :: List.replicate index true := by
  simp [unaryIndexEncode_eq_replicate]

/-- Execute the vertex-count header pass, placing the reverse header in the
output accumulator and leaving the encoded edge stream untouched. -/
def run_header (index : Nat)
    (input reversedOutput firstU secondU thirdU firstW secondW thirdW output : List Bool)
    (state : Option Bool) :
    StateTransition.EvalsToInTime machine.step
      (config (some .header) state (unaryIndexEncode index ++ input) reversedOutput
        firstU secondU thirdU firstW secondW thirdW output)
      (some (config (some .firstEndpoint) (some false) input
        ((unaryIndexEncode index).reverse ++ reversedOutput)
        firstU secondU thirdU firstW secondW thirdW output))
      (index + 1) := by
  induction index generalizing reversedOutput state with
  | zero =>
      simpa [unaryIndexEncode] using
        oneStep _ _ _ (header_step_false state input reversedOutput
          firstU secondU thirdU firstW secondW thirdW output)
  | succ index ih =>
      have hfirst := oneStep _ _ _ (header_step_true state
        (unaryIndexEncode index ++ input) reversedOutput
        firstU secondU thirdU firstW secondW thirdW output)
      have hrest := ih (true :: reversedOutput) (some true)
      have haccumulator :
          (unaryIndexEncode index).reverse ++ true :: reversedOutput =
            (unaryIndexEncode (index + 1)).reverse ++ reversedOutput := by
        simp only [unaryIndexEncode_reverse]
        apply congrArg (List.cons false)
        change List.replicate index true ++ ([true] ++ reversedOutput) =
          List.replicate (index + 1) true ++ reversedOutput
        rw [← List.append_assoc]
        exact congrArg (fun tails : List Bool => tails ++ reversedOutput)
          (replicate_append_singleton true index)
      rw [haccumulator] at hrest
      simpa [unaryIndexEncode, List.reverse_cons, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans _ 1 (index + 1) _ _ _ hfirst hrest

/-- Read one unary endpoint and copy its positive tokens to three working
stacks.  The delimiter is consumed without entering a working stack. -/
def run_firstEndpoint (index : Nat)
    (input reversedOutput firstU secondU thirdU firstW secondW thirdW output : List Bool)
    (state : Option Bool) :
    StateTransition.EvalsToInTime machine.step
      (config (some .firstEndpoint) state (unaryIndexEncode index ++ input) reversedOutput
        firstU secondU thirdU firstW secondW thirdW output)
      (some (config (some .secondEndpoint) (some false) input reversedOutput
        (List.replicate index true ++ firstU) (List.replicate index true ++ secondU)
        (List.replicate index true ++ thirdU) firstW secondW thirdW output))
      (index + 1) := by
  induction index generalizing firstU secondU thirdU state with
  | zero =>
      simpa [unaryIndexEncode] using
        oneStep _ _ _ (firstEndpoint_step_false state input reversedOutput
          firstU secondU thirdU firstW secondW thirdW output)
  | succ index ih =>
      have hfirst := oneStep _ _ _ (firstEndpoint_step_true state
        (unaryIndexEncode index ++ input) reversedOutput
        firstU secondU thirdU firstW secondW thirdW output)
      have hrest := ih (true :: firstU) (true :: secondU) (true :: thirdU) (some true)
      have hfirstU : List.replicate index true ++ true :: firstU =
          List.replicate (index + 1) true ++ firstU := by
        change List.replicate index true ++ ([true] ++ firstU) =
          List.replicate (index + 1) true ++ firstU
        rw [← List.append_assoc]
        exact congrArg (fun tails : List Bool => tails ++ firstU)
          (replicate_append_singleton true index)
      have hsecondU : List.replicate index true ++ true :: secondU =
          List.replicate (index + 1) true ++ secondU := by
        change List.replicate index true ++ ([true] ++ secondU) =
          List.replicate (index + 1) true ++ secondU
        rw [← List.append_assoc]
        exact congrArg (fun tails : List Bool => tails ++ secondU)
          (replicate_append_singleton true index)
      have hthirdU : List.replicate index true ++ true :: thirdU =
          List.replicate (index + 1) true ++ thirdU := by
        change List.replicate index true ++ ([true] ++ thirdU) =
          List.replicate (index + 1) true ++ thirdU
        rw [← List.append_assoc]
        exact congrArg (fun tails : List Bool => tails ++ thirdU)
          (replicate_append_singleton true index)
      simpa [unaryIndexEncode, List.replicate_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm, hfirstU, hsecondU, hthirdU] using
        StateTransition.EvalsToInTime.trans _ 1 (index + 1) _ _ _ hfirst hrest

/-- Read the second unary endpoint and copy its positive tokens to three
working stacks. -/
def run_secondEndpoint (index : Nat)
    (input reversedOutput firstU secondU thirdU firstW secondW thirdW output : List Bool)
    (state : Option Bool) :
    StateTransition.EvalsToInTime machine.step
      (config (some .secondEndpoint) state (unaryIndexEncode index ++ input) reversedOutput
        firstU secondU thirdU firstW secondW thirdW output)
      (some (config (some .emitFirstU) (some false) input reversedOutput
        firstU secondU thirdU (List.replicate index true ++ firstW)
        (List.replicate index true ++ secondW) (List.replicate index true ++ thirdW) output))
      (index + 1) := by
  induction index generalizing firstW secondW thirdW state with
  | zero =>
      simpa [unaryIndexEncode] using
        oneStep _ _ _ (secondEndpoint_step_false state input reversedOutput
          firstU secondU thirdU firstW secondW thirdW output)
  | succ index ih =>
      have hfirst := oneStep _ _ _ (secondEndpoint_step_true state
        (unaryIndexEncode index ++ input) reversedOutput
        firstU secondU thirdU firstW secondW thirdW output)
      have hrest := ih (true :: firstW) (true :: secondW) (true :: thirdW) (some true)
      have hfirstW : List.replicate index true ++ true :: firstW =
          List.replicate (index + 1) true ++ firstW := by
        change List.replicate index true ++ ([true] ++ firstW) =
          List.replicate (index + 1) true ++ firstW
        rw [← List.append_assoc]
        exact congrArg (fun tails : List Bool => tails ++ firstW)
          (replicate_append_singleton true index)
      have hsecondW : List.replicate index true ++ true :: secondW =
          List.replicate (index + 1) true ++ secondW := by
        change List.replicate index true ++ ([true] ++ secondW) =
          List.replicate (index + 1) true ++ secondW
        rw [← List.append_assoc]
        exact congrArg (fun tails : List Bool => tails ++ secondW)
          (replicate_append_singleton true index)
      have hthirdW : List.replicate index true ++ true :: thirdW =
          List.replicate (index + 1) true ++ thirdW := by
        change List.replicate index true ++ ([true] ++ thirdW) =
          List.replicate (index + 1) true ++ thirdW
        rw [← List.append_assoc]
        exact congrArg (fun tails : List Bool => tails ++ thirdW)
          (replicate_append_singleton true index)
      simpa [unaryIndexEncode, List.replicate_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm, hfirstW, hsecondW, hthirdW] using
        StateTransition.EvalsToInTime.trans _ 1 (index + 1) _ _ _ hfirst hrest

/-- Emit the first stored copy of the first endpoint. -/
def run_emitFirstU (tokens : List Bool)
    (input reversedOutput secondU thirdU firstW secondW thirdW output : List Bool)
    (state : Option Bool) :
    StateTransition.EvalsToInTime machine.step
      (config (some .emitFirstU) state input reversedOutput
        tokens secondU thirdU firstW secondW thirdW output)
      (some (config (some .emitSecondU) none input
        (false :: tokens.reverse ++ reversedOutput)
        [] secondU thirdU firstW secondW thirdW output))
      (tokens.length + 1) := by
  induction tokens generalizing reversedOutput state with
  | nil =>
      simpa using oneStep _ _ _ (emitFirstU_step_nil state input reversedOutput
        secondU thirdU firstW secondW thirdW output)
  | cons bit tokens ih =>
      have hfirst := oneStep _ _ _ (emitFirstU_step_cons state bit input reversedOutput
        tokens secondU thirdU firstW secondW thirdW output)
      have hrest := ih (bit :: reversedOutput) (some bit)
      simpa [List.reverse_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        List.append_assoc] using
        StateTransition.EvalsToInTime.trans _ 1 (tokens.length + 1) _ _ _ hfirst hrest

/-- Emit the second stored copy of the first endpoint. -/
def run_emitSecondU (tokens : List Bool)
    (input reversedOutput firstU thirdU firstW secondW thirdW output : List Bool)
    (state : Option Bool) :
    StateTransition.EvalsToInTime machine.step
      (config (some .emitSecondU) state input reversedOutput
        firstU tokens thirdU firstW secondW thirdW output)
      (some (config (some .emitFirstW) none input
        (false :: tokens.reverse ++ reversedOutput)
        firstU [] thirdU firstW secondW thirdW output))
      (tokens.length + 1) := by
  induction tokens generalizing reversedOutput state with
  | nil =>
      simpa using oneStep _ _ _ (emitSecondU_step_nil state input reversedOutput
        firstU thirdU firstW secondW thirdW output)
  | cons bit tokens ih =>
      have hfirst := oneStep _ _ _ (emitSecondU_step_cons state bit input reversedOutput
        firstU tokens thirdU firstW secondW thirdW output)
      have hrest := ih (bit :: reversedOutput) (some bit)
      simpa [List.reverse_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        List.append_assoc] using
        StateTransition.EvalsToInTime.trans _ 1 (tokens.length + 1) _ _ _ hfirst hrest

/-- Emit the first stored copy of the second endpoint. -/
def run_emitFirstW (tokens : List Bool)
    (input reversedOutput firstU secondU thirdU secondW thirdW output : List Bool)
    (state : Option Bool) :
    StateTransition.EvalsToInTime machine.step
      (config (some .emitFirstW) state input reversedOutput
        firstU secondU thirdU tokens secondW thirdW output)
      (some (config (some .emitSecondW) none input
        (false :: tokens.reverse ++ reversedOutput)
        firstU secondU thirdU [] secondW thirdW output))
      (tokens.length + 1) := by
  induction tokens generalizing reversedOutput state with
  | nil =>
      simpa using oneStep _ _ _ (emitFirstW_step_nil state input reversedOutput
        firstU secondU thirdU secondW thirdW output)
  | cons bit tokens ih =>
      have hfirst := oneStep _ _ _ (emitFirstW_step_cons state bit input reversedOutput
        firstU secondU thirdU tokens secondW thirdW output)
      have hrest := ih (bit :: reversedOutput) (some bit)
      simpa [List.reverse_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        List.append_assoc] using
        StateTransition.EvalsToInTime.trans _ 1 (tokens.length + 1) _ _ _ hfirst hrest

/-- Emit the second stored copy of the second endpoint. -/
def run_emitSecondW (tokens : List Bool)
    (input reversedOutput firstU secondU thirdU firstW thirdW output : List Bool)
    (state : Option Bool) :
    StateTransition.EvalsToInTime machine.step
      (config (some .emitSecondW) state input reversedOutput
        firstU secondU thirdU firstW tokens thirdW output)
      (some (config (some .emitThirdU) none input
        (false :: tokens.reverse ++ reversedOutput)
        firstU secondU thirdU firstW [] thirdW output))
      (tokens.length + 1) := by
  induction tokens generalizing reversedOutput state with
  | nil =>
      simpa using oneStep _ _ _ (emitSecondW_step_nil state input reversedOutput
        firstU secondU thirdU firstW thirdW output)
  | cons bit tokens ih =>
      have hfirst := oneStep _ _ _ (emitSecondW_step_cons state bit input reversedOutput
        firstU secondU thirdU firstW tokens thirdW output)
      have hrest := ih (bit :: reversedOutput) (some bit)
      simpa [List.reverse_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        List.append_assoc] using
        StateTransition.EvalsToInTime.trans _ 1 (tokens.length + 1) _ _ _ hfirst hrest

/-- Emit the third stored copy of the first endpoint. -/
def run_emitThirdU (tokens : List Bool)
    (input reversedOutput firstU secondU firstW secondW thirdW output : List Bool)
    (state : Option Bool) :
    StateTransition.EvalsToInTime machine.step
      (config (some .emitThirdU) state input reversedOutput
        firstU secondU tokens firstW secondW thirdW output)
      (some (config (some .emitThirdW) none input
        (false :: tokens.reverse ++ reversedOutput)
        firstU secondU [] firstW secondW thirdW output))
      (tokens.length + 1) := by
  induction tokens generalizing reversedOutput state with
  | nil =>
      simpa using oneStep _ _ _ (emitThirdU_step_nil state input reversedOutput
        firstU secondU firstW secondW thirdW output)
  | cons bit tokens ih =>
      have hfirst := oneStep _ _ _ (emitThirdU_step_cons state bit input reversedOutput
        firstU secondU tokens firstW secondW thirdW output)
      have hrest := ih (bit :: reversedOutput) (some bit)
      simpa [List.reverse_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        List.append_assoc] using
        StateTransition.EvalsToInTime.trans _ 1 (tokens.length + 1) _ _ _ hfirst hrest

/-- Emit the third stored copy of the second endpoint and return to edge
parsing. -/
def run_emitThirdW (tokens : List Bool)
    (input reversedOutput firstU secondU thirdU firstW secondW output : List Bool)
    (state : Option Bool) :
    StateTransition.EvalsToInTime machine.step
      (config (some .emitThirdW) state input reversedOutput
        firstU secondU thirdU firstW secondW tokens output)
      (some (config (some .firstEndpoint) none input
        (false :: tokens.reverse ++ reversedOutput)
        firstU secondU thirdU firstW secondW [] output))
      (tokens.length + 1) := by
  induction tokens generalizing reversedOutput state with
  | nil =>
      simpa using oneStep _ _ _ (emitThirdW_step_nil state input reversedOutput
        firstU secondU thirdU firstW secondW output)
  | cons bit tokens ih =>
      have hfirst := oneStep _ _ _ (emitThirdW_step_cons state bit input reversedOutput
        firstU secondU thirdU firstW secondW tokens output)
      have hrest := ih (bit :: reversedOutput) (some bit)
      simpa [List.reverse_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        List.append_assoc] using
        StateTransition.EvalsToInTime.trans _ 1 (tokens.length + 1) _ _ _ hfirst hrest

/-- Execute the six emitted unary words associated with one ordered edge.
The parser retains three copies of each endpoint, and the six emitter phases
write the reversed words for `(u,u,w,w,u,w)` onto the output accumulator. -/
def run_edge (u w : Nat)
    (input reversedOutput output : List Bool) (state : Option Bool) :
    StateTransition.EvalsToInTime machine.step
      (config (some .firstEndpoint) state
        (unaryIndexEncode u ++ unaryIndexEncode w ++ input) reversedOutput
        [] [] [] [] [] [] output)
      (some (config (some .firstEndpoint) none input
        ((unaryNatListEncode [u, u, w, w, u, w]).reverse ++ reversedOutput)
        [] [] [] [] [] [] output))
      (4 * u + 4 * w + 8) := by
  have hfirstEndpoint := run_firstEndpoint u (unaryIndexEncode w ++ input)
    reversedOutput [] [] [] [] [] [] output state
  have hsecondEndpoint := run_secondEndpoint w input reversedOutput
    (List.replicate u true) (List.replicate u true) (List.replicate u true)
    [] [] [] output (some false)
  have hemitFirstU := run_emitFirstU (List.replicate u true) input reversedOutput
    (List.replicate u true) (List.replicate u true)
    (List.replicate w true) (List.replicate w true) (List.replicate w true)
    output (some false)
  have hemitSecondU := run_emitSecondU (List.replicate u true) input
    (false :: (List.replicate u true).reverse ++ reversedOutput) []
    (List.replicate u true) (List.replicate w true) (List.replicate w true)
    (List.replicate w true) output none
  have hemitFirstW := run_emitFirstW (List.replicate w true) input
    (false :: (List.replicate u true).reverse ++
      (false :: (List.replicate u true).reverse ++ reversedOutput))
    [] [] (List.replicate u true)
    (List.replicate w true) (List.replicate w true) output none
  have hemitSecondW := run_emitSecondW (List.replicate w true) input
    (false :: (List.replicate w true).reverse ++
      (false :: (List.replicate u true).reverse ++
        (false :: (List.replicate u true).reverse ++ reversedOutput)))
    [] [] (List.replicate u true) [] (List.replicate w true) output none
  have hemitThirdU := run_emitThirdU (List.replicate u true) input
    (false :: (List.replicate w true).reverse ++
      (false :: (List.replicate w true).reverse ++
        (false :: (List.replicate u true).reverse ++
          (false :: (List.replicate u true).reverse ++ reversedOutput))))
    [] [] [] [] (List.replicate w true) output none
  have hemitThirdW := run_emitThirdW (List.replicate w true) input
    (false :: (List.replicate u true).reverse ++
      (false :: (List.replicate w true).reverse ++
        (false :: (List.replicate w true).reverse ++
          (false :: (List.replicate u true).reverse ++
            (false :: (List.replicate u true).reverse ++ reversedOutput)))))
    [] [] [] [] [] output none
  have hfirstEndpoint' : StateTransition.EvalsToInTime machine.step
      (config (some .firstEndpoint) state
        (unaryIndexEncode u ++ unaryIndexEncode w ++ input) reversedOutput
        [] [] [] [] [] [] output)
      (some (config (some .secondEndpoint) (some false)
        (unaryIndexEncode w ++ input) reversedOutput
        (List.replicate u true) (List.replicate u true) (List.replicate u true)
        [] [] [] output))
      (u + 1) := by
    simpa using hfirstEndpoint
  have hsecondEndpoint' : StateTransition.EvalsToInTime machine.step
      (config (some .secondEndpoint) (some false)
        (unaryIndexEncode w ++ input) reversedOutput
        (List.replicate u true) (List.replicate u true) (List.replicate u true)
        [] [] [] output)
      (some (config (some .emitFirstU) (some false) input reversedOutput
        (List.replicate u true) (List.replicate u true) (List.replicate u true)
        (List.replicate w true) (List.replicate w true) (List.replicate w true) output))
      (w + 1) := by
    simpa using hsecondEndpoint
  have hfirstSecond := StateTransition.EvalsToInTime.trans _ _ _ _ _ _
    hfirstEndpoint' hsecondEndpoint'
  have hfirstSecondFirstU := StateTransition.EvalsToInTime.trans _ _ _ _ _ _
    hfirstSecond hemitFirstU
  have hfirstSecondFirstUSecondU := StateTransition.EvalsToInTime.trans _ _ _ _ _ _
    hfirstSecondFirstU hemitSecondU
  have hfirstSecondFirstUSecondUFirstW := StateTransition.EvalsToInTime.trans _ _ _ _ _ _
    hfirstSecondFirstUSecondU hemitFirstW
  have hfirstSecondFirstUSecondUFirstWSecondW :=
    StateTransition.EvalsToInTime.trans _ _ _ _ _ _
      hfirstSecondFirstUSecondUFirstW hemitSecondW
  have hfirstSecondFirstUSecondUFirstWSecondWThirdU :=
    StateTransition.EvalsToInTime.trans _ _ _ _ _ _
      hfirstSecondFirstUSecondUFirstWSecondW hemitThirdU
  have h := StateTransition.EvalsToInTime.trans _ _ _ _ _ _
    hfirstSecondFirstUSecondUFirstWSecondWThirdU hemitThirdW
  convert h using 1 <;>
    simp [unaryNatListEncode,
      List.length_replicate, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      Nat.mul_comm]
  all_goals omega

/-- The exact transition work for parsing and emitting a streamed edge list,
excluding the vertex-count header and final output transfer. -/
def edgeStreamWork {n : Nat} (edges : List (Fin n × Fin n)) : Nat :=
  (edges.map fun edge => 4 * edge.1.val + 4 * edge.2.val + 8).sum

/-- Execute an entire streamed edge list.  For an empty list this is the
zero-step identity configuration; otherwise each edge leaves the parser in
its neutral state. -/
def run_edges {n : Nat} (edges : List (Fin n × Fin n))
    (input reversedOutput output : List Bool) (state : Option Bool) :
    StateTransition.EvalsToInTime machine.step
      (config (some .firstEndpoint) state
        (unaryNatListEncode (unaryEdgeListWords edges) ++ input) reversedOutput
        [] [] [] [] [] [] output)
      (some (config (some .firstEndpoint)
        (if edges = [] then state else none) input
        ((unaryNatListEncode (unaryEdgeIncidenceOutputWords edges)).reverse ++ reversedOutput)
        [] [] [] [] [] [] output))
      (edgeStreamWork edges) := by
  induction edges generalizing input reversedOutput output state with
  | nil =>
      simpa [unaryEdgeListWords, unaryEdgeIncidenceOutputWords, edgeStreamWork] using
        StateTransition.EvalsToInTime.refl machine.step
          (config (some .firstEndpoint) state input reversedOutput
            [] [] [] [] [] [] output)
  | cons edge edges ih =>
      have hfirst := run_edge edge.1.val edge.2.val
        (unaryNatListEncode (unaryEdgeListWords edges) ++ input)
        reversedOutput output state
      have hrest := ih input
        ((unaryNatListEncode [edge.1.val, edge.1.val, edge.2.val, edge.2.val,
          edge.1.val, edge.2.val]).reverse ++ reversedOutput)
        output none
      have h := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ hfirst hrest
      convert h using 1 <;>
        simp [unaryNatListEncode, unaryEdgeListWords, unaryEdgeIncidenceOutputWords,
          edgeStreamWork, List.reverse_append, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm]

/-- The per-edge parser/emitter work is four times the length of its input
endpoint stream. -/
theorem edgeStreamWork_eq_four_mul_input_length {n : Nat}
    (edges : List (Fin n × Fin n)) :
    edgeStreamWork edges =
      4 * (unaryNatListEncode (unaryEdgeListWords edges)).length := by
  induction edges with
  | nil => rfl
  | cons edge edges ih =>
      simp only [edgeStreamWork, List.map_cons, List.sum_cons,
        unaryEdgeListWords, List.flatMap_cons, List.cons_append,
        unaryNatListEncode_cons, List.nil_append]
      change 4 * edge.1.val + 4 * edge.2.val + 8 +
          (edges.map fun edge => 4 * edge.1.val + 4 * edge.2.val + 8).sum =
        4 * (unaryIndexEncode edge.1.val ++
          (unaryIndexEncode edge.2.val ++
            unaryNatListEncode (unaryEdgeListWords edges))).length
      have ih' := ih
      simp only [edgeStreamWork] at ih'
      simp [List.length_append, ih']
      omega

/-- The incidence stream has exactly three times the endpoint-stream length:
each source endpoint is represented in three emitted incidence coordinates. -/
theorem incidence_output_length_eq_three_mul_input_length {n : Nat}
    (edges : List (Fin n × Fin n)) :
    (unaryNatListEncode (unaryEdgeIncidenceOutputWords edges)).length =
      3 * (unaryNatListEncode (unaryEdgeListWords edges)).length := by
  induction edges with
  | nil => rfl
  | cons edge edges ih =>
      simp only [unaryEdgeIncidenceOutputWords, List.flatMap_cons,
        List.cons_append, unaryNatListEncode_cons, unaryEdgeListWords,
        List.nil_append]
      change (unaryIndexEncode edge.1.val ++
        (unaryIndexEncode edge.1.val ++
          (unaryIndexEncode edge.2.val ++
            (unaryIndexEncode edge.2.val ++
              (unaryIndexEncode edge.1.val ++
                (unaryIndexEncode edge.2.val ++
                  unaryNatListEncode (unaryEdgeIncidenceOutputWords edges))))))).length =
        3 * (unaryIndexEncode edge.1.val ++
          (unaryIndexEncode edge.2.val ++
            unaryNatListEncode (unaryEdgeListWords edges))).length
      simp [List.length_append, ih]
      omega

/-- Transfer the accumulated reverse stream to the designated output stack. -/
def run_transfer (reversedOutput output : List Bool) (state : Option Bool) :
    StateTransition.EvalsToInTime machine.step
      (config (some .transfer) state [] reversedOutput [] [] [] [] [] [] output)
      (some (config none none [] [] [] [] [] [] [] [] (reversedOutput.reverse ++ output)))
      (reversedOutput.length + 1) := by
  induction reversedOutput generalizing output state with
  | nil =>
      simpa using oneStep _ _ _ (transfer_step_nil state output)
  | cons bit reversedOutput ih =>
      have hfirst := oneStep _ _ _ (transfer_step_cons state bit reversedOutput output)
      have hrest := ih (bit :: output) (some bit)
      simpa [List.reverse_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        List.append_assoc] using
        StateTransition.EvalsToInTime.trans _ 1 (reversedOutput.length + 1) _ _ _ hfirst hrest

/-- The complete checked run for a unary edge-list graph: copy the vertex
header, stream every edge into its two incidence records, then reverse the
accumulator onto the output stack. -/
def run (n : Nat) (edges : List (Fin n × Fin n)) :
    StateTransition.EvalsToInTime machine.step
      (config (some .header) none
        (unaryIndexEncode n ++ unaryNatListEncode (unaryEdgeListWords edges))
        [] [] [] [] [] [] [] [])
      (some (config none none [] [] [] [] [] [] [] []
        (unaryIndexEncode n ++
          unaryNatListEncode (unaryEdgeIncidenceOutputWords edges))))
      ((unaryIndexEncode n).length + edgeStreamWork edges +
        ((unaryIndexEncode n ++
          unaryNatListEncode (unaryEdgeIncidenceOutputWords edges)).length + 2)) := by
  have hheader := run_header n (unaryNatListEncode (unaryEdgeListWords edges))
    [] [] [] [] [] [] [] [] none
  have hedges := run_edges edges [] (unaryIndexEncode n).reverse [] (some false)
  have hleave := oneStep _ _ _ (firstEndpoint_step_nil
    (if edges = [] then some false else none)
    ((unaryNatListEncode (unaryEdgeIncidenceOutputWords edges)).reverse ++
      (unaryIndexEncode n).reverse)
    [] [] [] [] [] [] [])
  have htransfer := run_transfer
    ((unaryNatListEncode (unaryEdgeIncidenceOutputWords edges)).reverse ++
      (unaryIndexEncode n).reverse)
    [] none
  have hheader' : StateTransition.EvalsToInTime machine.step
      (config (some .header) none
        (unaryIndexEncode n ++ unaryNatListEncode (unaryEdgeListWords edges))
        [] [] [] [] [] [] [] [])
      (some (config (some .firstEndpoint) (some false)
        (unaryNatListEncode (unaryEdgeListWords edges))
        (unaryIndexEncode n).reverse [] [] [] [] [] [] []))
      (n + 1) := by
    simpa using hheader
  have hedges' : StateTransition.EvalsToInTime machine.step
      (config (some .firstEndpoint) (some false)
        (unaryNatListEncode (unaryEdgeListWords edges))
        (unaryIndexEncode n).reverse [] [] [] [] [] [] [])
      (some (config (some .firstEndpoint)
        (if edges = [] then some false else none) []
        ((unaryNatListEncode (unaryEdgeIncidenceOutputWords edges)).reverse ++
          (unaryIndexEncode n).reverse)
        [] [] [] [] [] [] []))
      (edgeStreamWork edges) := by
    simpa using hedges
  have hheaderEdges := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ hheader' hedges'
  have hheaderEdgesLeave := StateTransition.EvalsToInTime.trans _ _ _ _ _ _
    hheaderEdges hleave
  have h := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ hheaderEdgesLeave htransfer
  convert h using 1 <;>
    simp [List.reverse_append, List.length_append, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]
  all_goals omega

/-- The same transducer streams an edge list under any terminated-unary
header.  It never inspects the header's numeric meaning after copying it, so
this supports source encodings that pack auxiliary decision data with the
vertex count while retaining the exact edge-to-incidence payload map. -/
def run_with_header (header : Nat) {n : Nat} (edges : List (Fin n × Fin n)) :
    StateTransition.EvalsToInTime machine.step
      (config (some .header) none
        (unaryIndexEncode header ++ unaryNatListEncode (unaryEdgeListWords edges))
        [] [] [] [] [] [] [] [])
      (some (config none none [] [] [] [] [] [] [] []
        (unaryIndexEncode header ++
          unaryNatListEncode (unaryEdgeIncidenceOutputWords edges))))
      ((unaryIndexEncode header).length + edgeStreamWork edges +
        ((unaryIndexEncode header ++
          unaryNatListEncode (unaryEdgeIncidenceOutputWords edges)).length + 2)) := by
  have hheader := run_header header (unaryNatListEncode (unaryEdgeListWords edges))
    [] [] [] [] [] [] [] [] none
  have hedges := run_edges edges [] (unaryIndexEncode header).reverse [] (some false)
  have hleave := oneStep _ _ _ (firstEndpoint_step_nil
    (if edges = [] then some false else none)
    ((unaryNatListEncode (unaryEdgeIncidenceOutputWords edges)).reverse ++
      (unaryIndexEncode header).reverse)
    [] [] [] [] [] [] [])
  have htransfer := run_transfer
    ((unaryNatListEncode (unaryEdgeIncidenceOutputWords edges)).reverse ++
      (unaryIndexEncode header).reverse)
    [] none
  have hheader' : StateTransition.EvalsToInTime machine.step
      (config (some .header) none
        (unaryIndexEncode header ++ unaryNatListEncode (unaryEdgeListWords edges))
        [] [] [] [] [] [] [] [])
      (some (config (some .firstEndpoint) (some false)
        (unaryNatListEncode (unaryEdgeListWords edges))
        (unaryIndexEncode header).reverse [] [] [] [] [] [] []))
      (header + 1) := by
    simpa using hheader
  have hedges' : StateTransition.EvalsToInTime machine.step
      (config (some .firstEndpoint) (some false)
        (unaryNatListEncode (unaryEdgeListWords edges))
        (unaryIndexEncode header).reverse [] [] [] [] [] [] [])
      (some (config (some .firstEndpoint)
        (if edges = [] then some false else none) []
        ((unaryNatListEncode (unaryEdgeIncidenceOutputWords edges)).reverse ++
          (unaryIndexEncode header).reverse)
        [] [] [] [] [] [] []))
      (edgeStreamWork edges) := by
    simpa using hedges
  have hheaderEdges := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ hheader' hedges'
  have hheaderEdgesLeave := StateTransition.EvalsToInTime.trans _ _ _ _ _ _
    hheaderEdges hleave
  have h := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ hheaderEdgesLeave htransfer
  convert h using 1 <;>
    simp [List.reverse_append, List.length_append, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]
  all_goals omega

/-- The opaque-header execution remains linearly bounded in the complete
header-and-edge stream length. -/
def outputsInTime_with_header (header : Nat) {n : Nat}
    (edges : List (Fin n × Fin n)) :
    Turing.TM2OutputsInTime machine
      (unaryIndexEncode header ++ unaryNatListEncode (unaryEdgeListWords edges))
      (some (unaryIndexEncode header ++
        unaryNatListEncode (unaryEdgeIncidenceOutputWords edges)))
      (7 * (unaryIndexEncode header ++
        unaryNatListEncode (unaryEdgeListWords edges)).length) := by
  rw [Turing.TM2OutputsInTime, initList_eq_config, Option.map_some,
    haltList_eq_config]
  have h := run_with_header header edges
  refine ⟨h.toEvalsTo, le_trans h.steps_le_m ?_⟩
  rw [edgeStreamWork_eq_four_mul_input_length, List.length_append,
    incidence_output_length_eq_three_mul_input_length]
  simp only [List.length_append, unaryIndexEncode_length]
  omega

/-- The complete native run is linearly bounded by the length of the selected
self-delimiting input encoding. -/
def outputsInTime (input : UnaryEdgeListGraphInput) :
    Turing.TM2OutputsInTime machine
      (unaryEdgeListGraphInputCode input)
      (some (unaryEdgeListAuctionInputCode (unaryEdgeListGraphToAuction input)))
      (7 * (unaryEdgeListGraphInputCode input).length) := by
  rcases input with ⟨n, edges⟩
  change Turing.TM2OutputsInTime machine
    (unaryIndexEncode n ++ unaryNatListEncode (unaryEdgeListWords edges))
    (some (unaryEdgeListAuctionInputCode
      (unaryEdgeListGraphToAuction ⟨n, edges⟩)))
    (7 * (unaryIndexEncode n ++ unaryNatListEncode (unaryEdgeListWords edges)).length)
  rw [unaryEdgeListAuctionInputCode_map]
  rw [Turing.TM2OutputsInTime, initList_eq_config, Option.map_some,
    haltList_eq_config]
  have h := run n edges
  refine ⟨h.toEvalsTo, le_trans h.steps_le_m ?_⟩
  rw [edgeStreamWork_eq_four_mul_input_length, List.length_append,
    incidence_output_length_eq_three_mul_input_length]
  simp only [List.length_append, unaryIndexEncode_length]
  omega

/-- A native polynomial-time witness for the source-nearer streamed
edge-list-to-incidence transformation.  This establishes the executable
binary map only; the graph/auction decision-equivalence bridge remains a
separate theorem obligation. -/
noncomputable def computableInPolyTime :
    Turing.TM2ComputableInPolyTime
      unaryEdgeListGraphInputEncoding.encode
      unaryEdgeListAuctionInputEncoding.encode
      unaryEdgeListGraphToAuction where
  tm := machine
  inputAlphabet := BooleanListMap.boolIdentityEquiv
  outputAlphabet := BooleanListMap.boolIdentityEquiv
  time := 7 * Polynomial.X
  outputsFun input := by
    change Turing.TM2OutputsInTime machine
      (List.map (fun bit => bit) (unaryEdgeListGraphInputCode input))
      (some (List.map (fun bit => bit)
        (unaryEdgeListAuctionInputCode (unaryEdgeListGraphToAuction input))) ) _
    simpa [unaryEdgeListGraphInputEncoding, unaryEdgeListAuctionInputEncoding,
      BooleanListMap.boolIdentityEquiv, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X] using outputsInTime input

end EdgeListNativeMachine
end LOS02CombinatorialAuctions
