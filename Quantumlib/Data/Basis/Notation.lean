import Quantumlib.Data.Basis.Basic
import Quantumlib.Data.Matrix.Basic
import Quantumlib.Data.Matrix.Kron
import Quantumlib.Tactic.Basic

import Lean

open Matrix Kron

open Lean PrettyPrinter Delaborator

def mkKronChain (terms: List (TSyntax `term)) : MacroM (TSyntax `term) := do
    match terms with
    | [] => Macro.throwError "Empty list of terms"
    | [v] => pure v
    | v::vs => vs.foldlM (init := v) fun acc v' => 
               `(($acc) ⊗ ($v'))

syntax (name := kets) "∣" num "⟩" : term
@[macro kets] def ketsImpl : Macro 
  | `(∣ $n ⟩ ) => do
    let digits := (n.raw.isLit? `num).get!.toList
    let qubits ← (digits.mapM fun d => do
        match d with
        | '0' => ``(ket0)
        | '1' => ``(ket1)
        | _   =>
          Macro.throwError s!"invalid qubit state: expected 0 or 1, got {d}")
    mkKronChain qubits
  | _ => Macro.throwUnsupported

@[app_unexpander ket0]
def ket0Unexpander : Unexpander
  | `($(_) $arg1 $arg2) => `(∣0⟩ $arg1 $arg2)
  | `($(_) $arg) => `(∣0⟩ $arg)
  | `($(_)) => `(∣0⟩)

@[app_unexpander ket1]
def ket1Unexpander : Unexpander
  | `($(_) $arg1 $arg2) => `(∣1⟩ $arg1 $arg2)
  | `($(_) $arg) => `(∣1⟩ $arg)
  | `($(_)) => `(∣1⟩)

syntax (name := bras) "⟨" num "∣" : term
@[macro bras] def brasImpl : Macro 
  | `(⟨ $n ∣) => do
    let digits := (n.raw.isLit? `num).get!.toList
    let qubits ← (digits.mapM fun d => do
        match d with
        | '0' => ``(bra0)
        | '1' => ``(bra1)
        | _   =>
          Macro.throwError s!"invalid qubit state: expected 0 or 1, got {d}")
    mkKronChain qubits
  | _ => Macro.throwUnsupported

@[app_unexpander bra0]
def bra0Unexpander : Unexpander
  | `($(_) $arg1 $arg2) => `((⟨0∣) $arg1 $arg2)
  | `($(_) $arg) => `((⟨0∣) $arg)
  | `($(_)) => `((⟨0∣))

@[app_unexpander bra1]
def bra1Unexpander : Unexpander
  | `($(_) $arg1 $arg2) => `((⟨1∣) $arg1 $arg2)
  | `($(_) $arg) => `((⟨1∣) $arg)
  | `($(_)) => `((⟨1∣))

@[app_unexpander kron]
def kronUnexpander : Unexpander
  | `($(_) ∣$num₁:num⟩ ∣$num₂:num⟩) => do
    let n₁ := (num₁.raw.isLit? `num).get!
    let n₂ := (num₂.raw.isLit? `num).get!
    let n_sum := TSyntax.mk (Syntax.mkNumLit (n₁ ++ n₂))
    `(∣$n_sum⟩)
  | `($(_) (⟨$num₁:num∣) (⟨$num₂:num∣)) => do
    let n₁ := (num₁.raw.isLit? `num).get!
    let n₂ := (num₂.raw.isLit? `num).get!
    let n_sum := TSyntax.mk (Syntax.mkNumLit (n₁ ++ n₂))
    `(⟨$n_sum∣)
  | _ => throw ()

macro "∣" n₁:num "⟩⟨" n₂:num "∣" : term => `(∣$n₁⟩ * ⟨$n₂∣)
macro "⟨" n₁:num "∣" n₂:num "⟩" : term => `(⟨$n₁∣ * ∣$n₂⟩)

@[app_unexpander HMul.hMul]
def hmulUnexpander : Unexpander
  | `($(_) ∣$num₁⟩ (⟨$num₂∣)) => `(∣$num₁⟩⟨$num₂∣)
  | `($(_) (⟨$num₁∣) ∣$num₂⟩) => `(⟨$num₁∣$num₂⟩)
  | _ => throw ()

notation "∣+⟩" => xbasisPlus
notation "∣-⟩" => xbasisMinus

notation "∣R⟩" => ybasisPlus
notation "∣L⟩" => ybasisMinus

notation "∣Φ+⟩" => EPRpair

