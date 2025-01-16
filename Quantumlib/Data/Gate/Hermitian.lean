import Quantumlib.Data.Gate.Basic
import Quantumlib.Data.Gate.Pauli
import Quantumlib.Data.Gate.ConjTranspose
import Quantumlib.Tactic.Basic

import Mathlib.LinearAlgebra.Matrix.Hermitian

open Matrix

open Lean Elab Command in
elab "make_hermitian " gates:ident+ : command => do
  for gate in gates do
    let name :=
      gate.getId.toString ++ "_isHermitian"
      |> Name.mkStr1
      |> mkIdent
    let decl ← `(
      @[simp]
      lemma $name : ($gate).IsHermitian := by
        unfold $gate
        simp [IsHermitian]
        solve_matrix
    )
    elabCommand decl

make_hermitian hadamard cnot swap σx σy σz

example : hadamard = hadamardᴴ := by rw   [hadamard_isHermitian]
example : cnot     = cnotᴴ     := by simp [cnot_isHermitian.eq]


lemma controlM_isHermitian : ∀ (M : CSquare n), 
  M.IsHermitian → (controlM M).IsHermitian := by
    intros M h
    simp only [IsHermitian] at h ⊢
    rw [controlM_conjTranspose, h]

