import Quantumlib.Data.Gate.Basic
import Quantumlib.Data.Gate.Pauli
import Quantumlib.Data.Gate.ConjTranspose
import Quantumlib.Tactic.Basic

import Mathlib.LinearAlgebra.Matrix.Hermitian

open Matrix

open Lean Elab Command in
elab "make_hermitian " gates:ident+ : command => do
  for gate in gates do
    let name := gate.getId.appendAfter "_isHermitian" |> mkIdent
    let decl ← `(
      @[simp]
      lemma $name : ($gate).IsHermitian := by
        unfold $gate
        solve_matrix
    )
    elabCommand decl

make_hermitian hadamard cnot swap σx σy σz

lemma controlM_isHermitian : ∀ (M : CSquare n), 
  M.IsHermitian → (controlM M).IsHermitian := by
    intros M h
    simp only [IsHermitian] at h ⊢
    rw [controlM_conjTranspose, h]

lemma braket0_isHermitian : ∣0⟩⟨0∣.IsHermitian := by
  solve_matrix

lemma braket1_isHermitian : ∣1⟩⟨1∣.IsHermitian := by
  solve_matrix
