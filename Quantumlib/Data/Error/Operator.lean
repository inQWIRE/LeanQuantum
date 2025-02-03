import Quantumlib.Data.Gate.Pauli

import Mathlib.Data.Vector.Basic
import Mathlib.Data.List.Basic


structure StabilizerCode where
  n : ℕ
  k : ℕ
  d : ℕ
  stabilizers : List (Pauli n)
  logicalX : List.Vector (Pauli n) k
  logicalZ : List.Vector (Pauli n) k
  stabilizers_commute : ∀ S₁ ∈ stabilizers, ∀ S₂ ∈ stabilizers, S₁.commutesWith S₂
  logical_commute : ∀ i j, !(logicalX.get i).commutesWith (logicalZ.get j) = (i = j)

namespace StabilizerCode

def syndrome (code : StabilizerCode) (E : Pauli code.n) : List Bool :=
  code.stabilizers.map (!E.commutesWith ·)

def bitFlipCode : StabilizerCode where
  n := 3
  k := 1
  d := 3
  stabilizers := [
    { x := 0, z := 0b110}, -- ZZI
    { x := 0, z := 0b011}  -- IZZ
  ]
  logicalX := ⟨[{x := 0b111, z := 0}], rfl⟩  -- XXX
  logicalZ := ⟨[{x := 0, z := 0b111}], rfl⟩  -- ZZZ

  stabilizers_commute := by
    intros S₁ hS₁ S₂ hS₂
    fin_cases hS₁ <;> fin_cases hS₂ <;> rfl
  logical_commute := by
    intros i j
    fin_cases i; fin_cases j; rfl


theorem bitFlipCode_corrects_single_qubit_errors (E : Pauli 3) (hE : E.weight = 1) (hX : E.z = 0) :
  ∃ C : Pauli 3, C.weight ≤ 1 ∧ (E.commutesWith C) := by

  sorry

end StabilizerCode
