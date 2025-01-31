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
  stabilizers_commute : ∀ S₁ ∈ stabilizers, ∀ S₂ ∈ stabilizers, ¬(Pauli.symplecticProduct S₁ S₂)
  logical_commute : ∀ i j, Pauli.symplecticProduct (logicalX.get i) (logicalZ.get j) = (i = j)

namespace StabilizerCode

def syndrome (code : StabilizerCode) (E : Pauli code.n) : List Bool :=
  code.stabilizers.map (fun S => Pauli.symplecticProduct E S)

def bitFlipCode : StabilizerCode where
  n := 3
  k := 1
  d := 3
  stabilizers := [
    { x := ⟨[false, false, false], rfl⟩, z := ⟨[true, true, false], rfl⟩}, -- ZZI
    { x := ⟨[false, false, false], rfl⟩, z := ⟨[false, true, true], rfl⟩}  -- IZZ
  ]
  logicalX := ⟨[⟨1, ⟨[true, true, true], rfl⟩, ⟨[false, false, false], rfl⟩⟩], rfl⟩  -- XXX
  logicalZ := ⟨[⟨1, ⟨[false, false, false], rfl⟩, ⟨[true, true, true], rfl⟩⟩], rfl⟩  -- ZZZ

  stabilizers_commute := by
    intro S₁ hS₁ S₂ hS₂
    -- Verify stabilizers commute by checking all pairs
    fin_cases hS₁ <;> fin_cases hS₂ <;> simp [Pauli.symplecticProduct] <;> rfl
  logical_commute := by
    intro i j
    -- Verify logical operators commute appropriately
    fin_cases i <;> fin_cases j <;> simp [Pauli.symplecticProduct, List.Vector.head]


theorem bitFlipCode_corrects_single_qubit_errors (E : Pauli 3) (hE : E.weight = 1) (hX : E.z = ⟨[false, false, false], rfl⟩) :
  ∃ C : Pauli 3, C.weight ≤ 1 ∧ (Pauli.symplecticProduct E C = false) := by
  sorry

end StabilizerCode
