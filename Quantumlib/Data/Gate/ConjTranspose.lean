import Quantumlib.Data.Basis.Notation
import Quantumlib.Data.Basis.Equivs
import Quantumlib.Data.Gate.Basic
import Quantumlib.Data.Gate.Equivs
import Quantumlib.Data.Gate.Pauli
import Quantumlib.Data.Gate.PhaseShift
import Quantumlib.Data.Gate.Rotate
import Quantumlib.Tactic.Basic

open Matrix

@[simp]
lemma controlM_conjTranspose : ∀ (M : CSquare n),
  (controlM M)ᴴ = controlM Mᴴ := by
    intros M
    ext i j
    rw [conjTranspose_apply]
    simp only [controlM]
    cases h : decide (j = i)
    · split_ifs <;> simp_all
    · cases hlt : decide (i < n) <;> cases hle : decide (n ≤ i) <;> simp_all
      split_ifs
      · apply not_lt_of_le at hlt
        contradiction
      · simp

@[simp]
lemma rotate_conjTranspose : ∀ θ φ δ,
  (rotate θ φ δ)ᴴ = rotate (-θ) (-δ) (-φ) := by
    intros θ φ δ
    simp only [rotate]
    ext i j
    rw [Matrix.conjTranspose_apply]
    fin_cases i <;> fin_cases j
      <;> simp [←Complex.exp_conj, ←Complex.cos_conj, ←Complex.sin_conj]
      <;> field_simp [OfNat.ofNat]
      <;> rw [neg_div]
    all_goals try rw [Complex.cos_neg]
    all_goals try rw [Complex.sin_neg]
    all_goals ring_nf

@[simp]
lemma phaseShift_conjTranspose : ∀ θ, (phaseShift θ)ᴴ = phaseShift (-θ) := by
  intros θ
  iterate 2 rw [←rotate_phaseShift]
  rw [rotate_conjTranspose]
  simp [rotate]
