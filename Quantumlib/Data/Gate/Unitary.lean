import Quantumlib.Data.Basic
import Quantumlib.Data.Gate.ConjTranspose
import Quantumlib.Data.Gate.Rotate
import Quantumlib.Data.Matrix.Unitary

import Mathlib.LinearAlgebra.UnitaryGroup

open Matrix

open Complex in
lemma rotate_isUnitary : ∀ θ φ δ, (rotate θ φ δ).IsUnitary := by
  intros θ φ δ
  simp_rw [Matrix.mem_unitaryGroup_iff', star, rotate_conjTranspose]
  simp only [rotate]
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j
    <;> simp
    <;> rw [neg_div]
  all_goals try rw [cos_neg]
  all_goals try rw [sin_neg]
  -- Getting the exps next to each other and simplifying
  · calc
      _ = (cos (↑θ / 2)) ^ 2 + exp (-↑φ * I) * exp (↑φ * I) * (sin (↑θ / 2)) ^ 2 := by ring_nf
      _ = (cos (↑θ / 2)) ^ 2 + exp (-↑φ * I + ↑φ * I) * (sin (↑θ / 2)) ^ 2 := by rw [exp_add]
      _ = _ := by simp
  · calc
      _ = -exp (↑δ * I) * cos (↑θ / 2) * sin (↑θ / 2) +
           exp (-↑φ * I) * exp ((↑φ + ↑δ) * I) * cos (↑θ / 2) * sin (↑θ / 2) := by ring_nf
      _ = -exp (↑δ * I) * cos (↑θ / 2) * sin (↑θ / 2) +
           exp (↑δ * I) * cos (↑θ / 2) * sin (↑θ / 2) := by rw [←exp_add]; ring_nf
      _ = _ := by simp
  · calc
    _ = -exp (-↑δ * I) * sin (↑θ / 2) * cos (↑θ / 2) +
         exp ((-↑δ + -↑φ) * I) * exp (↑φ * I) * cos (↑θ / 2) * sin (↑θ / 2) := by ring_nf
    _ = -exp (-↑δ * I) * sin (↑θ / 2) * cos (↑θ / 2) +
         exp (-↑δ * I)  * cos (↑θ / 2) * sin (↑θ / 2) := by rw [←exp_add]; ring_nf
    _ = _ := by ring_nf
  · calc
      _ = exp (-↑δ * I) * exp (↑δ * I) * (sin (↑θ / 2)) ^ 2 +
          exp ((-↑δ + -↑φ) * I) * exp ((↑φ + ↑δ) * I) * (cos (↑θ / 2)) ^ 2 := by ring_nf
      _ = exp 0 * (sin (↑θ / 2)) ^ 2 + exp 0 * (cos (↑θ / 2)) ^ 2 := by
        repeat rw [←exp_add]; ring_nf
      _ = _ := by simp

lemma hadamard_isUnitary : hadamard.IsUnitary := by 
  rw [←rotate_hadamard]
  apply rotate_isUnitary

lemma σx_isUnitary : σx.IsUnitary := by
  rw [←rotate_σx]
  apply rotate_isUnitary

lemma σy_isUnitary : σy.IsUnitary := by
  rw [←rotate_σy]
  apply rotate_isUnitary

lemma σz_isUnitary : σz.IsUnitary := by
  rw [←rotate_σz]
  apply rotate_isUnitary

lemma phaseShift_isUnitary : ∀ φ, (phaseShift φ).IsUnitary := by
  intros φ
  rw [←rotate_phaseShift φ]
  apply rotate_isUnitary

lemma sGate_isUnitary : sGate.IsUnitary := by 
  apply phaseShift_isUnitary

lemma tGate_isUnitary : tGate.IsUnitary := by 
  apply phaseShift_isUnitary

lemma controlM_isUnitary : ∀ (M : CSquare n),
  M.IsUnitary → (controlM M).IsUnitary := by
    intros M h
    simp_rw [Matrix.mem_unitaryGroup_iff', star] at h ⊢
    rw [controlM_conjTranspose, controlM_mul_controlM, h, controlM_1]

lemma cnot_isUnitary : cnot.IsUnitary := by
  simp_rw [Matrix.mem_unitaryGroup_iff', cnot]
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;> simp [Finset.sum]

lemma notc_isUnitary : notc.IsUnitary := by
  simp_rw [Matrix.mem_unitaryGroup_iff', notc]
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;> simp [Finset.sum]

lemma one_isUnitary : (1 : CSquare n).IsUnitary := by
  simp_rw [Matrix.mem_unitaryGroup_iff']
  simp

lemma not_zero_isUnitary {n : ℕ} [NeZero n] : ¬(0 : CSquare n).IsUnitary := by
  simp_rw [Matrix.mem_unitaryGroup_iff']
  simp

lemma swap_isUnitary : swap.IsUnitary := by
  simp_rw [Matrix.mem_unitaryGroup_iff', swap]
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;> simp [Finset.sum]

