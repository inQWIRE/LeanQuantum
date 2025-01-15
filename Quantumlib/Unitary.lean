import Quantumlib.Data.Basic
import Quantumlib.Data.Gate.Rotation
import Quantumlib.Data.Matrix.Unitary

import Mathlib.LinearAlgebra.UnitaryGroup

open Complex in
lemma rotation_isUnitary : ∀ θ φ δ, (rotation θ φ δ).IsUnitary := by
  intros θ φ δ
  simp_rw [Matrix.mem_unitaryGroup_iff', star, rotation_conjTranspose]
  simp only [rotation]
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j
    <;> simp
    <;> rw [neg_div]
  all_goals try rw [Complex.cos_neg]
  all_goals try rw [Complex.sin_neg]
  · calc
      _ = (cos (↑θ / 2)) ^ 2 + exp (-↑φ * I) * exp (↑φ * I) * (sin (↑θ / 2)) ^ 2 := by ring_nf
      _ = (cos (↑θ / 2)) ^ 2 + exp (-↑φ * I + ↑φ * I) * (sin (↑θ / 2)) ^ 2 := by rw [exp_add]
      _ = _ := by simp
  · calc
      _ = -exp (↑δ * I) * cos (↑θ / 2) * sin (↑θ / 2) +
           exp (-↑φ * I) * exp ((↑φ + ↑δ) * I) * cos (↑θ / 2) * sin (↑θ / 2) := by ring_nf
      _ = -exp (↑δ * Complex.I) * cos (↑θ / 2) * sin (↑θ / 2) +
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
          exp ((-↑δ + -↑φ) * I) * exp ((↑φ + ↑δ) * Complex.I) * (cos (↑θ / 2)) ^ 2 := by ring_nf
      _ = exp 0 * (sin (↑θ / 2)) ^ 2 + exp 0 * (cos (↑θ / 2)) ^ 2 := by
        repeat rw [←exp_add]; ring_nf
      _ = _ := by simp

lemma hadamard_isUnitary : hadamard.IsUnitary := by 
  rw [←rotation_hadamard]
  apply rotation_isUnitary

lemma σx_isUnitary : σx.IsUnitary := by
  rw [←rotation_σx]
  apply rotation_isUnitary

lemma σy_isUnitary : σy.IsUnitary := by
  rw [←rotation_σy]
  apply rotation_isUnitary

lemma σz_isUnitary : σz.IsUnitary := by
  rw [←rotation_σz]
  apply rotation_isUnitary

lemma phase_isUnitary : ∀ φ, (phaseShift φ).IsUnitary := by
  intros φ
  rw [←rotation_phaseShift φ]
  apply rotation_isUnitary

lemma sGate_isUnitary : sGate.IsUnitary := by 
  apply phase_isUnitary

lemma tGate_isUnitary : tGate.IsUnitary := by 
  apply phase_isUnitary

lemma controlM_isUnitary : ∀ (M : CSquare n),
  M.IsUnitary → (controlM M).IsUnitary := by
    intros M h
    simp_rw [Matrix.mem_unitaryGroup_iff', star] at h ⊢
    ext i j
    simp_rw [Matrix.mul_apply, Matrix.conjTranspose_apply]
    unfold controlM
    admit

lemma 
