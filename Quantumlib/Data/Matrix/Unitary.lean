import Quantumlib.Data.Matrix.Basic
import Quantumlib.Data.Matrix.Kron

open Kron

namespace Matrix

abbrev IsUnitary {n} (M : CSquare n) := M ∈ Matrix.unitaryGroup (Fin n) ℂ

theorem transpose_of_isUnitary : ∀ (M : CSquare n),
  M.IsUnitary → Mᵀ.IsUnitary := by
    intros M h
    simp_rw [mem_unitaryGroup_iff']
    simp_rw [mem_unitaryGroup_iff] at h
    simp only [star] at *
    rw [←conjTranspose_transpose_comm,
        ←transpose_mul, h, transpose_one]

theorem conjTranspose_of_isUnitary : ∀ (M : CSquare n),
  M.IsUnitary → Mᴴ.IsUnitary := by
    intros M h
    simp_rw [mem_unitaryGroup_iff']
    simp_rw [mem_unitaryGroup_iff] at h
    simp only [star] at *
    simpa

theorem kron_of_isUnitary : ∀ (M₁ : CSquare m) (M₂ : CSquare n),
  M₁.IsUnitary → M₂.IsUnitary → (M₁ ⊗ M₂).IsUnitary := by
    intros M₁ M₂ h₁ h₂
    simp_rw [mem_unitaryGroup_iff', star] at *
    rw [conjTranspose_kron, ←mul_kron_mul, h₁, h₂, one_kron_one]

theorem mul_of_isUnitary : ∀ (M₁ M₂ : CSquare n),
  M₁.IsUnitary → M₂.IsUnitary → (M₁ * M₂).IsUnitary := by
    intros M₁ M₂ h₁ h₂
    simp_rw [mem_unitaryGroup_iff', star] at *
    rw [conjTranspose_mul, mul_assoc, ←mul_assoc M₁ᴴ, h₁, one_mul, h₂]

theorem smul_of_isUnitary : ∀ (c : ℂ) (M : CSquare n),
  M.IsUnitary → c ∈ unitary ℂ → (c • M).IsUnitary := by
    intros c M hM hc
    simp_rw [mem_unitaryGroup_iff'] at hM ⊢
    rw [unitary.mem_iff_self_mul_star] at hc
    rw [star_smul, mul_smul, smul_mul, ←smul_assoc, smul_eq_mul, hc, hM]
    simp


end Matrix

