import Quantumlib.Data.Basic
import Quantumlib.Tactic.Basic

open Matrix KroneckerCMatrix

@[simp]
lemma σx_mul_ket0 : σx * ∣0⟩ = ∣1⟩ := by
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i
    <;> simp [σx]

@[simp]
lemma bra0_mul_σx : ⟨0∣ * σx = ⟨1∣ := by
  simp only [σx]
  ext i j
  fin_cases j
    <;> rw [Matrix.mul_apply]
    <;> simp

@[simp]
lemma σx_mul_ket1 : σx * ∣1⟩ = ∣0⟩ := by
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i
    <;> simp [σx]

@[simp]
lemma bra1_mul_σx : ⟨1∣ * σx = ⟨0∣ := by
  ext i j
  rw [Matrix.mul_apply]
  fin_cases j
    <;> simp [σx]


lemma EPRpair_create :
  cnot * (hadamard ⊗ (1 : CSquare 2)) * ∣00⟩ = EPRpair := by
    simp only [kroneckerCMatrix, cnot, hadamard, EPRpair]
    ext i j
    simp_rw [Matrix.mul_apply]
    simp [Finset.sum, Fin.modNat, Fin.divNat]
    fin_cases i <;> simp <;> rfl

@[simp]
lemma q_mul_bra0_mul_σx : ∀ (q : CVector 2), (q * ⟨0∣) * σx = q * ⟨1∣ := by
  intros
  rw [Matrix.mul_assoc, bra0_mul_σx]

@[simp]
lemma q_mul_bra1_mul_σx : ∀ (q : CVector 2), (q * ⟨1∣) * σx = q * ⟨0∣ := by
  intros
  rw [Matrix.mul_assoc, bra1_mul_σx]

@[simp]
lemma σx_mul_ket0_mul_q : ∀ (q : CMatrix 1 2), σx * (∣0⟩ * q) = ∣1⟩ * q := by
  intros
  rw [←Matrix.mul_assoc, σx_mul_ket0]

@[simp]
lemma σx_mul_ket1_mul_q : ∀ (q : CMatrix 1 2), σx * (∣1⟩ * q) = ∣0⟩ * q := by
  intros
  rw [←Matrix.mul_assoc, σx_mul_ket1]

@[simp]
lemma q1_mul_bra0_mul_ket0_mul_q2 : ∀ (q₁ : CMatrix 2 1) (q₂ : CMatrix 1 2), 
  (q₁ * ⟨0∣) * (∣0⟩ * q₂) = q₁ * q₂ := by
  intros 
  rw [Matrix.mul_assoc, ←Matrix.mul_assoc ⟨0∣]
  simp

@[simp]
lemma q1_mul_bra1_mul_ket0_mul_q2 : ∀ (q₁ : CMatrix 2 1) (q₂ : CMatrix 1 2), 
  (q₁ * ⟨1∣) * (∣0⟩ * q₂) = 0 := by
  intros 
  rw [Matrix.mul_assoc, ←Matrix.mul_assoc ⟨1∣]
  simp

@[simp]
lemma q1_mul_bra0_mul_ket1_mul_q2 : ∀ (q₁ : CMatrix 2 1) (q₂ : CMatrix 1 2), 
  (q₁ * ⟨0∣) * (∣1⟩ * q₂) = 0 := by
  intros 
  rw [Matrix.mul_assoc, ←Matrix.mul_assoc ⟨0∣]
  simp

@[simp]
lemma q1_mul_bra1_mul_ket1_mul_q2 : ∀ (q₁ : CMatrix 2 1) (q₂ : CMatrix 1 2), 
  (q₁ * ⟨1∣) * (∣1⟩ * q₂) = q₁ * q₂ := by
  intros 
  rw [Matrix.mul_assoc, ←Matrix.mul_assoc ⟨1∣]
  simp

@[simp]
lemma swap_def : ∀ (q₁ q₂ : CVector 2), swap * (q₁ ⊗ q₂) = q₂ ⊗ q₁ := by
  intros
  simp [swap, vecHead, vecTail, Fin.modNat, Fin.divNat]
  ext i
  fin_cases i <;> simp <;> ring_nf!

