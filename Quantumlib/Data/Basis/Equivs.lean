import Quantumlib.Data.Basis.Notation
import Quantumlib.Data.Matrix.Basic
import Quantumlib.Data.Matrix.KroneckerCMatrix

@[simp]
lemma bra0_mul_ket0 : ⟨0∣0⟩ = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i; fin_cases j
  simp

@[simp]
lemma ket0_mul_bra0 : ∣0⟩⟨0∣ = !![1, 0;
                                  0, 0] := by
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;> simp

@[simp]
lemma bra0_mul_ket1 : ⟨0∣1⟩ = 0 := by
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i; fin_cases j
  simp

@[simp]
lemma ket0_mul_bra1 : ∣0⟩⟨1∣ = !![0, 1;
                                  0, 0] := by
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;> simp

@[simp]
lemma bra1_mul_ket0 : ⟨1∣0⟩ = 0 := by
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i; fin_cases j
  simp

@[simp]
lemma ket1_mul_bra0 : ∣1⟩⟨0∣ = !![0, 0;
                                  1, 0] := by
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;> simp

@[simp]
lemma bra1_mul_ket1 : ⟨1∣1⟩ = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i; fin_cases j
  simp

@[simp]
lemma ket1_mul_bra1 : ∣1⟩⟨1∣ = !![0, 0;
                                  0, 1] := by
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;> simp

@[simp]
lemma ket0bra0_plus_ket1bra1 : ∣0⟩⟨0∣ + ∣1⟩⟨1∣ = 1 := by
  ext i j
  simp_rw [Matrix.add_apply, Matrix.mul_apply, Finset.sum]
  fin_cases i <;> fin_cases j <;> simp

@[simp]
lemma ket1bra1_plus_ket0bra0 : ∣1⟩⟨1∣ + ∣0⟩⟨0∣ = 1 := by
  rw [add_comm]
  apply ket0bra0_plus_ket1bra1
