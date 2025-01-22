import Quantumlib.Data.Basis.Notation
import Quantumlib.Data.Matrix.Basic
import Quantumlib.Data.Matrix.Kron
import Quantumlib.Tactic.Basic

@[simp]
lemma braket0_def : ⟨0∣0⟩ = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i; fin_cases j
  simp

lemma ketbra0_def : ∣0⟩⟨0∣ = !![1, 0;
                                0, 0] := by
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;> simp

@[simp]
lemma bra0ket1_def : ⟨0∣1⟩ = 0 := by
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i; fin_cases j
  simp

lemma ket0bra1_def : ∣0⟩⟨1∣ = !![0, 1;
                                 0, 0] := by
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;> simp

@[simp]
lemma bra1ket0_def : ⟨1∣0⟩ = 0 := by
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i; fin_cases j
  simp

lemma ket1bra0_def : ∣1⟩⟨0∣ = !![0, 0;
                                 1, 0] := by
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;> simp

@[simp]
lemma braket1_def : ⟨1∣1⟩ = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i; fin_cases j
  simp

lemma ketbra1_def : ∣1⟩⟨1∣ = !![0, 0;
                                0, 1] := by
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;> simp

@[simp]
lemma braket0_mul_braket1 : ∣0⟩⟨0∣ * ∣1⟩⟨1∣ = 0 := by 
  rw [ketbra0_def, ketbra1_def]
  solve_matrix

@[simp]
lemma braket0_mul_braket0 : ∣0⟩⟨0∣ * ∣0⟩⟨0∣ = ∣0⟩⟨0∣ := by 
  rw [ketbra0_def]
  solve_matrix

@[simp]
lemma braket1_mul_braket0 : ∣1⟩⟨1∣ * ∣0⟩⟨0∣ = 0 := by
  rw [ketbra0_def, ketbra1_def]
  solve_matrix

@[simp]
lemma braket1_mul_braket1 : ∣1⟩⟨1∣ * ∣1⟩⟨1∣ = ∣1⟩⟨1∣ := by 
  rw [ketbra1_def]
  solve_matrix

@[simp]
lemma ketbra0_plus_ketbra1 : ∣0⟩⟨0∣ + ∣1⟩⟨1∣ = 1 := by
  rw [ketbra0_def, ketbra1_def]
  solve_matrix

@[simp]
lemma ketbra1_plus_ketbra0 : ∣1⟩⟨1∣ + ∣0⟩⟨0∣ = 1 := by
  rw [add_comm]
  apply ketbra0_plus_ketbra1

attribute [simp] ketbra0_def ketbra1_def ket0bra1_def ket1bra0_def
