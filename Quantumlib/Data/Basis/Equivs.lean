import Quantumlib.Data.Basis.Notation
import Quantumlib.Tactic.Basic

@[simp]
lemma braket0_mul_braket1 : ∣0⟩⟨0∣ * ∣1⟩⟨1∣ = 0 := by 
  solve_matrix

@[simp]
lemma braket0_mul_braket0 : ∣0⟩⟨0∣ * ∣0⟩⟨0∣ = ∣0⟩⟨0∣ := by 
  solve_matrix

@[simp]
lemma braket1_mul_braket0 : ∣1⟩⟨1∣ * ∣0⟩⟨0∣ = 0 := by
  solve_matrix

@[simp]
lemma braket1_mul_braket1 : ∣1⟩⟨1∣ * ∣1⟩⟨1∣ = ∣1⟩⟨1∣ := by 
  solve_matrix

@[simp]
lemma ketbra0_plus_ketbra1 : ∣0⟩⟨0∣ + ∣1⟩⟨1∣ = 1 := by
  solve_matrix

@[simp]
lemma ketbra1_plus_ketbra0 : ∣1⟩⟨1∣ + ∣0⟩⟨0∣ = 1 := by
  solve_matrix


@[simp]
lemma braket0_def : ⟨0∣0⟩ = 1 := by
  solve_matrix

@[simp]
lemma ketbra0_def : ∣0⟩⟨0∣ = !![1, 0;
                                0, 0] := by
  solve_matrix


@[simp]
lemma bra0ket1_def : ⟨0∣1⟩ = 0 := by solve_matrix

@[simp]
lemma ket0bra1_def : ∣0⟩⟨1∣ = !![0, 1;
                                 0, 0] := by
  solve_matrix

@[simp]
lemma bra1ket0_def : ⟨1∣0⟩ = 0 := by solve_matrix

@[simp]
lemma ket1bra0_def : ∣1⟩⟨0∣ = !![0, 0;
                                 1, 0] := by
  solve_matrix

@[simp]
lemma braket1_def : ⟨1∣1⟩ = 1 := by
  solve_matrix

@[simp]
lemma ketbra1_def : ∣1⟩⟨1∣ = !![0, 0;
                                0, 1] := by
  solve_matrix

