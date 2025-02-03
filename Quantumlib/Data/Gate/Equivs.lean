import Quantumlib.Data.Basis.Notation
import Quantumlib.Data.Basis.Equivs
import Quantumlib.Data.Gate.Basic
import Quantumlib.Data.Gate.Pauli
import Quantumlib.Data.Gate.PhaseShift
import Quantumlib.Data.Gate.Rotate
import Quantumlib.Data.Matrix.Basic
import Quantumlib.Data.Matrix.Kron
import Quantumlib.Tactic.Basic

open Matrix Kron

@[simp]
lemma hadamardK_one : hadamardK 1 = hadamard := by
  simp [hadamardK, CMatrix.powBitVec]

@[simp]
lemma hadamard_mul_hadamard : hadamard * hadamard = 1 := by
  simp only [hadamard]
  ext i j
  fin_cases i <;> fin_cases j
    <;> field_simp
    <;> apply Complex.ext
    <;> simp
    <;> ring_nf

@[simp]
lemma hadamard_transpose : hadamardᵀ = hadamard := by
  solve_matrix [hadamard]

@[simp]
lemma sqrtx_mul_sqrtx : sqrtx * sqrtx = σx := by
  simp only [sqrtx, σx]
  ext i j
  fin_cases i <;> fin_cases j
    <;> apply Complex.ext 
    <;> simp
    <;> ring_nf

lemma sqrtx_decompose :
  hadamard * phaseShift (π / 2) * hadamard = sqrtx := by
  simp_rw [sqrtx, hadamard, phaseShift, Complex.exp_mul_I]
  ext i j
  fin_cases i <;> fin_cases j
    <;> apply Complex.ext
    <;> simp
    <;> field_simp

@[simp]
lemma xRotate_π : xRotate π = -Complex.I • σx := by
  simp [xRotate, σx]

@[simp]
lemma yRotate_π : yRotate π = -Complex.I • σy := by
  simp [yRotate, σy]

@[simp]
lemma rotate_hadamard : rotate (π / 2) 0 π = hadamard := by
  simp [rotate, hadamard]
  ring_nf
  rw [mul_one_div]
  ext i j
  fin_cases i <;> fin_cases j
    <;> apply Complex.ext
    <;> simp

@[simp]
lemma rotate_σx : rotate π 0 π = σx := by
  simp [rotate, σx]
  
@[simp]
lemma rotate_σy : rotate π (π / 2) (π / 2) = σy := by
  simp only [rotate, σy]
  rw [Complex.exp_mul_I]
  simp

@[simp]
lemma rotate_σz : rotate 0 0 π = σz := by
  simp [rotate, σz]

lemma rotate_xRotate : ∀ θ,
  rotate θ (3 * π / 2) (π / 2) = xRotate θ := by
  intros
  simp [rotate, xRotate]
  rw [Complex.exp_mul_I]
  simp
  ext i j
  fin_cases i <;> fin_cases j 
    <;> simp
  rw [add_mul, Complex.exp_add,
      Complex.exp_three_pi_div_two,
      neg_mul, Complex.exp_mul_I]
  simp

lemma rotate_yRotate : ∀ θ,
  rotate θ 0 0 = yRotate θ := by
  intros
  simp [rotate, yRotate]

lemma rotate_phaseShift : ∀ θ,
  rotate 0 0 θ = phaseShift θ := by
  simp [rotate, phaseShift]

lemma rotate_one : rotate 0 0 0 = 1 := by
  solve_matrix [rotate]

@[simp]
lemma phaseShift_zero : phaseShift 0 = 1 := by
  solve_matrix [phaseShift]

@[simp]
lemma phaseShift_π : phaseShift π = σz := by
  simp [phaseShift, σz]

@[simp]
lemma phaseShift_2π : phaseShift (2 * π) = 1 := by
  solve_matrix [phaseShift]

@[simp]
lemma phaseShift_neg_π : phaseShift (-π) = σz := by
  simp [phaseShift, σz]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  rw [Complex.exp_neg]
  field_simp

@[simp]
lemma phaseShift_mul_phaseShift : ∀ θ₁ θ₂,
  phaseShift θ₁ * phaseShift θ₂ = phaseShift (θ₁ + θ₂) := by
    intros
    simp [phaseShift, ←Complex.exp_add, add_mul]

@[simp]
lemma phaseShift_pow : ∀ (n : ℕ) θ,
  (phaseShift θ) ^ n  = phaseShift (n * θ) := by
    intros n θ
    induction n
    case zero => simp
    case succ n' ih => 
      simp [pow_succ]
      rw [add_mul, ←phaseShift_mul_phaseShift, ih]
      ring_nf

@[simp]
lemma sGate_mul_sGate : sGate * sGate = σz := by
  simp [sGate]

@[simp]
lemma tGate_mul_tGate : tGate * tGate = sGate := by
  simp only [tGate, phaseShift_mul_phaseShift, sGate]
  ring_nf

section Paulis
open Lean Elab Command

private def pauliProd : Name → Name → CommandElabM Syntax
  | `σx, `σx => `(1)
  | `σy, `σy => `(1)
  | `σz, `σz => `(1)
  | `σx, `σy => `( Complex.I • σz)
  | `σy, `σz => `( Complex.I • σx)
  | `σz, `σx => `( Complex.I • σy)
  | `σy, `σx => `(-Complex.I • σz)
  | `σz, `σy => `(-Complex.I • σx)
  | `σx, `σz => `(-Complex.I • σy)
  |  a, b    => panic! s!"Unexpected combination {a}, {b}"

elab "make_pauli_mul_table" : command => do
  let paulis := [`σx, `σy, `σz]

  for (a, b) in paulis.product paulis do
    let name := s!"{a}_mul_{b}" |> Name.mkStr1 |> mkIdent
    let res ← pauliProd a b
    let decl ← `(
      @[simp]
      lemma $name : $(mkIdent a) * $(mkIdent b) = $(⟨res⟩) := by
        try unfold σx 
        try unfold σy 
        try unfold σz 
        solve_matrix
    )
    elabCommand decl

end Paulis
make_pauli_mul_table

lemma controlM_def : ∀ (M : CSquare n),
  controlM M = ∣0⟩⟨0∣ ⊗ 1 + ∣1⟩⟨1∣ ⊗ M := by
    intros
    ext x y
    simp only [controlM]
    have hxsubn : ↑x - n < n := by omega
    have hysubn : ↑y - n < n := by omega
    have hngt0 : 0 < n := by omega

    split_ifs
    next h =>
      simp_all
      obtain ⟨left, right⟩ := h
      subst right
      have : x.divNat = 0 := by
        simp [Fin.divNat]
        conv in ↑x / n =>
          rw [Nat.div_eq_of_lt left]
          rfl
        rfl
      simp [this]
    next h hxy =>
      simp_all [blockDiagonal]
      obtain ⟨hx, hy⟩ := hxy
      have : y.divNat = 1 := by
        simp [Fin.divNat]
        conv in ↑y / n =>
          rw [Nat.div_eq_sub_div hngt0 hy,
              Nat.div_eq_of_lt hysubn,
              zero_add]
          rfl
        rfl
      rw [this]
      have : x.divNat = 1 := by
        simp [Fin.divNat]
        conv in ↑x / n =>
          rw [Nat.div_eq_sub_div hngt0 hx,
              Nat.div_eq_of_lt hxsubn,
              zero_add]
          rfl
        rfl
      simp [this, Fin.modNat, Fin.subNat]
      congr <;>
        rwa [Nat.mod_eq, if_pos (by omega),
             Nat.mod_eq_of_lt]
    next h hxy =>
      simp_all [blockDiagonal]
      cases h : decide (x < n) <;> simp_all
      · rename' hxy => hy, h => hx
        have : y.divNat = 0 := by
          simp [Fin.divNat]
          conv in ↑y / n =>
            rw [Nat.div_eq_of_lt hy]
            rfl
          rfl
        rw [this]
        have : x.divNat = 1 := by
          simp [Fin.divNat]
          conv in ↑x / n =>
            rw [Nat.div_eq_sub_div hngt0 hx,
                Nat.div_eq_of_lt hxsubn,
                zero_add]
            rfl
          rfl
        simp [this]
      · rename_i hxney
        have : x.divNat = 0 := by
          simp [Fin.divNat]
          conv in ↑x / n =>
            rw [Nat.div_eq_of_lt h]
            rfl
          rfl
        simp_all [this]
        generalize hyDiv : y.divNat = yDiv
        fin_cases yDiv <;> simp
        rw [if_neg]
        intros contra
        simp [Fin.divNat] at hyDiv
        simp [Fin.modNat] at contra
        apply hxney
        have : ↑y < n := by
          apply Nat.lt_of_div_eq_zero hngt0
          rw [Fin.ext_iff] at hyDiv
          simp_all
        rwa [Nat.mod_eq, if_neg (by omega),
             Nat.mod_eq, if_neg (by omega),
             ←Fin.ext_iff] at contra

@[simp]
lemma controlM_mul_controlM : ∀ (M₁ M₂ : CSquare n),
  controlM M₁ * controlM M₂ = controlM (M₁ * M₂) := by
    intros
    repeat rw [controlM_def]
    repeat rw [mul_add]
    repeat rw [add_mul]
    repeat rw [←mul_kron_mul]
    simp [-ketbra0_def, -ketbra1_def]

@[simp]
lemma controlM_one : controlM (1 : CSquare n) = 1 := by
  rw [controlM_def, ←add_kron,
      ketbra0_plus_ketbra1,
      one_kron_one]

@[simp]
lemma controlM_σx : controlM σx = cnot := by
  solve_matrix [controlM, σx, cnot]

@[simp]
lemma cnot_decompose : ∣1⟩⟨1∣ ⊗ σx + ∣0⟩⟨0∣ ⊗ 1 = cnot := by
  solve_matrix [cnot, σx]

@[simp]
lemma notc_decompose : σx ⊗ ∣1⟩⟨1∣ + 1 ⊗ ∣0⟩⟨0∣ = notc := by
  solve_matrix [notc, σx]

@[simp]
lemma swap_mul_swap : swap * swap = 1 := by
  solve_matrix [swap, Finset.sum]

