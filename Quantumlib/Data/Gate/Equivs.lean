import Quantumlib.Data.Basis.Notation
import Quantumlib.Data.Basis.Equivs
import Quantumlib.Data.Gate.Basic
import Quantumlib.Data.Gate.Pauli
import Quantumlib.Data.Gate.PhaseShift
import Quantumlib.Data.Gate.Rotation
import Quantumlib.Data.Matrix.Basic
import Quantumlib.Data.Matrix.Basic
import Quantumlib.Data.Matrix.KroneckerCMatrix
import Quantumlib.Tactic.Basic

open Matrix KroneckerCMatrix

@[simp]
lemma hadamardK_1 : hadamardK 1 = hadamard := by
  simp only [hadamardK, kroneckerCMatrix_one]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

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
lemma sqrtx_mul_sqrtx : sqrtx * sqrtx = σx := by
  simp [sqrtx, σx]
  ext i j
  fin_cases i <;> fin_cases j
    <;> field_simp
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
lemma xRotation_pi : xRotation π = -Complex.I • σx := by
  simp [xRotation, σx]

@[simp]
lemma yRotation_pi : yRotation π = -Complex.I • σy := by
  simp [yRotation, σy]

@[simp]
lemma rotation_hadamard : rotation (π / 2) 0 π = hadamard := by
  simp [rotation, hadamard]
  ring_nf
  rw [mul_one_div]
  ext i j
  fin_cases i <;> fin_cases j
    <;> apply Complex.ext
    <;> simp

@[simp]
lemma rotation_σx : rotation π 0 π = σx := by
  simp [rotation, σx]
  
@[simp]
lemma rotation_σy : rotation π (π / 2) (π / 2) = σy := by
  simp only [rotation, σy]
  rw [Complex.exp_mul_I]
  simp

@[simp]
lemma rotation_σz : rotation 0 0 π = σz := by
  simp [rotation, σz]

lemma rotation_xRotation : ∀ θ,
  rotation θ (3 * π / 2) (π / 2) = xRotation θ := by
  intros θ
  simp [rotation, xRotation]
  rw [Complex.exp_mul_I]
  simp
  ext i j
  fin_cases i <;> fin_cases j 
    <;> simp
  rw [add_mul, Complex.exp_add]
  simp
  rw [Complex.exp_mul_I]
  simp

lemma rotation_yRotation : ∀ θ,
  rotation θ 0 0 = yRotation θ := by
  intros
  simp [rotation, yRotation]

lemma rotation_phaseShift : ∀ θ,
  rotation 0 0 θ = phaseShift θ := by
  simp [rotation, phaseShift]

lemma rotation_1 : rotation 0 0 0 = 1 := by
  simp [rotation]
  solve_matrix

@[simp]
lemma rotation_conjTranspose : ∀ θ φ δ, (rotation θ φ δ)ᴴ = rotation (-θ) (-δ) (-φ) := by
  intros θ φ δ
  simp [rotation]
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
lemma phaseShift_0 : phaseShift 0 = 1 := by
  simp [phaseShift]
  solve_matrix

@[simp]
lemma phaseShift_π : phaseShift π = σz := by
  simp [phaseShift, σz]

@[simp]
lemma phaseShift_2π : phaseShift (2 * π) = 1 := by
  simp [phaseShift]
  solve_matrix

@[simp]
lemma phaseShift_neg_pi : phaseShift (-π) = σz := by
  simp [phaseShift, σz]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  rw [Complex.exp_neg]
  field_simp

@[simp]
lemma phaseShift_mul : ∀ θ₁ θ₂, phaseShift θ₁ * phaseShift θ₂ = phaseShift (θ₁ + θ₂) := by
  intros θ₁ θ₂
  simp [phaseShift]
  rw [←Complex.exp_add, add_mul]

@[simp]
lemma phaseShift_pow : ∀ (n : ℕ) θ, (phaseShift θ) ^ n  = phaseShift (n * θ) := by
  intros n θ
  induction n
  case zero => simp
  case succ n' ih => 
    simp [pow_succ]
    rw [add_mul, ←phaseShift_mul, ih]
    ring_nf

@[simp]
lemma sGate_mul_sGate : sGate * sGate = σz := by
  simp [sGate]

@[simp]
lemma tGate_mul_tGate : tGate * tGate = sGate := by
  simp [tGate, sGate]
  ring_nf

@[simp]
lemma σx_mul_σx : σx * σx = 1 := by
  simp only [σx]
  solve_matrix

@[simp]
lemma σy_mul_σy : σy * σy = 1 := by
  simp only [σy]
  solve_matrix

@[simp]
lemma σz_mul_σz : σz * σz = 1 := by
  simp only [σz]
  solve_matrix

@[simp]
lemma controlM_σx : controlM σx = cnot := by
  ext i j
  fin_cases i <;> fin_cases j
    <;> simp (config := { decide := true }) [cnot, controlM]
    <;> rfl

@[simp]
lemma cnot_decompose : ∣1⟩⟨1∣ ⊗ σx + ∣0⟩⟨0∣ ⊗ 1 = cnot := by
  ext i j
  rw [Matrix.add_apply]
  simp [kroneckerCMatrix, σx, cnot]
  fin_cases i <;> fin_cases j
    <;> simp [cnot, Fin.divNat, Fin.modNat]

@[simp]
lemma notc_decompose : σx ⊗ ∣1⟩⟨1∣ + 1 ⊗ ∣0⟩⟨0∣ = notc := by
  ext i j
  rw [Matrix.add_apply]
  simp [kroneckerCMatrix, σx, notc]
  fin_cases i <;> fin_cases j
    <;> simp [cnot, Fin.divNat, Fin.modNat]

@[simp]
lemma swap_mul_swap : swap * swap = 1 := by
  simp [swap]
  solve_matrix

