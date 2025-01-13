import Quantumlib.Data.Matrix.Basic
import Quantumlib.Data.Matrix.KroneckerCMatrix
import Quantumlib.Data.Complex.Basic
import Quantumlib.Notation

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.UnitaryGroup

open Matrix KroneckerCMatrix

lemma ket_decompose : ∀ (q : CVector 2), 
  q = (q 0 0) • ∣0⟩ + (q 1 0) • ∣1⟩ := by
  intros
  ext i j
  fin_cases i <;> fin_cases j <;> simp


noncomputable def xbasisPlus : CVector 2 :=
  √ 2⁻¹ • (∣0⟩ + ∣1⟩) 

noncomputable def xbasisMinus : CVector 2 :=
  √ 2⁻¹ • (∣0⟩ - ∣1⟩) 

noncomputable def ybasisPlus : CVector 2 :=
  √ 2⁻¹ • (∣0⟩ + Complex.I • ∣1⟩)

noncomputable def ybasisMinus : CVector 2 :=
  √ 2⁻¹ • (∣0⟩ + Complex.I • ∣1⟩)

notation "∣+⟩" => xbasisPlus
notation "∣-⟩" => xbasisMinus
notation "∣R⟩" => ybasisPlus
notation "∣L⟩" => ybasisMinus

noncomputable def EPRpair : CVector 4 :=
  √ 2⁻¹ • (∣00⟩ + ∣11⟩)

notation "∣Φ+⟩" => EPRpair

noncomputable def hadamard : CSquare 2 :=
  √ 2⁻¹ • !![1,  1;
             1, -1]

noncomputable def hadamardK (k : ℕ) : CSquare (2 ^ k) := 
  match k with
  | 0 => 1
  | .succ k' => by 
    rw [Nat.pow_succ, Nat.mul_comm]
    exact hadamard ⊗ hadamardK k'

@[simp]
lemma hadamard_1 : hadamardK 1 = hadamard := by
  simp only [hadamardK, kroneckerCMatrix_one]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

def σx : CSquare 2 :=
  !![0, 1; 
     1, 0]

def σy : CSquare 2 :=
  !![0, -Complex.I;
     Complex.I, 0]

def σz : CSquare 2 :=
  !![1,  0;
     0, -1]

noncomputable def sqrtx : CSquare 2 :=
  !![⟨1,  1⟩ / 2, ⟨1, -1⟩ / 2;
     ⟨1, -1⟩ / 2, ⟨1,  1⟩ / 2]


@[simp]
lemma sqrtx_mul_sqrtx : sqrtx * sqrtx = σx := by
  simp [sqrtx, σx]
  ext i j
  fin_cases i <;> fin_cases j
    <;> field_simp
    <;> apply Complex.ext <;> simp
    <;> ring_nf

def controlM (M : CMatrix n n) : CSquare (2 * n) :=
  fun x y =>
    let x' : Fin (n + n) := Fin.cast (by apply Nat.two_mul) x
    let y' : Fin (n + n) := Fin.cast (by apply Nat.two_mul) y
    if x' < n && y' = x' then 1 else
    if h : n <= x' && n <= y' then by
      simp at h
      exact M (Fin.subNat n x' h.left) (Fin.subNat n y' h.right)
    else 0

def cnot : CMatrix 4 4 :=
  !![1, 0, 0, 0;
     0, 1, 0, 0; 
     0, 0, 0, 1;
     0, 0, 1, 0]

@[simp]
lemma controlM_σx : controlM σx = cnot := by
  ext i j
  fin_cases i <;> fin_cases j
    <;> simp (config := { decide := true }) [cnot, controlM]
    <;> rfl

def notc : CSquare 4 := 
  !![1, 0, 0, 0;
     0, 0, 0, 1;
     0, 0, 1, 0;
     0, 1, 0, 0]

def swap : CSquare 4 :=
  !![1, 0, 0, 0;
     0, 0, 1, 0;
     0, 1, 0, 0;
     0, 0, 0, 1]

noncomputable section 

open Complex (exp I)
open Real (cos sin)

def rotation (θ φ δ : ℝ) : CSquare 2 :=
  !![              cos (θ / 2), -exp (δ * I)       * sin (θ / 2);
     exp (φ * I) * sin (θ / 2),  exp ((φ + δ) * I) * cos (θ / 2)]

def phaseShift (φ : ℝ) : CSquare 2 :=
  !![1, 0          ;
     0, exp (φ * I)]

def xRotation (θ : ℝ) : CSquare 2 :=
  !![     cos (θ / 2), -I * sin (θ / 2); 
     -I * sin (θ / 2),      cos (θ / 2)]

def yRotation (θ : ℝ) : CSquare 2 :=
  !![cos (θ / 2), -sin (θ / 2);
     sin (θ / 2),  cos (θ / 2)]

def sGate : CSquare 2 :=
  phaseShift (π / 2)

def tGate : CSquare 2 :=
  phaseShift (π / 4)

end section

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
  ext i j
  fin_cases i <;> fin_cases j <;> rfl


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

@[simp]
lemma σx_mul_σx : σx * σx = 1 := by
  simp only [σx]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

@[simp]
lemma σy_mul_σy : σy * σy = 1 := by
  simp only [σy]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

@[simp]
lemma σz_mul_σz : σz * σz = 1 := by
  simp only [σz]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

@[simp]
lemma hadamard_mul_hadamard : hadamard * hadamard = 1 := by
  simp only [hadamard]
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
lemma cnot_decompose : ∣1⟩⟨1∣ ⊗ σx + ∣0⟩⟨0∣ ⊗ 1 = cnot := by
  ext i j
  rw [Matrix.add_apply]
  simp [kroneckerCMatrix, σx, cnot]
  fin_cases i <;> fin_cases j
    <;> simp [cnot, Fin.divNat, Fin.modNat]


lemma notc_decompose : σx ⊗ ∣1⟩⟨1∣ + 1 ⊗ ∣0⟩⟨0∣ = notc := by
  ext i j
  rw [Matrix.add_apply]
  simp [kroneckerCMatrix, σx, notc]
  fin_cases i <;> fin_cases j
    <;> simp [cnot, Fin.divNat, Fin.modNat]


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
lemma swap_mul_swap : swap * swap = 1 := by
  simp [swap]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

lemma hadamard_unitary : hadamard.IsUnitary := by 
  simp_rw [mem_unitaryGroup_iff']
  simp [star, hadamard]
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j
    <;> apply Complex.ext
    <;> simp
    <;> field_simp

lemma σx_unitary : σx.IsUnitary := by
  simp_rw [mem_unitaryGroup_iff']
  simp [star, σx]
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;> simp

lemma σy_unitary : σy.IsUnitary := by
  simp_rw [mem_unitaryGroup_iff']
  simp [star, σy]
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;> simp

lemma σz_unitary : σz.IsUnitary := by
  simp_rw [mem_unitaryGroup_iff']
  simp [star, σz]
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;> simp

lemma phase_unitary : ∀ φ, (phaseShift φ).IsUnitary := by
  intros
  simp_rw [mem_unitaryGroup_iff']
  simp [star, phaseShift]
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;> simp
  rw [←Complex.exp_conj, ←Complex.exp_add]
  simp

lemma sGate_unitary : sGate.IsUnitary := by 
  apply phase_unitary

lemma tGate_unitary : tGate.IsUnitary := by 
  apply phase_unitary

@[simp]
lemma rotation_conjTranspose : ∀ θ φ δ, (rotation θ φ δ)ᴴ = rotation (-θ) (-δ) (-φ) := by
  intros θ φ δ
  simp [rotation]
  ext i j
  rw [Matrix.conjTranspose_apply]
  fin_cases i <;> fin_cases j
    <;> simp [←Complex.exp_conj, ←Complex.cos_conj, ←Complex.sin_conj]
    <;> field_simp [OfNat.ofNat]
    <;> field_simp
    <;> ring_nf


lemma rotation_unitary : ∀ θ φ δ, (rotation θ φ δ).IsUnitary := by
  intros θ φ δ
  simp_rw [mem_unitaryGroup_iff', star, rotation_conjTranspose]
  simp only [rotation]
  repeat rw [Complex.exp_mul_I]
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j
    <;> apply Complex.ext
    <;> simp
    <;> ring_nf



lemma swap_spec : ∀ (q₁ q₂ : CVector 2), swap * (q₁ ⊗ q₂) = q₂ ⊗ q₁ := by
  intros
  simp [swap, vecHead, vecTail, Fin.modNat, Fin.divNat]
  ext i
  fin_cases i <;> simp <;> ring_nf!

