import Quantumlib.Data.Matrix.Basic

import Mathlib.Data.Matrix.Kronecker

namespace Matrix

def kroneckerCMatrix (m₁ : CMatrix a b) (m₂ : CMatrix c d) : CMatrix (a * c) (b * d) :=
  of fun x y => m₁ x.divNat y.divNat * m₂ x.modNat y.modNat

open Kronecker in
lemma kroneckerCMatrix_def (m₁ : CMatrix a b) (m₂ : CMatrix c d) :
  kroneckerCMatrix m₁ m₂ = reindex finProdFinEquiv finProdFinEquiv (m₁ ⊗ₖ m₂) := by
  rfl

scoped[KroneckerCMatrix] infixl:100 " ⊗ " => Matrix.kroneckerCMatrix

open KroneckerCMatrix

@[simp]
theorem zero_kroneckerCMatrix (B : CMatrix n p) : (0 : CMatrix l m) ⊗ B = 0 := by
  simp [kroneckerCMatrix]
  rfl

@[simp]
theorem kroneckerCMatrix_zero (A : CMatrix l m) : A ⊗ (0 : CMatrix n p) = 0 := by
  simp [kroneckerCMatrix]
  rfl

@[simp]
theorem add_kroneckerCMatrix (A₁ A₂ : CMatrix l m) (B : CMatrix n p) :
    (A₁ + A₂) ⊗ B = A₁ ⊗ B + A₂ ⊗ B := by
  rw [kroneckerCMatrix_def, add_kronecker]
  rfl

@[simp]
theorem kroneckerCMatrix_add (A : CMatrix l m) (B₁ B₂ : CMatrix n p) :
    A ⊗ (B₁ + B₂) = A ⊗ B₁ + A ⊗ B₂ := by
  rw [kroneckerCMatrix_def, kronecker_add]
  rfl

@[simp]
theorem smul_kroneckerCMatrix (r : ℂ)
    (A : CMatrix l m) (B : CMatrix n p) : (r • A) ⊗ B = r • A ⊗ B := by
  rw [kroneckerCMatrix_def, smul_kronecker]
  rfl

@[simp]
theorem kroneckerCMatrix_smul (r : ℂ)
    (A : CMatrix l m) (B : CMatrix n p) : A ⊗ (r • B) = r • A ⊗ B := by
  rw [kroneckerCMatrix_def, kronecker_smul]
  rfl

@[simp]
theorem one_kroneckerCMatrix_one :
    (1 : CMatrix m m) ⊗ (1 : CMatrix n n) = 1 := by
  rw [kroneckerCMatrix_def, one_kronecker_one]
  simp

@[simp]
theorem kroneckerCMatrix_one :
    A ⊗ (1 : CMatrix n n) = reindex finProdFinEquiv finProdFinEquiv (blockDiagonal fun _ => A) := by
  rw [kroneckerCMatrix_def, kronecker_one]

@[simp]
theorem one_kroneckerCMatrix (B : CMatrix m n) :
    (1 : CMatrix l l) ⊗ B =
      reindex
        ((Equiv.prodComm _ _).trans finProdFinEquiv)
        ((Equiv.prodComm _ _).trans finProdFinEquiv)
        (blockDiagonal fun _ => B) := by
  rw [kroneckerCMatrix_def, one_kronecker]
  rfl
  

@[simp]
theorem mul_kroneckerCMatrix_mul (A : CMatrix l m)
    (B : CMatrix m n) (A' : CMatrix l' m') (B' : CMatrix m' n') :
    (A * B) ⊗ (A' * B') = A ⊗ A' * B ⊗ B' := by
  simp_rw [kroneckerCMatrix_def, mul_kronecker_mul]
  simp

theorem kroneckerCMatrix_assoc (A : CMatrix l m) (B : CMatrix n p) (C : CMatrix q r) :
    reindex (finCongr <| Nat.mul_assoc _ _ _) (finCongr <| Nat.mul_assoc _ _ _) (A ⊗ B ⊗ C) =
    A ⊗ (B ⊗ C) := by
  ext i j
  simp [kroneckerCMatrix]
  rw [mul_assoc]
  congr 2 <;> simp [Fin.divNat, Fin.modNat]
  · rw [Nat.div_div_eq_div_mul, Nat.mul_comm q n]
  · rw [Nat.div_div_eq_div_mul, Nat.mul_comm r p]
  · congr <;> rw [Nat.mod_mul_left_div_self]

theorem trace_kroneckerCMatrix (A : CMatrix m m) (B : CMatrix n n) :
    trace (A ⊗ B) = trace A * trace B := by
  simp_rw [trace, Finset.sum_mul_sum, ←Equiv.sum_comp (e := finProdFinEquiv), ←Finset.univ_product_univ, Finset.sum_product]
  simp [kroneckerCMatrix_def]
  


 theorem det_kroneckerCMatrix (A : CMatrix m m) (B : CMatrix n n) :
    det (A ⊗ B) = det A ^ Fintype.card (Fin n) * det B ^ Fintype.card (Fin m) := by
  rw [kroneckerCMatrix_def]
  simp [det_kronecker]


theorem inv_kroneckerCMatrix
    (A : CMatrix m m) (B : CMatrix n n) : (A ⊗ B)⁻¹ = A⁻¹ ⊗ B⁻¹ := by
  simp_rw [kroneckerCMatrix_def]
  simp [inv_kronecker]

@[simp]
theorem transpose_kroneckerCMatrix : ∀ (A : CMatrix l m) (B : CMatrix n p),
  (A ⊗ B)ᵀ = Aᵀ ⊗ Bᵀ := by
    intros
    simp [kroneckerCMatrix, transpose]

@[simp]
theorem conjTranspose_kroneckerCMatrix : ∀ (A : CMatrix l m) (B : CMatrix n p),
  (A ⊗ B)ᴴ = Aᴴ ⊗ Bᴴ := by
    intros
    simp [conjTranspose, transpose, kroneckerCMatrix, Matrix.map]

end Matrix
