import Quantumlib.ForMathlib.Data.Matrix.Basic

import Mathlib.LinearAlgebra.Matrix.Kronecker

namespace Matrix

def kron (m₁ : CMatrix a b) (m₂ : CMatrix c d) : CMatrix (a * c) (b * d) :=
  of fun x y => m₁ x.divNat y.divNat * m₂ x.modNat y.modNat

open Kronecker in
lemma kron_def (m₁ : CMatrix a b) (m₂ : CMatrix c d) :
  kron m₁ m₂ = reindex finProdFinEquiv finProdFinEquiv (m₁ ⊗ₖ m₂) := by
  rfl

scoped[Kron] infixl:100 " ⊗ " => Matrix.kron

open Kron

@[simp]
theorem kron_apply (A : CMatrix l m) (B : CMatrix n p) (i j) :
    (A ⊗ B) i j = A i.divNat j.divNat * B i.modNat j.modNat :=
  rfl

@[simp]
theorem zero_kron (B : CMatrix n p) : (0 : CMatrix l m) ⊗ B = 0 := by
  simp [kron]
  rfl

@[simp]
theorem kron_zero (A : CMatrix l m) : A ⊗ (0 : CMatrix n p) = 0 := by
  simp [kron]
  rfl

@[simp]
theorem add_kron (A₁ A₂ : CMatrix l m) (B : CMatrix n p) :
    (A₁ + A₂) ⊗ B = A₁ ⊗ B + A₂ ⊗ B := by
  rw [kron_def, add_kronecker]
  rfl

@[simp]
theorem kron_add (A : CMatrix l m) (B₁ B₂ : CMatrix n p) :
    A ⊗ (B₁ + B₂) = A ⊗ B₁ + A ⊗ B₂ := by
  rw [kron_def, kronecker_add]
  rfl

@[simp]
theorem smul_kron (r : ℂ)
    (A : CMatrix l m) (B : CMatrix n p) : (r • A) ⊗ B = r • A ⊗ B := by
  rw [kron_def, smul_kronecker]
  rfl

@[simp]
theorem kron_smul (r : ℂ)
    (A : CMatrix l m) (B : CMatrix n p) : A ⊗ (r • B) = r • A ⊗ B := by
  rw [kron_def, kronecker_smul]
  rfl

@[simp]
theorem kron_neg
  (A : CMatrix l m) (B : CMatrix n p) : A ⊗ (-B) = -(A ⊗ B) := by
    rw [←neg_one_smul ℂ, kron_smul, neg_one_smul]

@[simp]
theorem neg_kron
  (A : CMatrix l m) (B : CMatrix n p) : (-A) ⊗ B = -(A ⊗ B) := by
    rw [←neg_one_smul ℂ, smul_kron, neg_one_smul]


@[simp]
theorem one_kron_one :
    (1 : CMatrix m m) ⊗ (1 : CMatrix n n) = 1 := by
  rw [kron_def, one_kronecker_one]
  simp

@[simp]
theorem kron_one' :
    A ⊗ (1 : CMatrix 1 1) = reindex (finCongr <| Nat.mul_one ..).symm (finCongr <| Nat.mul_one ..).symm A := by
  simp [kron_def]
  ext i j
  simp
  generalize h : (1 : CMatrix 1 1) (i.divNat, i.modNat).2 (j.divNat, j.modNat).2 = lhs
  have : lhs = 1 := by
    rw [←h,
        show (i.divNat, i.modNat).2 = i.modNat by rfl,
        show (j.divNat, j.modNat).2 = j.modNat by rfl,
    ]
    generalize hi : i.modNat = iModNat
    generalize hj : j.modNat = jModNat
    fin_cases iModNat; fin_cases jModNat
    rfl
  rw [this, mul_one]
  clear h lhs this
  simp only [Fin.divNat, Nat.div_one]
  rfl

theorem kron_one :
    A ⊗ (1 : CMatrix n n) = reindex finProdFinEquiv finProdFinEquiv (blockDiagonal fun _ => A) := by
  rw [kron_def, kronecker_one]

@[simp]
theorem one'_kron :
    (1 : CMatrix 1 1) ⊗ (A : CMatrix m n) = reindex (finCongr <| Nat.one_mul ..).symm (finCongr <| Nat.one_mul ..).symm A := by
  simp [kron_def]
  ext i j
  simp
  generalize h : (1 : CMatrix 1 1) (i.divNat, i.modNat).1 (j.divNat, j.modNat).1 = lhs
  have : lhs = 1 := by
    rw [←h,
        show (i.divNat, i.modNat).1 = i.divNat by rfl,
        show (j.divNat, j.modNat).1 = j.divNat by rfl,
    ]
    generalize hi : i.divNat = iDivNat
    generalize hj : j.divNat = jDivNat
    fin_cases iDivNat; fin_cases jDivNat
    rfl
  rw [this, one_mul]
  clear h lhs this
  congr <;> simp [Fin.modNat]
  · have : ↑i < m := by omega
    conv in ↑i % m =>
      rw [Nat.mod_eq_of_lt this]
      rfl
    simp [Fin.cast]
  · have : ↑j < n := by omega
    conv in ↑j % n =>
      rw [Nat.mod_eq_of_lt this]
      rfl
    simp [Fin.cast]


theorem one_kron (B : CMatrix m n) :
    (1 : CMatrix l l) ⊗ B =
      reindex ((Equiv.prodComm ..).trans finProdFinEquiv) ((Equiv.prodComm ..).trans finProdFinEquiv)
        (blockDiagonal fun _ => B) := by
  rw [kron_def, one_kronecker]
  rfl
  

theorem mul_kron_mul (A : CMatrix l m)
    (B : CMatrix m n) (A' : CMatrix l' m') (B' : CMatrix m' n') :
    (A * B) ⊗ (A' * B') = A ⊗ A' * B ⊗ B' := by
  simp_rw [kron_def, mul_kronecker_mul]
  simp

theorem kron_assoc (A : CMatrix l m) (B : CMatrix n p) (C : CMatrix q r) :
    reindex (finCongr <| Nat.mul_assoc ..) (finCongr <| Nat.mul_assoc ..) (A ⊗ B ⊗ C) =
    A ⊗ (B ⊗ C) := by
  ext i j
  simp [kron]
  rw [mul_assoc]
  congr 2 <;> simp [Fin.divNat, Fin.modNat]
  · rw [Nat.div_div_eq_div_mul, Nat.mul_comm q n]
  · rw [Nat.div_div_eq_div_mul, Nat.mul_comm r p]
  · congr <;> rw [Nat.mod_mul_left_div_self]

theorem trace_kron (A : CMatrix m m) (B : CMatrix n n) :
    trace (A ⊗ B) = trace A * trace B := by
  simp_rw [trace, Finset.sum_mul_sum,
           ←Equiv.sum_comp (e := finProdFinEquiv),
           ←Finset.univ_product_univ, Finset.sum_product]
  simp [kron_def]
  

theorem det_kron (A : CMatrix m m) (B : CMatrix n n) :
    det (A ⊗ B) = det A ^ n * det B ^ m := by
  rw [kron_def]
  simp [det_kronecker]


theorem inv_kron
    (A : CMatrix m m) (B : CMatrix n n) : (A ⊗ B)⁻¹ = A⁻¹ ⊗ B⁻¹ := by
  simp_rw [kron_def]
  simp [inv_kronecker]

@[simp]
theorem transpose_kron : ∀ (A : CMatrix l m) (B : CMatrix n p),
  (A ⊗ B)ᵀ = Aᵀ ⊗ Bᵀ := by
    intros
    simp [kron, transpose]

@[simp]
theorem conjTranspose_kron : ∀ (A : CMatrix l m) (B : CMatrix n p),
  (A ⊗ B)ᴴ = Aᴴ ⊗ Bᴴ := by
    intros
    simp [conjTranspose, transpose, kron, Matrix.map]

end Matrix
