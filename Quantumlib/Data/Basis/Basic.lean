import Quantumlib.Data.Matrix.Basic
import Quantumlib.Data.Matrix.Kron
import Quantumlib.Tactic.Basic

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Data.Real.Sqrt

open Matrix Kron

abbrev ket0 : CVector 2 :=
  ![1, 0]

abbrev ket1 : CVector 2 :=
  ![0, 1]

abbrev bra0 : CMatrix 1 2 :=
  ket0ᴴ

abbrev bra1 : CMatrix 1 2 :=
  ket1ᴴ


noncomputable section

def xbasisPlus : CVector 2 :=
  (√ 2⁻¹ : ℂ) • (ket0 + ket1) 

def xbasisMinus : CVector 2 :=
  (√ 2⁻¹ : ℂ) • (ket0 - ket1) 

def ybasisPlus : CVector 2 :=
  (√ 2⁻¹ : ℂ) • (ket0 + Complex.I • ket1)

def ybasisMinus : CVector 2 :=
  (√ 2⁻¹ : ℂ) • (ket0 + Complex.I • ket1)

def EPRpair : CVector 4 :=
  (√ 2⁻¹ : ℂ) • (ket0 ⊗ ket0 + ket1 ⊗ ket1)

end section

lemma ket_decompose : ∀ (q : CVector 2), 
  q = (q 0 0) • ket0 + (q 1 0) • ket1 := by
  intros
  solve_matrix
