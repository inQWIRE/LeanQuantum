import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Real.Basic

notation "π" => Real.pi

namespace Complex

@[simp]
theorem cos_pi_div_four : Complex.cos (π / 4) = √2 / 2 := by
    calc 
      Complex.cos (π / 4) = Real.cos (π / 4) := by rw [Complex.ofReal_cos]; simp
      _ = _ := by
        apply Complex.ext <;> simp

@[simp]
theorem sin_pi_div_four : Complex.sin (π / 4) = √2 / 2 := by
    calc 
      Complex.sin (π / 4) = Real.sin (π / 4) := by rw [Complex.ofReal_sin]; simp
      _ = _ := by
        apply Complex.ext <;> simp

@[simp]
theorem exp_three_pi_div_two : Complex.exp (3 * ↑π / 2 * Complex.I) = -Complex.I := by
  have : (3 : ℂ) = 2 + 1 := by ring_nf
  rw [show (3 : ℂ) = 2 + 1 by ring_nf, 
      add_mul, add_div, add_mul,
      exp_add]
  repeat rw [exp_mul_I]
  field_simp

@[simp]
theorem one_ne_neg_one : (1 : ℂ) ≠ -1 := by
  intros h
  rw [Complex.ext_iff] at h
  simp_all
  linarith


end Complex
