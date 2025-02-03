import Quantumlib.Data.BitVec.Basic

namespace BitVec

theorem cons_msb_tail (x : BitVec (w + 1)) :
  cons x.msb (tail x) = x := by simp [tail]

@[simp]
theorem tail_zero :
  (0#(m + 1)).tail = 0#m := by simp [tail]

@[simp]
theorem cons_true_allOnes :
  cons true (allOnes m) = allOnes (m + 1) := by
    ext
    simp only [getLsbD_cons, getLsbD_allOnes, Bool.if_true_left]
    rename ℕ => i
    cases h : decide (i = m) <;> simp_all
    omega

@[simp]
theorem tail_allOnes :
  (allOnes (m + 1)).tail = allOnes m := by
    ext
    simp [tail]
    omega

@[simp]
theorem weight_zero : 
  (0#m).weight = 0 := by
    simp [weight, foldr]
    induction m <;> simp_all

@[simp]
theorem weight_allOnes : 
  (allOnes m).weight = m := by
    simp [weight, foldr]
    induction m <;> simp_all [add_comm]

end BitVec
