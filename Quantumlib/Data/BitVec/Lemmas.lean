import Quantumlib.Data.BitVec.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace BitVec

theorem cons_msb_lsbs (x : BitVec (w + 1)) :
  cons x.msb (lsbs x) = x := by simp [lsbs]

@[simp]
theorem lsbs_zero :
  (0#(m + 1)).lsbs = 0#m := by simp [lsbs]

@[simp]
theorem lsbs_cons (x : BitVec w) b :
  (BitVec.cons b x).lsbs = x := by simp [lsbs]

@[simp]
theorem lsbs_xor (x y : BitVec (w + 1)) :
  (x ^^^ y).lsbs = x.lsbs ^^^ y.lsbs := by
    simp [lsbs]

@[simp]
theorem lsbs_or (x y : BitVec (w + 1)) :
  (x ||| y).lsbs = x.lsbs ||| y.lsbs := by
    simp [lsbs]

@[simp]
theorem lsbs_and (x y : BitVec (w + 1)) :
  (x &&& y).lsbs = x.lsbs &&& y.lsbs := by
    simp [lsbs]

@[simp]
theorem cons_true_allOnes :
  cons true (allOnes m) = allOnes (m + 1) := by
    ext
    simp only [getLsbD_cons, getLsbD_allOnes, Bool.if_true_left]
    rename ℕ => i
    cases h : decide (i = m) <;> simp_all
    omega

@[simp]
theorem lsbs_allOnes :
  (allOnes (m + 1)).lsbs = allOnes m := by
    ext
    simp [lsbs]
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

@[simp]
theorem weight_cons_true (x : BitVec w) : (BitVec.cons true x).weight = x.weight + 1 := by
  simp only [weight, foldr, Nat.fold_succ]
  conv =>
    lhs; lhs
    rw [getElem_cons]
    simp
    rfl
  rw [add_comm]
  congr
  ext i h acc
  rw [getElem_cons, if_neg (by omega)]
  rfl

@[simp]
theorem weight_cons_false (x : BitVec w) : (BitVec.cons false x).weight = x.weight := by
  simp only [weight, foldr, Nat.fold_succ]
  conv =>
    lhs; lhs
    rw [getElem_cons]
    simp
    rfl
  rw [zero_add]
  congr
  ext i h acc
  rw [getElem_cons, if_neg (by omega)]
  rfl

theorem weight_and_le (x y : BitVec w) :
  (x &&& y).weight ≤ x.weight := by
    induction w
    case zero =>
      simp [@BitVec.of_length_zero x, @BitVec.of_length_zero y]
    case succ wi' ih =>
      rw [←cons_msb_lsbs x, ←cons_msb_lsbs y] 
      simp only [cons_xor_cons, cons_and_cons]
      cases x.msb <;> cases y.msb
        <;> simp [ih, Nat.le_step]


theorem getElem_eq_msb (x : BitVec (w + 1)) : x[w] = x.msb := by
  simp [BitVec.msb, ←getLsbD_eq_getElem, BitVec.getLsbD_eq_getMsbD]

end BitVec
