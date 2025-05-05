import Quantumlib.Data.BitVec.Basic

import Mathlib.Data.BitVec
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace BitVec

instance : Fintype (BitVec w) :=
  Fintype.ofEquiv (Fin (2 ^ w)) equivFin.toEquiv.symm

theorem cons_msb_lsbs (x : BitVec (w + 1)) :
  cons x.msb x.lsbs = x := by simp [lsbs]

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

theorem getElem_eq_msb (x : BitVec (w + 1)) : x[w] = x.msb := by
  simp [BitVec.msb, ←getLsbD_eq_getElem, BitVec.getLsbD_eq_getMsbD]

@[simp]
theorem cons_true_allOnes :
  cons true (allOnes m) = allOnes (m + 1) := by
    ext
    simp [getElem_cons, getElem_allOnes, Bool.if_true_left]

@[simp]
theorem foldr_nil : foldr nil f a = a := by
  simp [foldr]

@[simp]
theorem foldr_cons {x : BitVec w} : foldr (cons b x) f a = f b (foldr x f a) := by
  simp only [foldr, getElem_cons, Nat.fold_succ, ↓reduceDIte]
  congr
  ext
  rw [dif_neg (by omega)]

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
theorem weight_cons (x : BitVec w) : (BitVec.cons a x).weight = a.toNat + x.weight := by
  simp [weight]

@[simp]
theorem weight_and_self (x : BitVec w) :
  (x &&& x).weight = x.weight := by
  simp [weight]

theorem weight_and_le (x y : BitVec w) :
  (x &&& y).weight ≤ x.weight := by
    induction w
    case zero =>
      simp [@BitVec.of_length_zero x, @BitVec.of_length_zero y]
    case succ w' ih =>
      rw [←cons_msb_lsbs x, ←cons_msb_lsbs y] 
      simp only [cons_xor_cons, cons_and_cons]
      cases x.msb <;> cases y.msb
        <;> simp [ih, Nat.le_step, add_comm]

theorem weight_or (x y : BitVec w) :
  (x ||| y).weight = x.weight + y.weight - (x &&& y).weight := by
    induction w
    case zero =>
      simp [@BitVec.of_length_zero x, @BitVec.of_length_zero y]
    case succ w' ih =>
      rw [←cons_msb_lsbs x, ←cons_msb_lsbs y] 
      simp only [cons_and_cons, cons_or_cons, weight_cons, ih]
      cases x.msb <;> cases y.msb
        <;> simp only [
          Bool.or_self, Bool.or_false, Bool.or_true,
          Bool.and_self, Bool.and_false, Bool.and_true,
          Bool.toNat_false, Bool.toNat_true, ←
          Nat.add_sub_assoc (Nat.le_add_right_of_le (weight_and_le ..))]
        <;> ring_nf
      rw [Nat.sub_add_eq, add_comm 2, add_assoc _ 2, add_comm 2, ←add_assoc]
      symm
      calc
        _ = (x.lsbs.weight + y.lsbs.weight + 1) - (x.lsbs &&& y.lsbs).weight := by
          rw [add_assoc, Nat.add_sub_assoc, Nat.add_sub_assoc (k := 1) (by omega)]
          ring_nf
          rw [add_comm]
          exact Nat.le_add_right_of_le (by omega)
        _ = _ := by ring_nf

theorem and_xor_distrib_left (x y z : BitVec w) :
  x &&& (y ^^^ z) = x &&& y ^^^ x &&& z := by
    ext
    simp [Bool.and_xor_distrib_left]

theorem and_xor_distrib_right (x y z : BitVec w) :
  (x ^^^ y) &&& z = x &&& z ^^^ y &&& z := by
    ext
    simp [Bool.and_xor_distrib_right]

theorem dot_comm (x y : BitVec w) : x.dot y = y.dot x := by 
  simp [dot, and_comm]

theorem cons_dot_cons (x y : BitVec w) :
  (cons a x).dot (cons b y) = ((a && b).toNat + x.dot y) := by
    simp [dot, foldr_cons]

@[simp]
theorem zero_dot : (0#m).dot x = 0 := by
  simp [dot]

@[simp]
theorem dot_zero : (x : BitVec m).dot (0#m) = 0 := by
  simp [dot]

@[simp]
theorem dot_allOnes : (x : BitVec m).dot (allOnes m) = x.weight := by 
  simp [dot]

end BitVec
