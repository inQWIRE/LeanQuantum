import Quantumlib.ForMathlib.Data.BitVec.Lemmas
import Quantumlib.ForMathlib.Data.Matrix.Basic
import Quantumlib.ForMathlib.Data.Matrix.Kron
import Quantumlib.Tactic.Basic

namespace CMatrix

open Kron in
def powBitVec (self : CMatrix m m) (x : BitVec n) : CMatrix (m ^ n) (m ^ n) :=
  match n with
  | 0 => 1
  | n' + 1 => 
      Matrix.reindex
        (finCongr <| by ring)
        (finCongr <| by ring) <|
          (self ^ x.msb.toNat) ⊗
          (powBitVec self x.lsbs : CMatrix (m ^ n') (m ^ n'))

infix:80 " ^ᵥ " => powBitVec


@[simp]
theorem powBitVec_zero (M : CMatrix n n) m :
  M ^ᵥ 0#m = 1 := by 
    induction m
    case zero => simp [powBitVec]
    case succ m' ih =>
      simp_rw [
        powBitVec,
        BitVec.msb_zero,
        BitVec.lsbs_zero,
        ih,
        Bool.toNat_false, pow_zero,
        Matrix.one_kron_one]
      simp

@[simp]
theorem one_powBitVec :
  (1 : CMatrix n n) ^ᵥ x = 1 := by 
    rename_i w
    induction w
    case zero => simp [powBitVec]
    case succ m' ih =>
      simp_rw [
        powBitVec,
        ih]
      cases x.msb <;> simp


@[simp]
theorem powBitVec_mul_powBitVec (A B : CMatrix n n) {m} (x : BitVec m) :
  A ^ᵥ x * B ^ᵥ x = (A * B) ^ᵥ x := by
    induction m
    case zero =>
      rw [BitVec.eq_nil x, BitVec.nil]
      simp

    case succ m' ih =>
      simp_rw [powBitVec, ←ih]
      cases x.msb
        <;> ext i j
        <;> simp [←Matrix.mul_kron_mul]

open Kron in
@[simp]
theorem powBitVec_cons (A : CMatrix n n) b (x : BitVec m) :
  A ^ᵥ (BitVec.cons b x) = 
    Matrix.reindex
      (finCongr <| by ring_nf)
      (finCongr <| by ring_nf)
        ((A ^ b.toNat) ⊗ 
         (A ^ᵥ x : CMatrix (n ^ m) (n ^ m))) := by 
      simp [powBitVec]

end CMatrix


