import Quantumlib.Data.Matrix.Basic
import Quantumlib.Data.Matrix.Kron
import Quantumlib.Tactic.Basic

namespace CMatrix

open Kron in
@[simp]
def powBitVec (self : CMatrix m m) (bitVec : List.Vector Bool n) : CMatrix (m ^ n) (m ^ n) :=
  match n with
  | 0 => 1
  | n' + 1 => 
      Matrix.reindex
        (finCongr <| by ring)
        (finCongr <| by ring) <|
          (self ^ bitVec.head.toNat) ⊗
          (powBitVec self bitVec.tail : CMatrix (m ^ n') (m ^ n'))

infix:80 " ^ᵥ " => powBitVec

@[simp]
theorem powBitVec_nil (M : CMatrix n n) : M ^ᵥ .nil = 1 := rfl

@[simp]
theorem powBitVec_cons (M : CMatrix n n) {m} b (bv : List.Vector Bool m) :
    M ^ᵥ (b ::ᵥ bv) = 
      (Matrix.reindex
        (finCongr <| by rw [pow_succ, mul_comm]) 
        (finCongr <| by rw [pow_succ, mul_comm]) <|
          Matrix.kron (a := n) (b := n) (M ^ b.toNat) (M ^ᵥ bv)) := rfl

@[simp]
theorem powBitVec_true (M : CMatrix n n) :
  M ^ᵥ (true ::ᵥ .nil) =
    Matrix.reindex (finCongr <| by ring) (finCongr <| by ring) M := by 
      simp [-Matrix.kron_one, Matrix.submatrix]

@[simp]
theorem powBitVec_0 (M : CMatrix n n) m :
  M ^ᵥ List.Vector.replicate m false = 1 := by 
    induction m
    case zero => simp
    case succ m' ih =>
      simp_rw [
        List.Vector.replicate_succ,
        powBitVec,
        List.Vector.head_cons, List.Vector.tail_cons,
        ih,
        Bool.toNat_false, pow_zero, Matrix.one_kron_one]
      simp

@[simp]
theorem powBitVec_false (M : CMatrix n n) :
  M ^ᵥ (false ::ᵥ .nil) = 1 := powBitVec_0 M 1

@[simp]
theorem powBitVec_mul_powBitVec (A B : CMatrix n n) {m} (bv : List.Vector Bool m) :
  A ^ᵥ bv * B ^ᵥ bv = (A * B) ^ᵥ bv := by
    induction m
    case zero => simp
    case succ m' ih =>
      obtain ⟨b, bv', h⟩ := List.Vector.exists_eq_cons bv
      subst h
      cases b
        <;> ext i j
        <;> simp_rw [
          powBitVec_cons, 
          Matrix.reindex_apply,
          Matrix.submatrix_apply,
          ←ih,
          Matrix.submatrix_mul_equiv,
          Matrix.submatrix_apply,
          ←Matrix.mul_kron_mul,
        ]
        <;> simp

end CMatrix


