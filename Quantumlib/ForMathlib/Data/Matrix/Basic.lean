import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Fin.Basic

-- Matrices over Fins
abbrev FMatrix m n := Matrix (Fin m) (Fin n)
abbrev FVector n := FMatrix n 1
abbrev FSquare n := FMatrix n n

-- Complex-valued Matrices over Fins
abbrev CMatrix m n := FMatrix m n ℂ
abbrev CVector n := CMatrix n 1
abbrev CSquare n := CMatrix n n

namespace Matrix

theorem conjTranspose_transpose_comm : ∀ (A : CMatrix m n),
  Aᴴᵀ = Aᵀᴴ := by intros; rfl

theorem pow_true [Fintype n] [DecidableEq n] [CommRing R] (M : Matrix n n R) :
    M ^ true.toNat = M := by simp

theorem pow_false [Fintype n] [DecidableEq n] [CommRing R] (M : Matrix n n R) :
    M ^ false.toNat = 1 := by simp

end Matrix

-- Can I say A * B = B * A (or reference some typeclass) for the first one?
-- Made maximally general (useful is another story)
def FMatrix.Commute     [Mul α] [AddCommMonoid α] (A B : FMatrix n n α) : Prop := _root_.Commute A B
def FMatrix.AntiCommute [Mul α] [AddCommMonoid α] [Neg α] (A B : FMatrix n n α) : Prop := A * B = -(B * A)
