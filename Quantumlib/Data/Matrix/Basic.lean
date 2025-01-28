import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Kronecker
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Fin

abbrev CMatrix m n := Matrix (Fin m) (Fin n) ℂ
abbrev CVector n := CMatrix n 1
abbrev CSquare n := CMatrix n n

namespace Matrix

theorem conjTranspose_transpose_comm : ∀ (A : CMatrix m n),
  Aᴴᵀ = Aᵀᴴ := by intros; rfl

end Matrix

def CMatrix.Commute     (A B : CMatrix n n) : Prop := _root_.Commute A B
def CMatrix.AntiCommute (A B : CMatrix n n) : Prop := A * B = -1 • B * A
