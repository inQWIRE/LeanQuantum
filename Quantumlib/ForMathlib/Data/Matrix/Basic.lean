import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Fin.Basic

abbrev CMatrix m n := Matrix (Fin m) (Fin n) ℂ
abbrev CVector n := CMatrix n 1
abbrev CSquare n := CMatrix n n

namespace Matrix

end Matrix

def CMatrix.AntiCommute (A B : CMatrix n n) : Prop := A * B = -(B * A)
