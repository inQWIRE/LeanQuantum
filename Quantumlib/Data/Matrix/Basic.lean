import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Kronecker
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Fin

abbrev CMatrix m n := Matrix (Fin m) (Fin n) ℂ
abbrev CVector n := CMatrix n 1
abbrev CSquare n := CMatrix n n

abbrev Matrix.IsUnitary {n} (M : CSquare n) := M ∈ Matrix.unitaryGroup (Fin n) ℂ

