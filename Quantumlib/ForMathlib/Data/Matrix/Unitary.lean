import Quantumlib.ForMathlib.Data.Matrix.Basic
import Quantumlib.ForMathlib.Data.Matrix.Kron

open Kron

namespace Matrix

abbrev IsUnitary {n} (M : CSquare n) := M ∈ Matrix.unitaryGroup (Fin n) ℂ


end Matrix

