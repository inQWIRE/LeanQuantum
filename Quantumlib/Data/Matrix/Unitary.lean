import Quantumlib.Data.Matrix.Basic

namespace Matrix

abbrev IsUnitary {n} (M : CSquare n) := M ∈ Matrix.unitaryGroup (Fin n) ℂ

end Matrix

