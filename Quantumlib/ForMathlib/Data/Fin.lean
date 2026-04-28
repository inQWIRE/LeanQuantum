import Mathlib.Data.Fintype.Basic
import Init.Data.Nat.Basic

namespace Fin

@[simp]
theorem add_neg (a b : Fin n) : a + -b = a - b := by
  simp only [neg_def, add_def, Nat.add_mod_mod, sub_def, Nat.add_comm]

end Fin
