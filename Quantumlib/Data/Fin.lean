import Mathlib

namespace Fin

@[simp]
theorem add_neg (a b : Fin n) : a + -b = a - b := by
  simp only [neg_def, add_def, Nat.add_mod_mod, sub_def, add_comm]

end Fin
