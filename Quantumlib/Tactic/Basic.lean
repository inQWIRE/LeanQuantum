import Mathlib.Tactic.FinCases

syntax (name := SolveMatrix) "solve_matrix" : tactic

macro_rules
  | `(tactic| solve_matrix) => `(tactic| ext i j; fin_cases i <;> fin_cases j <;> simp <;> done)
