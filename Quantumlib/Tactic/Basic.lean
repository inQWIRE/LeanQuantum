import Quantumlib.Data.Matrix.Kron

import Mathlib.Tactic.FinCases
import Mathlib.Data.Matrix.Basic

import Lean.Parser.Tactic

syntax (name := solveMatrix) "solve_matrix" (" [" (Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic

macro_rules
  | `(tactic| solve_matrix) => `(tactic| solve_matrix [])
  | `(tactic| solve_matrix [$idents,*]) => `(tactic|
      ext i j;
      simp [
        Matrix.mul_apply,
        Matrix.kron_apply,
        Matrix.blockDiagonal,
        finProdFinEquiv,
        Fin.divNat,
        Fin.modNat,
        $idents,*];
      first | fin_cases i <;> fin_cases j <;> simp! <;> done
            | done
    )
