import Quantumlib.Data.Matrix.Basic
import Quantumlib.Data.Matrix.KroneckerCMatrix
import Quantumlib.Data.Complex.Basic

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

noncomputable section 

open Complex (exp I)
open Real (cos sin)

def rotation (θ φ δ : ℝ) : CSquare 2 :=
  !![              cos (θ / 2), -exp (δ * I)       * sin (θ / 2);
     exp (φ * I) * sin (θ / 2),  exp ((φ + δ) * I) * cos (θ / 2)]

def phaseShift (φ : ℝ) : CSquare 2 :=
  !![1, 0          ;
     0, exp (φ * I)]

def xRotation (θ : ℝ) : CSquare 2 :=
  !![     cos (θ / 2), -I * sin (θ / 2); 
     -I * sin (θ / 2),      cos (θ / 2)]

def yRotation (θ : ℝ) : CSquare 2 :=
  !![cos (θ / 2), -sin (θ / 2);
     sin (θ / 2),  cos (θ / 2)]

def sGate : CSquare 2 :=
  phaseShift (π / 2)

def tGate : CSquare 2 :=
  phaseShift (π / 4)

end section
