import Quantumlib.Data.Matrix.Basic
import Quantumlib.Data.Matrix.KroneckerCMatrix
import Quantumlib.Data.Complex.Basic

noncomputable section

open Complex in
def phaseShift (φ : ℝ) : CSquare 2 :=
  !![1, 0          ;
     0, exp (φ * I)]

def sGate : CSquare 2 :=
  phaseShift (π / 2)

def tGate : CSquare 2 :=
  phaseShift (π / 4)

end section



