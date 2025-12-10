import Quantumlib.ForMathlib.Data.Matrix.Basic
import Quantumlib.ForMathlib.Data.Matrix.Kron
import Quantumlib.ForMathlib.Data.Complex.Basic

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



