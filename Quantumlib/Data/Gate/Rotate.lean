import Quantumlib.Data.Matrix.Basic
import Quantumlib.Data.Matrix.KroneckerCMatrix
import Quantumlib.Data.Complex.Basic

noncomputable section 

open Complex (exp I)
open Real (cos sin)

def rotate (θ φ δ : ℝ) : CSquare 2 :=
  !![              cos (θ / 2), -exp (δ * I)       * sin (θ / 2);
     exp (φ * I) * sin (θ / 2),  exp ((φ + δ) * I) * cos (θ / 2)]

def xRotate (θ : ℝ) : CSquare 2 :=
  !![     cos (θ / 2), -I * sin (θ / 2); 
     -I * sin (θ / 2),      cos (θ / 2)]

def yRotate (θ : ℝ) : CSquare 2 :=
  !![cos (θ / 2), -sin (θ / 2);
     sin (θ / 2),  cos (θ / 2)]

end section
