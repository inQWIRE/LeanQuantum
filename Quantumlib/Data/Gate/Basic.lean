import Quantumlib.Data.Matrix.Basic
import Quantumlib.Data.Matrix.Kron
import Quantumlib.Data.Matrix.PowBitVec
import Quantumlib.Data.Complex.Basic

open Matrix Kron

noncomputable def hadamard : CSquare 2 :=
  √ 2⁻¹ • !![1,  1;
             1, -1]

noncomputable def hadamardK (k : ℕ) : CSquare (2 ^ k) := 
  hadamard ^ᵥ BitVec.allOnes k

noncomputable def sqrtx : CSquare 2 :=
  !![⟨1,  1⟩ / 2, ⟨1, -1⟩ / 2;
     ⟨1, -1⟩ / 2, ⟨1,  1⟩ / 2]


def controlM (M : CSquare n) : CSquare (2 * n) :=
  fun x y =>
    if x < n && x = y then
      1
    else
      if h : n ≤ x ∧ n ≤ y then
        let pf := Nat.two_mul n
        let x' := Fin.cast pf x
        let y' := Fin.cast pf y
        M (Fin.subNat n x' h.left) (Fin.subNat n y' h.right)
      else
        0

def cnot : CSquare 4 :=
  !![1, 0, 0, 0;
     0, 1, 0, 0; 
     0, 0, 0, 1;
     0, 0, 1, 0]

def notc : CSquare 4 := 
  !![1, 0, 0, 0;
     0, 0, 0, 1;
     0, 0, 1, 0;
     0, 1, 0, 0]

def swap : CSquare 4 :=
  !![1, 0, 0, 0;
     0, 0, 1, 0;
     0, 1, 0, 0;
     0, 0, 0, 1]

