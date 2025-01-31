import Quantumlib.Data.Complex.Basic
import Quantumlib.Data.Matrix.Basic
import Quantumlib.Data.Matrix.Kron
import Quantumlib.Data.Matrix.PowBitVec
import Quantumlib.Data.Vector.Basic

import Mathlib.Analysis.Complex.Circle

def σx : CSquare 2 :=
  !![0, 1; 
     1, 0]

def σy : CSquare 2 :=
  !![0, -Complex.I;
     Complex.I, 0]

def σz : CSquare 2 :=
  !![1,  0;
     0, -1]


structure Pauli (n : ℕ) where
  coeff : Circle := Circle.exp 0
  x : List.Vector Bool n
  z : List.Vector Bool n

namespace Pauli

def symplecticProduct {n : ℕ} (P Q : Pauli n) : Bool :=
  let dot1 := P.x &&& Q.z |>.toList.foldr xor false
  let dot2 := Q.z &&& P.x |>.toList.foldr xor false
  dot1 ≠ dot2

def weight {n : ℕ} (P : Pauli n) : ℕ :=
  P.x ||| P.z |>.toList.filter (·) |>.length

noncomputable section

def toCMatrix (P : Pauli n) : CSquare (2 ^ n) :=
  P.coeff • (σx ^ᵥ P.x * σz ^ᵥ P.z)

def smul (a : Circle) (P : Pauli n) : Pauli n :=
  {P with coeff := P.coeff * a}

instance : SMul Circle (Pauli n) := ⟨smul⟩

def mul (P Q : Pauli n) : Pauli n := {
  coeff := P.coeff * Q.coeff * (Circle.exp (π * (symplecticProduct P Q).toNat)),
  x := P.x ^^^ Q.x,
  z := P.z ^^^ Q.z
}


instance : Mul (Pauli n) := ⟨mul⟩

end

example : 
    let P : Pauli 1 := {
      x := ⟨[false], rfl⟩,
      z := ⟨[false], rfl⟩
    } 
    P * P = P := by
      sorry



theorem mul_toCMatrix_eq_toCMatrix_mul_toCMatrix (P Q : Pauli n) :
  (P * Q).toCMatrix = P.toCMatrix * Q.toCMatrix := by
    sorry


end Pauli
 
