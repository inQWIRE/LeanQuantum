import Quantumlib.Data.Matrix.Basic
import Quantumlib.Data.Matrix.KroneckerCMatrix
import Quantumlib.Data.Complex.Basic

open Matrix KroneckerCMatrix

noncomputable def hadamard : CSquare 2 :=
  √ 2⁻¹ • !![1,  1;
             1, -1]

noncomputable def hadamardK (k : ℕ) : CSquare (2 ^ k) := 
  match k with
  | 0 => 1
  | .succ k' => by 
    rw [Nat.pow_succ, Nat.mul_comm]
    exact hadamard ⊗ hadamardK k'

noncomputable def sqrtx : CSquare 2 :=
  !![⟨1,  1⟩ / 2, ⟨1, -1⟩ / 2;
     ⟨1, -1⟩ / 2, ⟨1,  1⟩ / 2]


def controlM (M : CSquare n) : CSquare (2 * n) :=
  fun x y =>
    let x' : Fin (n + n) := Fin.cast (Nat.two_mul _) x
    let y' : Fin (n + n) := Fin.cast (Nat.two_mul _) y
    if x' < n && x' = y' then 1
    else if hx' : n ≤ x' then
          if hy' : n ≤ y' then
            M (Fin.subNat n x' hx') (Fin.subNat n y' hy')
          else 0
        else 0

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

