import Quantumlib.Data.Complex.Basic
import Quantumlib.Data.Matrix.Basic
import Quantumlib.Data.Matrix.PowBitVec

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
  isNeg : Bool := false
  x : BitVec n
  z : BitVec n

namespace Pauli

def X : Pauli 1 where
  x := 1
  z := 0

def IY : Pauli 1 where
  isNeg := true
  x := 1
  z := 1

def Z : Pauli 1 where
  x := 0
  z := 1


def commutesWith (P Q : Pauli n) : Bool :=
  ((P.x &&& Q.z).weight + (P.z &&& Q.x).weight) % 2 == 0

def phaseFlipsWith (P Q : Pauli n) : Bool :=
  (P.z &&& Q.x).weight % 2 == 1

def weight (P : Pauli n) : ℕ :=
  P.x ||| P.z |>.weight

def one : Pauli n := {x := 0, z := 0}

instance : One (Pauli n) := ⟨one⟩

def neg (P : Pauli n) : Pauli n := {P with isNeg := !P.isNeg}

instance : Neg (Pauli n) := ⟨neg⟩

def mul (P Q : Pauli n) : Pauli n := {
  isNeg := P.isNeg ^^ Q.isNeg ^^ phaseFlipsWith P Q,
  x := P.x ^^^ Q.x,
  z := P.z ^^^ Q.z
}

instance : Mul (Pauli n) := ⟨mul⟩

noncomputable
def toCMatrix (P : Pauli n) : CSquare (2 ^ n) :=
  (-1) ^ P.isNeg.toNat • (σx ^ᵥ P.x * σz ^ᵥ P.z)

end Pauli
 
