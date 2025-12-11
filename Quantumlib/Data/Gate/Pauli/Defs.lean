import Quantumlib.ForMathlib.Data.BitVec.Basic
import Quantumlib.ForMathlib.Data.Complex.Basic
import Quantumlib.ForMathlib.Data.Matrix.Kron

import Mathlib.Algebra.MonoidAlgebra.Defs

def σx : CSquare 2 :=
  !![0, 1;
     1, 0]

def σy : CSquare 2 :=
  !![0, -Complex.I;
     Complex.I, 0]

def σz : CSquare 2 :=
  !![1,  0;
     0, -1]

/-- P = (-i)ᵐ Zᶻ Xˣ -/
@[ext]
structure Pauli (n : ℕ) where
  /-- Phase, (-i)ᵐ -/
  m : Fin 4 := 0
  z : BitVec n
  x : BitVec n
deriving DecidableEq, BEq

namespace Pauli

def X : Pauli 1 where
  z := 0
  x := 1

def Y : Pauli 1 where
  m := 1
  z := 1
  x := 1

def iY : Pauli 1 where
  z := 1
  x := 1

def Z : Pauli 1 where
  z := 1
  x := 0

def cons (z x : Bool) (P : Pauli n) : Pauli (n + 1) :=
  {P with z := P.z.cons z, x := P.x.cons x}

def tail (P : Pauli (n + 1)) : Pauli n :=
  {P with z := P.z.lsbs, x := P.x.lsbs}

def addPhase (a : Fin 4) (P : Pauli n) :=
  {P with m := P.m + a}

def zeroed (P : Pauli n) :=
  {P with m := 0}

def weight (P : Pauli n) : ℕ :=
  P.x ||| P.z |>.weight

def one : Pauli n where
  z := 0
  x := 0

instance : One (Pauli n) := ⟨one⟩

def neg : Pauli n → Pauli n := addPhase 2

instance : Neg (Pauli n) := ⟨neg⟩

def i : Pauli n → Pauli n := addPhase 3

def phaseFlipCount (P Q : Pauli n) : Fin 4 :=
  if P.x.dotZ₂ Q.z then 2 else 0

def mul (P Q : Pauli n) : Pauli n where
  m := P.m + Q.m + phaseFlipCount P Q
  z := P.z ^^^ Q.z
  x := P.x ^^^ Q.x

instance : Mul (Pauli n) := ⟨mul⟩

def kron {n m} (P : Pauli n) (Q : Pauli m) : Pauli (n + m) where
  m := P.m + Q.m
  z := P.z ++ Q.z
  x := P.x ++ Q.x

scoped[Pauli] infixl:100 " ⊗ " => kron

def evalPhase (P : Pauli n) : ℂ :=
  match P.m with
  | 0 => 1
  | 1 => -Complex.I
  | 2 => -1
  | 3 => Complex.I

def commutesWith (P Q : Pauli n) : Bool :=
  (phaseFlipCount P Q : Fin 4) == phaseFlipCount Q P

def toCMatrix (P : Pauli n) : CMatrix (2 ^ n) (2 ^ n) :=
  match n with
  | 0      => (-Complex.I) ^ P.m.toNat • 1
  | n' + 1 =>
    Matrix.reindex (finCongr <| by ring) (finCongr <| by ring)
    <| Matrix.kron (a := 2) (b := 2)
        (bitsToMat (P.z.msb, P.x.msb)) P.tail.toCMatrix
where
  bitsToMat p :=
    if p.1 && p.2 then
      Complex.I • σy
    else if p.1 then
      σz
    else if p.2 then
      σx
    else 1

end Pauli

abbrev PauliMap (n : ℕ) := MonoidAlgebra ℂ (Pauli n)

namespace PauliMap

noncomputable section

def normalized (Pm : PauliMap n) : PauliMap n :=
  Finsupp.sum Pm f
where
  f P c := MonoidAlgebra.single P.zeroed (P.evalPhase * c)

@[coe]
def ofPauli (P : Pauli n) : PauliMap n :=
  Finsupp.single P 1 |> normalized

instance : Coe (Pauli n) (PauliMap n) := ⟨ofPauli⟩

def toCMatrix (pm : PauliMap n) : CMatrix (2 ^ n) (2 ^ n) :=
  pm.sum (fun P c => (c • P.toCMatrix))

end
