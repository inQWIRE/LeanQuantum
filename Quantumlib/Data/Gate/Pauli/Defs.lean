import Quantumlib.Data.Complex.Basic
import Quantumlib.Data.Matrix.Basic
import Quantumlib.Data.Matrix.PowBitVec

open Kron

def σx : CSquare 2 :=
  !![0, 1; 
     1, 0]

def σy : CSquare 2 :=
  !![0, -Complex.I;
     Complex.I, 0]

def σz : CSquare 2 :=
  !![1,  0;
     0, -1]

/-- Unsigned Pauli -/
structure UPauli (n : ℕ) where
  x : BitVec n
  z : BitVec n
deriving DecidableEq

structure Pauli (n : ℕ) extends UPauli n where
  c : ℂ

abbrev PauliMap (n : ℕ) := UPauli n →₀ ℂ

namespace UPauli

def X : UPauli 1 where
  x := 1
  z := 0

def negIY : UPauli 1 where
  x := 1
  z := 1

def Z : UPauli 1 where
  x := 0
  z := 1

def cons (x z : Bool) (P : UPauli n) : UPauli (n + 1) :=
  {P with x := P.x.cons x, z := P.z.cons z}

def tail (P : UPauli (n + 1)) : UPauli n :=
  {P with x := P.x.lsbs, z := P.z.lsbs}

def phaseFlipsWith (P Q : UPauli n) : Bool :=
  (P.z &&& Q.x).weight % 2 == 1

def commutesWith (P Q : UPauli n) : Bool :=
  P.phaseFlipsWith Q == Q.phaseFlipsWith P

def weight (P : UPauli n) : ℕ :=
  P.x ||| P.z |>.weight

def one : UPauli n := {x := 0, z := 0}

instance : One (UPauli n) := ⟨one⟩

def mul (P Q : UPauli n) : UPauli n where
  x := P.x ^^^ Q.x
  z := P.z ^^^ Q.z

instance : Mul (UPauli n) := ⟨mul⟩

def toCMatrix (P : UPauli n) : CMatrix (2 ^ n) (2 ^ n) :=
  match n with
  | 0      => 1
  | n' + 1 => 
    Matrix.reindex (finCongr <| by ring) (finCongr <| by ring)
    <| Matrix.kron (a := 2) (b := 2)
        (bitsToMat (P.x.msb, P.z.msb)) P.tail.toCMatrix
where
  bitsToMat p := 
    if p.1 && p.2 then 
      -(Complex.I • σy)
    else if p.1 then
      σx
    else if p.2 then
      σz
    else 1

end UPauli

namespace Pauli

@[coe]
def ofUPauli (P : UPauli n) : Pauli n := {P with c := 1}

instance : Coe (UPauli n) (Pauli n) := ⟨ofUPauli⟩

def cons (x z : Bool) (P : Pauli n) : Pauli (n + 1) :=
  {P with x := P.x.cons x, z := P.z.cons z}

def tail (P : Pauli (n + 1)) : Pauli n :=
  {P with x := P.x.lsbs, z := P.z.lsbs}

def one : Pauli n := {(1 : UPauli n) with c := 1}

instance : One (Pauli n) := ⟨one⟩

def smul (c : ℂ) (P : Pauli n) := 
  {P with c := c * P.c}

instance : SMul ℂ (Pauli n) := ⟨smul⟩

def mul (P Q : Pauli n) : Pauli n := 
  (P.c * Q.c) • ofUPauli (P.toUPauli * Q.toUPauli)

instance : Mul (Pauli n) := ⟨mul⟩

def neg (P : Pauli n) : Pauli n :=
  (-1 : ℂ) • P

instance : Neg (Pauli n) := ⟨neg⟩

def toCMatrix (Pc : Pauli n) : CMatrix (2 ^ n) (2 ^ n) :=
  Pc.2 • Pc.1.toCMatrix

end Pauli

namespace PauliMap

noncomputable section

@[coe]
def ofPauli (P : Pauli n) : PauliMap n :=
  Finsupp.single P.toUPauli P.c 

instance : Coe (Pauli n) (PauliMap n) := ⟨ofPauli⟩

def one : PauliMap n := (1 : Pauli n)

instance : One (PauliMap n) := ⟨one⟩

def mul (pm qm : PauliMap n) : PauliMap n :=
  pm.sum (fun P c₁ =>
    qm.sum (fun Q c₂ =>
      let R := P * Q
      let neg := (-1) ^ (P.phaseFlipsWith Q).toNat
      Finsupp.single R (c₁ * c₂ * neg)))

instance : Mul (PauliMap n) := ⟨mul⟩

def toCMatrix (pm : PauliMap n) : CMatrix (2 ^ n) (2 ^ n) :=
  pm.sum (fun P c => ({P with c := c} : Pauli n).toCMatrix)

end

