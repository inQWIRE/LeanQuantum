import Quantumlib.Data.Complex.Basic
import Quantumlib.Data.Matrix.Basic
import Quantumlib.Data.Matrix.PowBitVec
import Quantumlib.Data.Finmap.MergeWith

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
@[ext]
structure UPauli (n : ℕ) where
  x : BitVec n
  z : BitVec n
deriving DecidableEq

abbrev PauliCoeff (n : ℕ) := UPauli n × ℂ

namespace UPauli

instance : Ord (UPauli n) where
  compare := compareLex (compareOn (·.x.toNat)) (compareOn (·.z.toNat))
    
def X : UPauli 1 where
  x := 1
  z := 0

def IY : UPauli 1 where
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

def mul (P Q : UPauli n) : UPauli n := {
  x := P.x ^^^ Q.x,
  z := P.z ^^^ Q.z
}

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
      Complex.I • σy
    else if p.1 then
      σx
    else if p.2 then
      σz
    else 1

end UPauli

namespace PauliCoeff

def X  : PauliCoeff 1 := (UPauli.X, 1)

def IY : PauliCoeff 1 := (UPauli.IY, 1)

def Z  : PauliCoeff 1 := (UPauli.Z, 1)

def cons (x z : Bool) (Pc : PauliCoeff n) : PauliCoeff (n + 1) :=
  ({Pc.1 with x := Pc.1.x.cons x, z := Pc.1.z.cons z}, Pc.2)

def tail (P : UPauli (n + 1)) : UPauli n :=
  {P with x := P.x.lsbs, z := P.z.lsbs}

def neg (Pc : PauliCoeff n) : PauliCoeff n :=
  (Pc.1, -Pc.2)

instance : Neg (PauliCoeff n) := ⟨neg⟩

def mul (Pc Qc : PauliCoeff n) : PauliCoeff n := 
  (Pc.1 * Qc.1, Pc.2 * Qc.2 * (-1) ^ (Pc.1.phaseFlipsWith Qc.1).toNat)

instance : Mul (PauliCoeff n) := ⟨mul⟩

def smul (c : ℂ) (Pc : PauliCoeff n) := 
  (Pc.1, c * Pc.2)

instance : SMul ℂ (PauliCoeff n) := ⟨smul⟩

def toCMatrix (Pc : PauliCoeff n) : CMatrix (2 ^ n) (2 ^ n) :=
  Pc.2 • Pc.1.toCMatrix

end PauliCoeff

abbrev PauliMap (n : ℕ) := Lean.RBMap (UPauli n) ℂ Ord.compare

namespace PauliMap

open Lean (RBMap)

def X  : PauliMap 1 := RBMap.ofList [PauliCoeff.X]
def IY : PauliMap 1 := RBMap.ofList [PauliCoeff.IY]
def Z  : PauliMap 1 := RBMap.ofList [PauliCoeff.Z]

def one : PauliMap n := RBMap.ofList [1]

instance : One (PauliMap n) := ⟨one⟩

def add (pm qm : PauliMap n) : PauliMap n := 
  pm.mergeBy (fun _ => (· + ·)) qm

instance : Add (PauliMap n) := ⟨add⟩

def smul (a : ℂ) (pm : PauliMap n) : PauliMap n :=
  pm.filterMap (fun _ c => some (a * c))

instance : SMul ℂ (PauliMap n) := ⟨smul⟩

def mul (pm qm : PauliMap n) : PauliMap n :=
  pm.fold (init := ∅) fun acc' P c₁ =>
    qm.fold (init := acc') fun acc Q c₂ =>
      let R := P * Q
      let factor := (-1 : ℂ) ^ (UPauli.phaseFlipsWith P Q).toNat * c₁ * c₂
      match acc.find? R with
      | none   => acc.insert R factor
      | some c => acc.insert R (c + factor)

instance : Mul (PauliMap n) := ⟨mul⟩

end PauliMap
