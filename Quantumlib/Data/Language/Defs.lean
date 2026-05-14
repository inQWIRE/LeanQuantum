import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Data.Matrix.PEquiv
import Mathlib.Data.Finset.Image
import QuantumLib.ForMathlib.Data.Matrix.Basic
import QuantumLib.ForMathlib.Data.BitVec.Basic
import Mathlib.Data.BitVec
import Batteries.Data.BitVec
import Init.Data.Vector


def NoDupVector (A : Type) (n : ℕ) := { v : Vector A n // v.toList.Nodup}

namespace NoDupVector

def image (f : A -> B) (Hf : f.Injective) {n} (v : NoDupVector A n) :
  NoDupVector B n := ⟨v.val.map f, by {
    rw [Vector.toList_map]
    rw [List.nodup_map_iff Hf]
    apply v.property
  }⟩

def map (f : A ↪ B) {n} (v : NoDupVector A n) : NoDupVector B n :=
  image f f.injective v

end NoDupVector


namespace Vector

def listNotIndexed {n m} (v : Vector (Fin n) m) : List (Fin n) :=
  (List.finRange n).filter (fun i => (v.contains i).not)

end Vector

namespace BitVec

def vectorReindex {n m} (v : Vector (Fin n) m) (bv : BitVec n) : BitVec m :=
  BitVec.ofFnLE (fun i => bv.getLsb (v.get i))

def vectorNotIndexed {n m} (v : Vector (Fin n) m) (bv : BitVec n) : List Bool :=
  v.listNotIndexed.map bv.getLsb

end BitVec



def gen_pad_matrix {n m n' m'} (vn : Vector (Fin n') n)
  (vm : Vector (Fin m') m) [Zero R]
  (U : Matrix (BitVec n) (BitVec m) R) : Matrix (BitVec n') (BitVec m') R :=
  fun v w =>
    if v.vectorNotIndexed vn = w.vectorNotIndexed vm then
      U (v.vectorReindex vn) (w.vectorReindex vm) else 0

def pad_matrix {n m} (v : NoDupVector (Fin n) m) [Zero R]
  (U : Matrix (BitVec m) (BitVec m) R) : Matrix (BitVec n) (BitVec n) R :=
  gen_pad_matrix v.val v.val U





inductive EmbeddedGate (U : ℕ -> Type u) (n : ℕ) : Type u where
  | embedGate {m} (u : U m) (bits : NoDupVector (Fin n) m) : EmbeddedGate U n

namespace EmbeddedGate

def semantics {U : ℕ -> Type u} [Zero R]
  (SU : forall n, U n -> Matrix (BitVec n) (BitVec n) R) {n} (G : EmbeddedGate U n) :
    Matrix (BitVec n) (BitVec n) R :=
  match G with
  | .embedGate u bits => pad_matrix bits (SU _ u)

def whiskerL {U : ℕ -> Type u} (m : ℕ) {n} (G : EmbeddedGate U n) : EmbeddedGate U (m + n) :=
  match G with
  | .embedGate u bits =>
    .embedGate u (bits.image (Fin.natAdd m) (Fin.natAdd_injective n m))

def whiskerR {U : ℕ -> Type u} (m : ℕ) {n} (G : EmbeddedGate U n) : EmbeddedGate U (n + m) :=
  match G with
  | .embedGate u bits =>
    .embedGate u (bits.image (Fin.castAdd m) (Fin.castAdd_injective n m))

end EmbeddedGate




def Circuit (U : ℕ -> Type u) (n : ℕ) := List (EmbeddedGate U n)

namespace Circuit

instance : OfNat (Circuit U n) 1 := ⟨[]⟩

instance : Mul (Circuit U n) := ⟨List.append⟩

def whiskerL {U : ℕ -> Type u} (m : ℕ) {n} (G : Circuit U n) : Circuit U (m + n) :=
  G.map (.whiskerL m)

def whiskerR {U : ℕ -> Type u} (m : ℕ) {n} (G : Circuit U n) : Circuit U (n + m) :=
  G.map (.whiskerR m)

def stack {U : ℕ -> Type u} {n m} (G : Circuit U n) (H : Circuit U m) : Circuit U (n + m) :=
  G.whiskerR m * H.whiskerL n

def semantics [One R] [Mul R] [AddCommMonoid R] {U : ℕ -> Type u}
  (SU : forall n, U n -> Matrix (BitVec n) (BitVec n) R) {n} (C : Circuit U n) :
    Matrix (BitVec n) (BitVec n) R :=
    (C.map (fun g => g.semantics SU)).prod

end Circuit
