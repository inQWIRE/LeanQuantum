import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Data.Matrix.PEquiv
import Mathlib.Data.Finset.Image
import QuantumLib.ForMathlib.Data.Matrix.Basic

def NoDupVector (A : Type) (n : ℕ) := { v : Vector A n // v.toList.Nodup}

def pad_matrix {n m} (v : NoDupVector (Fin n) m) [Zero R] [One R]
  (U : Matrix (BitVec m) (BitVec m) R) : Matrix (BitVec n) (BitVec n) R := sorry

inductive embeddedGate (U : ℕ -> Type u) (n : ℕ) : Type u where
  | embedGate {m} (u : U m) (bits : NoDupVector (Fin n) m) : embeddedGate U n

def circuit (U : ℕ -> Type u) (n : ℕ) := List (embeddedGate U n)

def embeddedGateSemantics {U : ℕ -> Type u} [Zero R] [One R]
  (SU : forall n, U n -> Matrix (BitVec n) (BitVec n) R) {n} (G : embeddedGate U n) :
    Matrix (BitVec n) (BitVec n) R :=
  match G with
  | .embedGate u bits => pad_matrix bits (SU _ u)
