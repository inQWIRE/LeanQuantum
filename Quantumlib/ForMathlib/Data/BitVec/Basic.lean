import Mathlib

namespace BitVec

def lsbs (x : BitVec (w + 1)) : BitVec w := x.setWidth w

def foldl (x : BitVec w) (f : Bool → α → α) (init : α) : α :=
  w.fold (fun i h acc => f x[i] acc) init

def weight (x : BitVec w) : Nat :=
  x.foldl (·.toNat + ·) 0

def dot (x y : BitVec w) : Nat :=
  (x &&& y).weight

def dotZ₂ (x y : BitVec w) : Bool :=
  (x.dot y) % 2 == 1

instance : Fintype (BitVec w) := Fintype.ofEquiv (Fin (2^w)) BitVec.equivFin.symm.toEquiv

end BitVec
