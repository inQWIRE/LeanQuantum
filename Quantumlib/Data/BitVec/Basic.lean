namespace BitVec

def lsbs (x : BitVec (w + 1)) : BitVec w := x.setWidth w

def foldr (x : BitVec w) (f : Bool → α → α) (init : α) : α := 
  w.fold (fun i h acc => f x[i] acc) init

def weight (x : BitVec w) : Nat :=
  x.foldr (·.toNat + ·) 0

def dot (x y : BitVec w) : Nat :=
  (x &&& y).weight

def dotZ₂ (x y : BitVec w) : Bool := 
  (x.dot y) % 2 == 1

example : (0b0101001#10).weight = 3 := by rfl
example : (0b0101001#10).dotZ₂ (0b1#10) = true := by rfl
example : (0b0101001#10).dotZ₂ (0b10#10) = false := by rfl

end BitVec
