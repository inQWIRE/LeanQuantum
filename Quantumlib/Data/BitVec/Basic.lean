namespace BitVec

def lsbs (x : BitVec (w + 1)) : BitVec w := x.setWidth w

def foldr (x : BitVec w) (f : Bool → α → α) (init : α) : α := 
  w.fold (fun i h acc => f x[i] acc) init

def weight (x : BitVec w) : Nat :=
  x.foldr (·.toNat + ·) 0

example : (0b0101001#10).weight = 3 := by rfl

end BitVec
