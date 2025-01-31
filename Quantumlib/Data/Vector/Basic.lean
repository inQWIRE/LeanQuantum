import Mathlib.Data.Vector.Basic

instance : AndOp (List.Vector Bool n) where
  and a b := a.map₂ and b

instance : OrOp (List.Vector Bool n) where
  or a b := a.map₂ or b

instance : Xor (List.Vector Bool n) where
  xor a b := a.map₂ xor b
