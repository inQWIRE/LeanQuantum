import Quantumlib.Data.Matrix.Basic

open Matrix

@[reducible]
def ket0 : CVector 2 :=
  ![1, 0]

@[reducible]
def ket1 : CVector 2 :=
  ![0, 1]
@[reducible] def bra0 : CMatrix 1 2 :=
  ket0ᴴ

@[reducible]
def bra1 : CMatrix 1 2 :=
  ket1ᴴ

