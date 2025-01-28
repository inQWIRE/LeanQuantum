import Quantumlib.Data.Gate.Equivs
import Quantumlib.Data.Gate.Pauli
import Quantumlib.Data.Matrix.Basic
import Quantumlib.Tactic.Basic

inductive Pauli
  | i
  | x
  | y 
  | z

namespace Pauli

def toCSquare : Pauli → CSquare 2
  | i => 1
  | x => σx
  | y => σy
  | z => σz

instance : Coe Pauli (CSquare 2) := ⟨Pauli.toCSquare⟩

def commute? : Pauli → Pauli → Bool
  | i, _ | _, i => true
  | x, x | y, y | z, z => true
  | _, _ => false

theorem commute_comm : ∀ a b, Pauli.commute? a b ↔ Pauli.commute? b a := by
  intros a b
  cases a <;> cases b <;> rfl

theorem mul_commutativity :
  ∀ (a b : Pauli),
    (a : CSquare 2).Commute b ∨ (a : CSquare 2).AntiCommute b := by 
      intros a b
      cases h : (a.commute? b)
      right
      rotate_right
      left
      all_goals
        cases a <;> cases b
          <;> simp_all [Pauli.commute?,
                        CMatrix.Commute,
                        CMatrix.AntiCommute,
                        toCSquare]

theorem pow_two : ∀ (a : Pauli), (a : CSquare 2) ^ 2 = 1 := by
  intros a
  cases a <;> simp [toCSquare, _root_.pow_two]

end Pauli
