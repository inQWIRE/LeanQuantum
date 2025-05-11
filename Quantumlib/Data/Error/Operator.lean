import Quantumlib.Data.Gate.Pauli
import Quantumlib.Data.Gate.Pauli.Lemmas

structure StabilizerCode (n k : ℕ) where
  G : Subgroup (Pauli n)
  logicalX : Fin k → Pauli n
  logicalZ : Fin k → Pauli n
  stabilizers_commute : ∀ P ∈ G, ∀ Q ∈ G, P.commutesWith Q
  logical_commute : ∀ i j, !(logicalX i).commutesWith (logicalZ j) = (i = j)
  logical_independent : ∀ i, ¬(logicalX i ∈ G ∨ logicalZ i ∈ G)

namespace StabilizerCode

def syndrome (code : StabilizerCode n k) (E : Pauli n) : Set Bool :=
  Set.image (fun S => !E.commutesWith S) code.G.carrier

def bitFlipCode : StabilizerCode 3 1 where
  G := Subgroup.closure {[P| ZZI ], [P| IZZ ]}
  logicalX := fun 0 => [P| XXX ]
  logicalZ := fun 0 => [P| ZZZ ]

  stabilizers_commute := by
    intros P hP Q hQ
    induction hP using Subgroup.closure_induction with
    | mem P' hP' =>
      induction hQ using Subgroup.closure_induction with
      | mem Q' hQ' =>
        set_option maxRecDepth 1300 in
        decide +revert
      | one => simp
      | mul Q' R hQ' hR hP'Q' hP'R => 
        rw [Pauli.commutesWith_iff, commute_iff_eq] at *
        rw [mul_assoc, ←hP'R, ←mul_assoc Q', ←hP'Q', mul_assoc]
      | inv R hR hP'R  =>
        rw [Pauli.commutesWith_iff, commute_iff_eq] at *
        simp_all [Pauli.inv_mul, Pauli.mul_inv]
    | one => simp
    | mul P R hP hR hPQ hRQ => 
      rw [Pauli.commutesWith_iff, commute_iff_eq] at *
      rw [mul_assoc, hRQ, ←mul_assoc Q, ←hPQ, mul_assoc]
    | inv R hR hP'R  =>
      rw [Pauli.commutesWith_iff, commute_iff_eq] at *
      simp_all [Pauli.inv_mul, Pauli.mul_inv]
  logical_commute := by
    intros i j
    fin_cases i; fin_cases j; rfl



theorem bitFlipCode_corrects_single_qubit_errors (E : Pauli 3) (hE : E.weight = 1) (hX : E.z = 0) :
  ∃ C : Pauli 3, C.weight ≤ 1 ∧ (E.commutesWith C) := by
    have : E.zeroed ∈ [[P| IIX ], [P| IXI ], [P| XII ]] := by
      simp
      set_option maxRecDepth 2000 in
      decide +revert
    simp at this 
    rcases this with h | h | h <;> sorry


end StabilizerCode
