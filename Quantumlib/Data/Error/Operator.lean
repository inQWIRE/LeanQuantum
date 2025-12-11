
import Quantumlib.ForMathlib.Data.BitVec.Basic
import Quantumlib.Data.Gate.Pauli.Lemmas
import Mathlib.Tactic
import Mathlib.Algebra.Group.Subgroup.Finite

structure StabilizerCode (n k : ℕ) where
  generators : List (Pauli n)
  logicalX : Fin k → Pauli n
  logicalZ : Fin k → Pauli n
  stabilizers_commute : ∀ P ∈ generators, ∀ Q ∈ generators, P.commutesWith Q
  logical_commute : ∀ i j, !(logicalX i).commutesWith (logicalZ j) = (i = j)
  logical_independent : ∀ i,
    let G := Subgroup.closure { g | g ∈ generators }
    ¬(logicalX i ∈ G ∨ logicalZ i ∈ G)

namespace StabilizerCode

abbrev G (code : StabilizerCode n k) : Subgroup (Pauli n) :=
  Subgroup.closure { g | g ∈ code.generators }

def syndrome (code : StabilizerCode n k) (E : Pauli n) : List Bool :=
  code.generators.map (fun S => !E.commutesWith S)

def corrects (code : StabilizerCode n k) (errors : Set (Pauli n)) : Prop :=
  errors.InjOn code.syndrome

end StabilizerCode

namespace BitFlip

def generators : List (Pauli 3) := [[P| ZZI ], [P| IZZ ]]

def group : Subgroup (Pauli 3) := Subgroup.closure { g | g ∈ generators }

theorem group_members : group.carrier = {[P| III ], [P| ZZI ], [P| IZZ ], [P| ZIZ ]} := by
  unfold group

  apply Set.Subset.antisymm
  · intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      simp [generators, List.mem_cons] at hx
      rcases hx with rfl | rfl <;> simp
    | one =>
      decide
    | mul x y hx hy ihx ihy =>
      simp at ihx ihy ⊢
      rcases ihx with rfl|rfl|rfl|rfl <;> rcases ihy with rfl|rfl|rfl|rfl
      <;> simp [Pauli.mul_def, Pauli.phaseFlipsWith]
    | inv x hx ihx =>
      simp at ihx ⊢
      rcases ihx with rfl|rfl|rfl|rfl
      <;> simp [Inv.inv, Pauli.phaseFlipsWith]
  · simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
    constructor
    · apply Subgroup.one_mem
    · constructor
      · apply Subgroup.subset_closure; simp [generators]
      · constructor
        · apply Subgroup.subset_closure; simp [generators]
        · have : [P| ZIZ] = [P| ZZI] * [P| IZZ] := by decide
          rw [this]
          apply Subgroup.mul_mem <;> apply Subgroup.subset_closure <;> simp [generators]

instance : DecidablePred (· ∈ group) := by
  intro x
  change Decidable (x ∈ group.carrier)
  rw [group_members]
  infer_instance

def code : StabilizerCode 3 1 where
  generators := generators
  logicalX := fun 0 => [P| XXX ]
  logicalZ := fun 0 => [P| ZZZ ]

  stabilizers_commute := by
    intros P hP Q hQ
    simp [generators, List.mem_cons] at hP hQ
    rcases hP with rfl|rfl <;> rcases hQ with rfl|rfl
    <;> decide

  logical_commute := by
    intros i j
    fin_cases i; fin_cases j; rfl

  logical_independent := by
    intros i
    fin_cases i
    dsimp
    intro h
    change _ ∈ group.carrier ∨ _ ∈ group.carrier at h
    rw [group_members] at h
    rcases h with h | h
    · rcases h with h|h|h|h <;> simp at h
    · rcases h with h|h|h|h <;> simp at h

instance : DecidablePred (· ∈ code.G) := by
  change DecidablePred (· ∈ group)
  infer_instance

theorem corrects_single_qubit_errors :
  let errors : Set (Pauli 3) := {[P| IIX ], [P| IXI ], [P| XII ]}
  code.corrects errors := by
  dsimp only [StabilizerCode.corrects, Set.InjOn]
  intro e1 he1 e2 he2 h_eq

  simp at he1 he2
  rcases he1 with rfl | rfl | rfl <;> rcases he2 with rfl | rfl | rfl
    <;> simp_all +decide

end BitFlip

namespace Shor9

-- Generators for the 9-qubit code
-- X-type stabilizers: X_i X_{i+1} typically, but Shor code uses 8 generators.
-- M1 = ZZ I I I I I I I
-- M2 = I ZZ I I I I I I
-- ...
-- M7 = XXXXXX III
-- M8 = III XXXXXX
-- Standard Shor code:
-- 2 Z-type checks for each block of 3 (6 total)
-- 2 X-type checks comparing blocks (2 total)

def generators : List (Pauli 9) := [
  -- Block 1 Z-checks
  [P| ZZIIIIIII ], [P| IZZIIIIII ],
  -- Block 2 Z-checks
  [P| IIIZZIIII ], [P| IIIIZZIII ],
  -- Block 3 Z-checks
  [P| IIIIIIZZI ], [P| IIIIIIIZZ ],
  -- Block X-checks (comparing signs of blocks)
  [P| XXXXXXIII ], [P| IIIXXXXXX ]
]

def code : StabilizerCode 9 1 where
  generators := generators
  logicalX := fun 0 => [P| XXXXXXXXX ]
  logicalZ := fun 0 => [P| ZZZZZZZZZ ]

  stabilizers_commute := by
    intros P hP Q hQ
    simp [generators] at hP hQ
    rcases hP with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    <;> rcases hQ with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    <;> decide

  logical_commute := by
    intros i j
    fin_cases i; fin_cases j; decide

  logical_independent := by
    sorry


end Shor9
