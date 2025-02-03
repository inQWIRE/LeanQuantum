import Quantumlib.Data.Gate.Equivs
import Quantumlib.Data.Gate.Pauli.Defs

namespace Pauli

@[simp]
theorem one_def : (1 : Pauli n) = {
  x := 0,
  z := 0
} := by rfl

@[simp]
lemma one_weight : (1 : Pauli n).weight = 0 := by
  simp [weight]

@[simp]
theorem neg_def (P : Pauli n): -P = {P with isNeg := !P.isNeg} := rfl

@[simp]
theorem neg_weight (P : Pauli n): (-P).weight = P.weight := rfl


@[simp]
theorem mul_def (P Q : Pauli n) : P * Q = {
  isNeg := P.isNeg ^^ Q.isNeg ^^ phaseFlipsWith P Q,
  x := P.x ^^^ Q.x,
  z := P.z ^^^ Q.z
} := by
  conv =>
    lhs
    tactic => simp_rw [(· * ·), Mul.mul, Pauli.mul]
    rfl

@[simp]
theorem mul_one (P : Pauli n) : P * 1 = P := by
  simp [phaseFlipsWith]

@[simp]
theorem one_mul (P : Pauli n) : 1 * P = P := by
  simp [phaseFlipsWith]

theorem commutesWith_comm (P Q : Pauli n) : P.commutesWith Q ↔ Q.commutesWith P := by
  simp [commutesWith]
  conv =>
    lhs
    rw [add_comm, BitVec.and_comm, BitVec.and_comm P.x]
    rfl

theorem mul_comm_of_commutesWith (P Q : Pauli n) : P.commutesWith Q → P * Q = Q * P := by
  intros h
  simp only [mul_def, mk.injEq, phaseFlipsWith]
  constructor
  rotate_right
  constructor <;> simp only [BitVec.xor_comm]
  unfold commutesWith at h
  simp only [beq_iff_eq] at h
  congr 1 <;> try simp only [Bool.xor_comm]
  rw [←Nat.even_iff, Nat.even_add'] at h
  simp only [beq_eq_beq]
  repeat rw [←Nat.odd_iff]
  rw [BitVec.and_comm Q.z]
  rwa [Iff.comm]

theorem mul_anticomm_of_not_commutesWith (P Q : Pauli n) : !P.commutesWith Q → P * Q = -(Q * P) := by
  intros h
  simp only [mul_def, neg_def, mk.injEq, phaseFlipsWith]
  constructor
  rotate_right
  constructor <;> simp only [BitVec.xor_comm]
  unfold commutesWith at h
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true,
             beq_eq_false_iff_ne, ne_eq,
             Nat.mod_two_not_eq_zero] at h
  rw [←Nat.odd_iff] at h
  cases hParity : decide (Odd (P.z &&& Q.x).weight)
  · simp only [decide_eq_false_iff_not,
               Nat.not_odd_iff_even] at hParity
    rw [Nat.odd_add] at h
    have hOtherParity := h.mpr hParity
    rw [Nat.even_iff] at hParity
    rw [Nat.odd_iff] at hOtherParity
    rw [BitVec.and_comm Q.z,
        hParity, hOtherParity]
    simp [Bool.xor_comm]
  · simp only [decide_eq_true_eq] at hParity
    rw [Nat.odd_add'] at h
    have hOtherParity := h.mp hParity
    rw [Nat.odd_iff] at hParity
    rw [Nat.even_iff] at hOtherParity
    rw [hParity, BitVec.and_comm Q.z,
        hOtherParity]
    simp [Bool.xor_comm]

theorem mul_self_of_phaseFlipsWith (P : Pauli n) : P.phaseFlipsWith P → P * P = -1 := by
  simp

theorem mul_self_of_not_phaseFlipsWith (P : Pauli n) : !P.phaseFlipsWith P → P * P = 1 := by
  simp
    

theorem mul_toCMatrix_eq_toCMatrix_mul_toCMatrix (P Q : Pauli n) :
  (P * Q).toCMatrix = P.toCMatrix * Q.toCMatrix := by
    simp [toCMatrix, CMatrix.powBitVec]

    sorry

@[simp]
lemma one_toCMatrix_eq : (1 : Pauli n).toCMatrix = 1 := by
  simp [toCMatrix]

@[simp]
lemma X_toCMatrix_eq : X.toCMatrix = σx := by
  simp [X, toCMatrix, CMatrix.powBitVec]

@[simp]
lemma IY_toCMatrix_eq : IY.toCMatrix = Complex.I • σy := by
  simp [IY, toCMatrix, CMatrix.powBitVec]

@[simp]
lemma Z_toCMatrix_eq : Z.toCMatrix = σz := by
  simp [Z, toCMatrix, CMatrix.powBitVec]


example : 
  let P : Pauli 1 := {
    x := 0
    z := 0
  } 
  P * P = P := by
    simp [phaseFlipsWith]


example : 
  let P : Pauli 1 := {
    x := 1,
    z := 1
  } 
  let Q : Pauli 1 := {
    x := 0,
    z := 1
  } 
  P * Q = {
    x := 1,
    z := 0
  } := by
    simp [phaseFlipsWith]

example : 
  let P : Pauli 1 := {
    x := 1,
    z := 1
  } 
  let Q : Pauli 1 := {
    x := 1,
    z := 1
  } 
  P * Q = {
    isNeg := true,
    x := 0,
    z := 0
  } := by
    simp [phaseFlipsWith, BitVec.weight, BitVec.foldr]


end Pauli
