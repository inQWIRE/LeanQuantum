import Quantumlib.Data.Gate.Equivs
import Quantumlib.Data.Gate.Pauli.Defs

open Kron

@[simp]
lemma σx_ne_1 : σx ≠ 1 := by
  intros h
  apply_fun (· 0 0) at h
  simp [σx] at h

@[simp]
lemma σy_ne_1 : σy ≠ 1 := by
  intros h
  apply_fun (· 0 0) at h
  simp [σy] at h

@[simp]
lemma neg_I_smul_σy_ne_1 : -(Complex.I • σy) ≠ 1 := by
  intros h
  apply_fun (· 0 0) at h
  simp [σy] at h

@[simp]
lemma σz_ne_1 : σz ≠ 1 := by
  intros h
  apply_fun (· 1 1) at h
  simp [σz] at h
  apply Complex.one_ne_neg_one
  symm
  assumption

@[simp]
lemma σx_ne_σy : σx ≠ σy := by
  intros h
  apply_fun (· 1 0) at h
  simp [σx, σy] at h
  rw [Complex.ext_iff] at h
  simp at h

@[simp]
lemma σx_ne_neg_I_smul_σy : σx ≠ -(Complex.I • σy) := by
  intros h
  apply_fun (· 0 1) at h
  simp [σx, σy] at h

@[simp]
lemma σx_ne_σz : σx ≠ σz := by
  intros h
  apply_fun (· 0 0) at h
  simp [σx, σz] at h

@[simp]
lemma σy_ne_σz : σy ≠ σz := by
  intros h
  apply_fun (· 0 0) at h
  simp [σy, σz] at h

@[simp]
lemma neg_I_smul_σy_ne_σz : -(Complex.I • σy) ≠ σz := by
  intros h
  apply_fun (· 0 0) at h
  simp [σy, σz] at h


namespace Pauli

theorem cons_msb_tail (P : Pauli (n + 1)) :
  P = cons P.x.msb P.z.msb P.tail  := by 
    simp [cons, tail, BitVec.cons_msb_lsbs]

@[simp]
theorem neg_isNeg (P : Pauli n) :
  (-P).isNeg = !P.isNeg := by
    simp [(-·), Pauli.neg]

@[simp]
theorem neg_x (P : Pauli n) :
  (-P).x = P.x := by
    simp [(-·), Pauli.neg]

@[simp]
theorem neg_z (P : Pauli n) :
  (-P).z = P.z := by
    simp [(-·), Pauli.neg]
  
@[simp]
theorem cons_x (P : Pauli n) a b :
  (cons a b P).x = BitVec.cons a P.x := by 
    simp [cons]

@[simp]
theorem cons_z (P : Pauli n) a b :
  (cons a b P).z = BitVec.cons b P.z := by 
    simp [cons]

@[simp]
theorem cons_tail (P : Pauli n) a b :
  (cons a b P).tail = P := by 
    simp [cons, tail]

@[simp]
theorem cons_isNeg (P : Pauli n) a b :
  (cons a b P).isNeg = P.isNeg := by 
    simp [cons]

@[simp]
theorem tail_isNeg (P : Pauli (n + 1)) :
  P.tail.isNeg = P.isNeg := by 
    simp [tail]

theorem tail_x (P : Pauli (n + 1)) :
  P.tail.x = P.x.lsbs := by 
    simp [tail]

theorem tail_z (P : Pauli (n + 1)) :
  P.tail.z = P.z.lsbs := by 
    simp [tail]

theorem tail_neg (P : Pauli (n + 1)) :
  (-P).tail = -P.tail := by 
    simp [tail, (-·), neg]

@[simp]
theorem one_def : (1 : Pauli n) = {
  x := 0,
  z := 0
} := by rfl

@[simp]
lemma one_weight : (1 : Pauli n).weight = 0 := by
  simp [weight]

@[simp]
theorem neg_def (P : Pauli n) : -P = {P with isNeg := !P.isNeg} := rfl

@[simp]
theorem neg_weight (P : Pauli n) : (-P).weight = P.weight := rfl

theorem of_length_zero (P : Pauli 0) : P = 1 ∨ P = -1 := by
  let ⟨isNeg, x, z⟩ := P
  have hx := x.eq_nil
  have hz := z.eq_nil
  cases isNeg <;> simp_all

theorem phaseFlipsWith_cons (P Q : Pauli n) {a b c d} :
  (cons a b P).phaseFlipsWith (cons c d Q) ↔
    (b && c) ^^ P.phaseFlipsWith Q := by
      cases b <;> cases c
        <;> simp_all [phaseFlipsWith, Nat.succ_mod_two_eq_one_iff]

@[simp]
theorem mul_def (P Q : Pauli n) : P * Q = {
  isNeg := P.isNeg ^^ Q.isNeg ^^ phaseFlipsWith P Q,
  x := P.x ^^^ Q.x,
  z := P.z ^^^ Q.z
} := by
  conv =>
    lhs
    tactic => simp_rw [(· * ·), Mul.mul, Pauli.mul]

theorem mul_cons (P Q : Pauli n) : 
  cons a b P * cons c d Q =
  let r := cons (a ^^ c) (b ^^ d) (P * Q)
  if b && c then
    -r
  else 
    r := by
      split
      next h =>
        simp only [cons, mul_def, phaseFlipsWith, BitVec.cons_and_cons, h, BitVec.weight_cons_true,
          Bool.bne_assoc, BitVec.cons_xor_cons, neg_def, mk.injEq, and_self, and_true]
        obtain h' | h' := Nat.mod_two_eq_zero_or_one (P.z &&& Q.x).weight
        · simp [h', Nat.succ_mod_two_eq_one_iff.mpr h']
        · simp [h', Nat.succ_mod_two_eq_zero_iff.mpr h']
      next h =>
        cases b <;>
          simp [h, cons, phaseFlipsWith]

@[simp]
theorem mul_one (P : Pauli n) : P * 1 = P := by
  simp [phaseFlipsWith]

@[simp]
theorem one_mul (P : Pauli n) : 1 * P = P := by
  simp [phaseFlipsWith]

@[simp]
theorem neg_mul (P Q : Pauli n) : -P * Q = -(P * Q) := by
  simp [phaseFlipsWith]

@[simp]
theorem mul_neg (P Q : Pauli n) : P * -Q = -(P * Q) := by
  simp [phaseFlipsWith]

@[simp]
theorem neg_one_mul (P : Pauli n) : -1 * P = -P := by
  rw [neg_mul, one_mul]

@[simp]
theorem mul_neg_one (P : Pauli n) : P * -1 = -P := by
  rw [mul_neg, mul_one]

theorem commutesWith_comm (P Q : Pauli n) : P.commutesWith Q ↔ Q.commutesWith P := by
  simp [commutesWith]
  conv =>
    lhs
    rw [add_comm, BitVec.and_comm, BitVec.and_comm P.x]

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

theorem mul_anticomm_of_not_commutesWith (P Q : Pauli n) : ¬P.commutesWith Q → P * Q = -(Q * P) := by
  intros h
  simp only [mul_def, neg_def, mk.injEq, phaseFlipsWith]
  constructor
  rotate_right
  constructor <;> simp only [BitVec.xor_comm]
  unfold commutesWith at h
  simp only [beq_iff_eq, Nat.mod_two_not_eq_zero] at h
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

theorem mul_self (P : Pauli n) : P * P = if P.phaseFlipsWith P then -1 else 1 := by
  split <;> simp_all

lemma toCMatrix'_cons {n} a b (P : Pauli n) : (cons a b P).toCMatrix' = 
    (Matrix.reindex (finCongr <| by ring) (finCongr <| by ring)
    <| Matrix.kron (a := 2) (b := 2) 
        (toCMatrix'.bitsToMat (a, b)) P.toCMatrix') := by
          simp [toCMatrix']

@[simp]
theorem toCMatrix'_neg (P : Pauli n) :
  (-P).toCMatrix' = -P.toCMatrix' := by
    induction n with
    | zero =>
      obtain h | h := of_length_zero P
        <;> simp_all [toCMatrix']
    | succ n' ih => 
      conv_lhs =>
        rw [cons_msb_tail P]
        simp only [toCMatrix', cons_tail, tail_neg, ih]
      simp [Matrix.kron_neg, Matrix.submatrix_neg, toCMatrix']

theorem toCMatrix'_eq_toCMatrix (P : Pauli n) : 
  P.toCMatrix' = P.toCMatrix := by
    induction n with
    | zero =>
      obtain hP | hP := of_length_zero P
        <;> simp_all [toCMatrix', toCMatrix]

    | succ n' ih =>
      rw [cons_msb_tail P, toCMatrix'_cons, ih]
      simp only [
        toCMatrix, Matrix.reindex_apply,
        cons_isNeg, cons_x, CMatrix.powBitVec_cons, cons_z,
        Matrix.submatrix_mul_equiv, ←Matrix.mul_kron_mul,
        toCMatrix'.bitsToMat
      ]
      cases P.x.msb <;> cases P.z.msb
        <;> simp [Matrix.submatrix_neg,
                  Matrix.submatrix_smul] 

theorem toCMatrix'_bitsToMat_injective :
  Function.Injective (toCMatrix'.bitsToMat) := by
    simp only [Function.Injective]
    intro ⟨ax, az⟩ ⟨bx, bz⟩ h
    cases ax <;> cases az <;> cases bx <;> cases bz
      <;> simp_all [toCMatrix'.bitsToMat]
      <;> first | simp_all | (symm at h; try simp_all)

lemma toCMatrix'_bitsToMat_mul :
  toCMatrix'.bitsToMat (a, b) * toCMatrix'.bitsToMat (c, d)
  = let r := toCMatrix'.bitsToMat (a ^^ c, b ^^ d)
    if b && c then -r else r := by
      cases a <;> cases b <;> cases c <;> cases d
        <;> simp [toCMatrix'.bitsToMat, smul_smul]

theorem toCMatrix'_injective {n} :
  Function.Injective (toCMatrix' (n := n)) := by
    simp only [Function.Injective]
    intros P Q h
    induction n with
    | zero =>
      obtain hP | hP := of_length_zero P
        <;> obtain hQ | hQ := of_length_zero Q
        <;> simp_all [toCMatrix'] 
        <;> apply_fun (· 0 0) at h
        <;> rw [Complex.ext_iff] at h
        <;> simp_all
        <;> linarith
    | succ n' ih =>
      rw [cons_msb_tail P, cons_msb_tail Q] at h ⊢
      simp only [toCMatrix'_cons] at h
      admit


theorem mul_toCMatrix'_eq_toCMatrix'_mul_toCMatrix' (P Q : Pauli n) :
  (P * Q).toCMatrix' = P.toCMatrix' * Q.toCMatrix' := by
    induction n with
    | zero => 
      obtain hP | hP := of_length_zero P
        <;> obtain hQ | hQ := of_length_zero Q
        <;> simp_all [toCMatrix', phaseFlipsWith]
    | succ n' ih =>
      conv_rhs =>
        rw [
          Pauli.cons_msb_tail P, Pauli.cons_msb_tail Q,
          toCMatrix'_cons, toCMatrix'_cons,
          Matrix.reindex_apply, finCongr_symm,
          Matrix.reindex_apply, finCongr_symm,
          Matrix.submatrix_mul_equiv, ←Matrix.mul_kron_mul,
          toCMatrix'_bitsToMat_mul
        ]
      conv_lhs =>
        rw [
          Pauli.cons_msb_tail P, Pauli.cons_msb_tail Q,
          mul_cons
        ]
      split_ifs
        <;> simp only [
            toCMatrix'_neg, toCMatrix'_cons,
            ih P.tail Q.tail,
            Matrix.neg_kron,
            Matrix.submatrix_neg,
          ]
        <;> simp

theorem mul_assoc (P Q R : Pauli n) : P * Q * R = P * (Q * R) := by
  apply_fun toCMatrix'
  simp only [mul_toCMatrix'_eq_toCMatrix'_mul_toCMatrix']
  rw [←_root_.mul_assoc]
  apply toCMatrix'_injective


@[simp]
lemma one_toCMatrix : (1 : Pauli n).toCMatrix = 1 := by
  simp [toCMatrix]

@[simp]
lemma X_toCMatrix : X.toCMatrix = σx := by
  simp [X, toCMatrix, CMatrix.powBitVec]

@[simp]
lemma IY_toCMatrix : IY.toCMatrix = Complex.I • σy := by
  simp [IY, toCMatrix, CMatrix.powBitVec]

@[simp]
lemma Z_toCMatrix : Z.toCMatrix = σz := by
  simp [Z, toCMatrix, CMatrix.powBitVec]

example : 
  -IY * Z = X := by
    simp [IY, Z, X, phaseFlipsWith]

example : 
  IY * IY = -1 := by
    simp [IY, phaseFlipsWith, BitVec.weight, BitVec.foldr]


end Pauli
