import Quantumlib.Data.Fin
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
lemma σz_ne_1 : σz ≠ 1 := by
  intros h
  apply_fun (· 1 1) at h
  simp [σz, eq_comm] at h

@[simp]
lemma σx_ne_σy : σx ≠ σy := by
  intros h
  apply_fun (· 1 0) at h
  apply_fun Complex.re at h
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

namespace Pauli

theorem one_def : (1 : Pauli n) = {
  x := 0,
  z := 0
} := by rfl

@[simp]
theorem neg_eq {P : Pauli n} : -P = P.addPhase 2 := by rfl

theorem mul_def (P Q : Pauli n) : P * Q = 
  {
    m := P.m + Q.m + 2 * (P.x.dot Q.z),
    z := P.z ^^^ Q.z,
    x := P.x ^^^ Q.x,
  }
 := by
  conv_lhs =>
    tactic => simp_rw [(· * ·), Mul.mul, Pauli.mul]
    unfold phaseFlipCounts
  simp

theorem cons_msb_tail (P : Pauli (n + 1)) :
  P = cons P.z.msb P.x.msb P.tail  := by 
    simp [cons, tail, BitVec.cons_msb_lsbs]


theorem of_length_zero (P : Pauli 0) : ∃ m, P = {m := m, x := 0, z := 0} := by
  let ⟨m, x, z⟩ := P
  have hx := x.eq_nil
  have hz := z.eq_nil
  use m
  subst_vars
  rfl

@[simp]
theorem cons_z (P : Pauli n) a b :
  (cons a b P).z = BitVec.cons a P.z := by 
    simp [cons]

@[simp]
theorem cons_x (P : Pauli n) a b :
  (cons a b P).x = BitVec.cons b P.x := by 
    simp [cons]

@[simp]
theorem cons_m (P : Pauli n) a b :
  (cons a b P).m = P.m := by 
    simp [cons]

@[simp]
theorem cons_tail (P : Pauli n) a b :
  (cons a b P).tail = P := by 
    simp [cons, tail]

@[simp]
theorem tail_z (P : Pauli (n + 1)) :
  P.tail.z = P.z.lsbs := by 
    simp [tail]

@[simp]
theorem tail_x (P : Pauli (n + 1)) :
  P.tail.x = P.x.lsbs := by 
    simp [tail]

@[simp]
theorem tail_m (P : Pauli (n + 1)) :
  P.tail.m = P.m := by 
    simp [tail]

@[simp]
lemma one_weight : (1 : Pauli n).weight = 0 := by
  simp [one_def, weight]

@[simp]
lemma one_z : (1 : Pauli n).z = 0 := by
  simp [one_def]

@[simp]
lemma one_x : (1 : Pauli n).x = 0 := by
  simp [one_def]

@[simp]
lemma one_m : (1 : Pauli n).m = 0 := by
  simp [one_def]

@[simp]
theorem cons_mul_cons (P Q : Pauli n) : cons a b P * cons c d Q =
  addPhase (2 * (b && c).toNat) (cons (a ^^ c) (b ^^ d) (P * Q)) := by 
    simp only [mul_def, cons_m, Fin.isValue, cons_z, cons_x, BitVec.cons_dot_cons, Nat.cast_add,
      BitVec.cons_xor_cons, addPhase, mk.injEq, and_self, and_true]
    ring

section addPhase

@[simp]
theorem addPhase_x (P : Pauli n) {m} :
  (P.addPhase m).x = P.x := by
    simp [addPhase]

@[simp]
theorem addPhase_z (P : Pauli n) {m} :
  (P.addPhase m).z = P.z := by
    simp [addPhase]

@[simp]
theorem addPhase_m (P : Pauli n) {m} :
  (P.addPhase m).m = P.m + m := by
    simp [addPhase]

-- TODO: Is this the right direction?
@[simp]
theorem addPhase_cons (P : Pauli n) {m} : addPhase m (cons a b P) = cons a b (addPhase m P) := by
  simp [addPhase, cons]

@[simp]
theorem addPhase_addPhase (P : Pauli n) {l m} : addPhase l (addPhase m P) = addPhase (l + m) P := by
  simp only [addPhase, add_assoc, mk.injEq, add_right_inj, and_self, and_true]
  simp [add_comm]

@[simp]
theorem addPhase_mul (P : Pauli n) {m} : addPhase m P * Q = addPhase m (P * Q) := by
  simp only [addPhase, mul_def, Fin.isValue, mk.injEq, and_self, and_true]
  ring

@[simp]
theorem mul_addPhase (P : Pauli n) {m} : P * addPhase m Q = addPhase m (P * Q) := by
  simp only [addPhase, mul_def, Fin.isValue, mk.injEq, and_self, and_true]
  ring

@[simp]
theorem addPhase_zero (P : Pauli n) : addPhase 0 P = P := by 
  simp [addPhase]

@[simp]
theorem addPhase_lit {m} {x z : BitVec n} :
  addPhase m {m := m₀, x := x, z := z} = {m := m₀ + m, x := x, z := z} := by 
    simp [addPhase]

end addPhase

section neg

@[simp]
theorem neg_x (P : Pauli n) :
  (-P).x = P.x := by
    simp

@[simp]
theorem neg_z (P : Pauli n) :
  (-P).z = P.z := by
    simp

@[simp]
theorem neg_m (P : Pauli n) :
  (-P).m = P.m + 2 := by
    simp

-- TODO: Is this the right direction?
@[simp]
theorem neg_cons (P : Pauli n) : -(cons a b P) = cons a b (-P) := by
  simp

instance : InvolutiveNeg (Pauli n) := ⟨by simp⟩
instance : HasDistribNeg (Pauli n) := ⟨by simp, by simp⟩

end neg

section zeroed

@[simp]
theorem zeroed_z (P : Pauli n) : P.zeroed.z = P.z := by
  simp [zeroed]

@[simp]
theorem zeroed_x (P : Pauli n) : P.zeroed.x = P.x := by
  simp [zeroed]

@[simp]
theorem zeroed_m (P : Pauli n) : P.zeroed.m = 0 := by
  simp [zeroed]

@[simp]
theorem zeroed_eq_self_iff (P : Pauli n) : P.zeroed = P ↔ P.m = 0 := by
  simp only [zeroed]
  rw [mk.injEq]
  simp_all only [and_self, and_true]
  tauto

@[simp]
theorem addPhase_three_eq_zeroed_iff (P : Pauli n) :
  P.addPhase 3 = P.zeroed ↔ P.m = 1 := by
    simp only [zeroed]
    rw [mk.injEq]
    simp_all only [addPhase_m, addPhase_x, addPhase_z, and_self, and_true]
    constructor <;> intros <;> omega

@[simp]
theorem addPhase_two_eq_zeroed_iff (P : Pauli n) :
  P.addPhase 2 = P.zeroed ↔ P.m = 2 := by
    simp only [zeroed]
    rw [mk.injEq]
    simp_all only [addPhase_m, addPhase_x, addPhase_z, and_self, and_true]
    constructor <;> intros <;> omega

@[simp]
theorem addPhase_one_eq_zeroed_iff (P : Pauli n) :
  P.addPhase 1 = P.zeroed ↔ P.m = 3 := by
    simp only [zeroed]
    rw [mk.injEq]
    simp_all only [addPhase_m, addPhase_x, addPhase_z, and_self, and_true]
    constructor <;> intros <;> omega

end zeroed 

instance : CancelMonoid (Pauli n) where
  mul_assoc := by
    intros P Q R
    induction n with
    | zero =>
      let ⟨x, P'⟩ := of_length_zero P
      let ⟨y, Q'⟩ := of_length_zero Q
      simp_all [add_assoc, mul_def]
    | succ n' ih =>
      rw [cons_msb_tail P, cons_msb_tail Q, cons_msb_tail R]
      simp only [cons_mul_cons, Fin.isValue, addPhase_cons, Bool.bne_assoc, addPhase_mul, ih,
        addPhase_addPhase, mul_addPhase]
      congr 2
      cases Q.x.msb
        <;> cases Q.z.msb
        <;> cases R.z.msb
        <;> cases P.x.msb
        <;> simp
  mul_one := by 
    intros P
    simp [mul_def, one_def]
  one_mul := by 
    intros P
    simp [mul_def, one_def]
  mul_left_cancel := by
    intros P Q R
    simp only [mul_def, Fin.isValue, mk.injEq, BitVec.xor_right_inj, and_imp]
    intros h hz hx
    rw [hz] at h
    simp only [Fin.isValue, add_left_inj, add_right_inj] at h
    rw [mk.injEq]
    simp_all
  mul_right_cancel := by
    intros P Q R
    simp only [mul_def, Fin.isValue, mk.injEq, BitVec.xor_left_inj, and_imp]
    intros h hz hx
    rw [hx] at h
    simp only [Fin.isValue, add_left_inj, add_right_inj] at h
    rw [mk.injEq]
    simp_all

instance : Group (Pauli n) where
  inv P := P.addPhase (-(2 * (P.m + P.x.dot P.z)))
  inv_mul_cancel := by
    intros
    simp only [
      Fin.isValue, mul_def, addPhase_m, addPhase_x,
      addPhase_z, BitVec.xor_self, one_def,
      BitVec.ofNat_eq_ofNat, mk.injEq, and_self, and_true]
    ring

@[simp]
theorem inv_z (P : Pauli n) : P⁻¹.z = P.z := by
  simp [(·⁻¹)]

@[simp]
theorem inv_x (P : Pauli n) : P⁻¹.x = P.x := by
  simp [(·⁻¹)]

@[simp]
theorem inv_m (P : Pauli n) : P⁻¹.m = -(P.m + P.phaseFlipCounts P) := by
  simp only [(·⁻¹), phaseFlipCounts, addPhase]
  ring_nf
  norm_cast

theorem mul_inv (P Q : Pauli n) :
  P * Q⁻¹ = (P * Q).addPhase (-(2 * (Q.m + (Q.x.dot Q.z)))) := by
    simp only [mul_def, inv_m, phaseFlipCounts, Nat.cast_mul, Nat.cast_ofNat, Fin.isValue,
      neg_add_rev, Fin.add_neg, inv_z, inv_x, addPhase_lit, mk.injEq, and_self, and_true]
    ring

theorem inv_mul (P Q : Pauli n) :
  P⁻¹ * Q = (P * Q).addPhase (-(2 * (P.m + (P.x.dot P.z)))) := by
    simp only [mul_def, inv_m, phaseFlipCounts, Nat.cast_mul, Nat.cast_ofNat, Fin.isValue,
      neg_add_rev, Fin.add_neg, inv_x, inv_z, addPhase_lit, mk.injEq, and_self, and_true]
    ring

theorem commutesWith_comm (P Q : Pauli n) : P.commutesWith Q ↔ Q.commutesWith P := by
  simp [commutesWith, Bool.beq_comm]

lemma commute_of_commutesWith (P Q : Pauli n) : P.commutesWith Q → Commute P Q := by
  intros h
  simp only [commutesWith, phaseFlipCounts] at h
  simp_all [commute_iff_eq, mul_def, h, add_comm, BitVec.xor_comm]

lemma commutesWith_of_commute (P Q : Pauli n) : Commute P Q → P.commutesWith Q := by
  intros h
  rw [commute_iff_eq] at h
  unfold commutesWith
  simp_all [phaseFlipCounts, Nat.cast_mul, Nat.cast_ofNat, Fin.isValue, mul_def, add_comm]

theorem commutesWith_iff (P Q : Pauli n) : P.commutesWith Q ↔ Commute P Q :=
  ⟨commute_of_commutesWith P Q, commutesWith_of_commute P Q⟩
  

theorem mul_anticomm_of_not_commutesWith (P Q : Pauli n) :
  ¬P.commutesWith Q → P * Q = -(Q * P) := by
    intros h
    simp_all [commutesWith, mul_def, phaseFlipCounts, BitVec.xor_comm]

    generalize hm₁ : (P.x.dot Q.z : Fin 4) = m₁
    generalize hm₂ : (Q.x.dot P.z : Fin 4) = m₂
    rw [hm₁, hm₂] at h
    fin_cases m₁ <;> fin_cases m₂ <;> simp_all <;> omega


@[simp]
theorem commutesWith_one (P : Pauli n) : P.commutesWith 1 := by
  simp [commutesWith, phaseFlipCounts]

@[simp]
theorem one_commutesWith (P : Pauli n) : (1 : Pauli n).commutesWith P := by
  simp [commutesWith, phaseFlipCounts]

theorem pow_two (P : Pauli n) :
  P ^ 2 = (1 : Pauli n).addPhase (2 * (P.m + P.z.dot P.x)) := by
    simp [_root_.pow_two, mul_def, addPhase, one_def, BitVec.dot_comm, two_mul]
    ring

lemma toCMatrix_cons {n} a b (P : Pauli n) : (cons a b P).toCMatrix = 
    (Matrix.reindex (finCongr <| by ring) (finCongr <| by ring)
    <| Matrix.kron (a := 2) (b := 2) 
        (toCMatrix.bitsToMat (a, b)) P.toCMatrix) := by
          simp [toCMatrix]

@[simp]
theorem toCMatrix_neg (P : Pauli n) :
  (-P).toCMatrix = -P.toCMatrix := by
    induction n with
    | zero =>
      obtain ⟨_, h⟩ := of_length_zero P
      simp [h, toCMatrix, Fin.val_add,
            ←Complex.neg_I_pow_eq_pow_mod, pow_add]
    | succ n' ih => 
      conv_lhs =>
        rw [cons_msb_tail P]
        simp only [toCMatrix, cons_tail]
      simp [-neg_eq, ih, Matrix.submatrix_neg, toCMatrix]


lemma toCMatrix_bitsToMat_mul :
  toCMatrix.bitsToMat (a, b) * toCMatrix.bitsToMat (c, d)
  = let r := toCMatrix.bitsToMat (a ^^ c, b ^^ d)
    if b && c then -r else r := by
      cases a <;> cases b <;> cases c <;> cases d
        <;> simp [toCMatrix.bitsToMat, smul_smul]


theorem mul_toCMatrix_eq_toCMatrix_mul_toCMatrix (P Q : Pauli n) :
  (P * Q).toCMatrix = P.toCMatrix * Q.toCMatrix := by
    induction n with
    | zero => 
      let ⟨x, hP⟩ := of_length_zero P
      let ⟨y, hQ⟩ := of_length_zero Q
      subst_vars
      simp [toCMatrix, mul_def, smul_smul, ←pow_add, Fin.val_add,
            ←Complex.neg_I_pow_eq_pow_mod, add_comm]
    | succ n' ih =>

      conv_rhs =>
        rw [
          Pauli.cons_msb_tail P, Pauli.cons_msb_tail Q,
          toCMatrix_cons, toCMatrix_cons,
          Matrix.reindex_apply, finCongr_symm,
          Matrix.reindex_apply, finCongr_symm,
          Matrix.submatrix_mul_equiv, ←Matrix.mul_kron_mul,
        ]
      conv_lhs =>
        rw [
          Pauli.cons_msb_tail P, Pauli.cons_msb_tail Q,
          cons_mul_cons
        ]
      rw [toCMatrix_bitsToMat_mul]
      simp_all only [Fin.isValue, addPhase_cons, Bool.and_eq_true, Bool.bne_true, Bool.true_bne]
      split_ifs
      next
        h =>
        simp_all only [Bool.bne_true, Bool.true_bne, Fin.isValue, Bool.and_self, Bool.toNat_true, Nat.cast_one,
          mul_one, Matrix.neg_kron]
        obtain ⟨left, right⟩ := h
        simp [←neg_eq, toCMatrix_cons, Matrix.neg_kron, ←ih]
      next h =>
        simp_all only [not_and, Bool.not_eq_true, Fin.isValue]
        rw [show (P.x.msb && Q.z.msb).toNat = 0 by simp_all]
        simp [toCMatrix_cons, ←ih]


@[simp]
lemma one_toCMatrix : (1 : Pauli n).toCMatrix = 1 := by
  induction n with
  | zero => simp [toCMatrix, one_def]
  | succ n' ih =>
    rw [show 1 = cons false false 1 by simp [cons, one_def], toCMatrix_cons, ih]
    simp [toCMatrix.bitsToMat]

@[simp]
lemma X_toCMatrix : X.toCMatrix = σx := by
  simp [X, toCMatrix, toCMatrix.bitsToMat]

@[simp]
lemma Y_toCMatrix : Y.toCMatrix = σy := by
  simp [Y, toCMatrix, toCMatrix.bitsToMat, smul_smul]

@[simp]
lemma iY_toCMatrix : iY.toCMatrix = Complex.I • σy := by
  simp [iY, toCMatrix, toCMatrix.bitsToMat]

@[simp]
lemma Z_toCMatrix : Z.toCMatrix = σz := by
  simp [Z, toCMatrix, toCMatrix.bitsToMat]

@[simps]
def equivProd (n : ℕ) : Pauli n ≃ Fin 4 × BitVec n × BitVec n where
  toFun P := ⟨P.m, P.z, P.x⟩
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv := by rintro ⟨m, z, x⟩; rfl
  right_inv := by rintro ⟨m, z, x⟩; rfl

instance : Fintype (Pauli n) :=
  Fintype.ofEquiv (Fin 4 × BitVec n × BitVec n) (equivProd n).symm

@[simp]
lemma X_pow_2 : X ^ 2 = 1 := rfl
@[simp]
lemma Y_pow_2 : Y ^ 2 = 1 := rfl
@[simp]
lemma Z_pow_2 : Z ^ 2 = 1 := rfl

end Pauli

namespace PauliMap

@[simp]
theorem normalized.f_zero (P : Pauli n) : normalized.f P 0 = 0 := by 
  simp [f]

@[simp]
theorem normalized_neg : normalized (-Pm) = -normalized Pm := by
  simp only [normalized]
  rw [Finsupp.sum_neg_index (by simp)]
  simp only [Finsupp.single_neg, Fin.isValue,
             neg_neg, ←Finsupp.sum_neg]
  congr; ext
  unfold normalized.f
  simp only [mul_neg, Finsupp.single_neg, Finsupp.coe_neg, Pi.neg_apply]
  rfl

@[simp]
theorem normalized_zero : normalized (0 : PauliMap n) = 0 := by
  rfl

@[simp] 
theorem normalized_single : normalized (Finsupp.single P a) =
  Finsupp.single P.zeroed (P.evalPhase * a) := by 
  simp only [normalized]
  unfold normalized.f
  simp

@[simp]
theorem normalized_add {Pm₁ Pm₂ : PauliMap n} :
  normalized (Pm₁ + Pm₂) = normalized Pm₁ + normalized Pm₂ := by
    simp only [normalized]
    rw [Finsupp.sum_add_index'
        (by simp)
        (by intros; unfold normalized.f; simp [mul_add, add_comm])]

theorem m_eq_0_of_in_normalized_support {Pm : PauliMap n} {P : Pauli n} :
  (P ∈ (PauliMap.normalized Pm).support) → P.m = 0 := by
    intros h
    rw [Finsupp.mem_support_iff] at h
    induction Pm using Finsupp.induction generalizing P
    case zero =>
      simp [normalized] at h
    case single_add P₁ a Pm' h₁ h₂ ih =>
      rw [normalized_add, normalized_single,
          Finsupp.add_apply, Finsupp.single_apply] at h
      by_cases heq : P₁.zeroed = P
      · rw [if_pos heq] at h
        simp [←heq]
      · rw [if_neg heq] at h
        simp_all

end PauliMap
