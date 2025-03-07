import Quantumlib.Data.Gate.Equivs
import Quantumlib.Data.Gate.Pauli.Defs

import Mathlib.Data.Finsupp.Notation

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
lemma I_smul_σy_ne_1 : Complex.I • σy ≠ 1 := by
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
lemma σx_ne_I_smul_σy : σx ≠ Complex.I • σy := by
  intros h
  apply_fun (· 1 0) at h
  simp [σx, σy] at h

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
lemma I_smul_σy_ne_σz : Complex.I • σy ≠ σz := by
  intros h
  apply_fun (· 0 0) at h
  simp [σy, σz] at h

@[simp]
lemma neg_I_smul_σy_ne_σz : -(Complex.I • σy) ≠ σz := by
  intros h
  apply_fun (· 0 0) at h
  simp [σy, σz] at h

namespace UPauli

theorem cons_msb_tail (P : UPauli (n + 1)) :
  P = cons P.x.msb P.z.msb P.tail  := by 
    simp [cons, tail, BitVec.cons_msb_lsbs]

@[simp]
theorem cons_x (P : UPauli n) a b :
  (cons a b P).x = BitVec.cons a P.x := by 
    simp [cons]

@[simp]
theorem cons_z (P : UPauli n) a b :
  (cons a b P).z = BitVec.cons b P.z := by 
    simp [cons]

@[simp]
theorem cons_tail (P : UPauli n) a b :
  (cons a b P).tail = P := by 
    simp [cons, tail]

theorem tail_x (P : UPauli (n + 1)) :
  P.tail.x = P.x.lsbs := by 
    simp [tail]

theorem tail_z (P : UPauli (n + 1)) :
  P.tail.z = P.z.lsbs := by 
    simp [tail]

theorem one_def : (1 : UPauli n) = {
  x := 0,
  z := 0
} := by rfl

lemma one_weight : (1 : UPauli n).weight = 0 := by
  simp [one_def, weight]

theorem of_length_zero (P : UPauli 0) : P = 1 := by
  let ⟨x, z⟩ := P
  simp [one_def, x.eq_nil, z.eq_nil]

theorem phaseFlipsWith_cons (P Q : UPauli n) {a b c d} :
  (cons a b P).phaseFlipsWith (cons c d Q) ↔
    (b && c) ^^ P.phaseFlipsWith Q := by
      cases b <;> cases c
        <;> simp_all [phaseFlipsWith, Nat.succ_mod_two_eq_one_iff]


theorem mul_def (P Q : UPauli n) : P * Q = {
  x := P.x ^^^ Q.x,
  z := P.z ^^^ Q.z
} := by
  conv_lhs =>
    tactic => simp_rw [(· * ·), Mul.mul, UPauli.mul]

theorem mul_cons (P Q : UPauli n) {a b c d} : 
  cons a b P * cons c d Q =
  cons (a ^^ c) (b ^^ d) (P * Q) := by
    simp [mul_def, cons]

instance : MulOneClass (UPauli n) where
  one_mul := by simp [mul_def, one_def, phaseFlipsWith]
  mul_one := by simp [mul_def, one_def, phaseFlipsWith]

theorem mul_comm (P Q : UPauli n) : P * Q = Q * P := by
  simp [mul_def, BitVec.xor_comm]

@[simp]
theorem commutesWith_comm (P Q : UPauli n) : P.commutesWith Q ↔ Q.commutesWith P := by
  simp_rw [commutesWith, Bool.beq_comm]

instance : CommSemigroup (UPauli n) where
  mul_comm := by
    intros
    simp only [mul_def, mk.injEq]
    constructor <;> simp only [BitVec.xor_comm]

  mul_assoc := by
    simp [mul_def, BitVec.xor_assoc]

@[simp]
theorem one_phaseFlipsWith : phaseFlipsWith 1 P = false := by
  simp [phaseFlipsWith, mul_def, one_def]

@[simp]
theorem phaseFlipsWith_one : phaseFlipsWith P 1 = false := by
  simp [phaseFlipsWith, mul_def, one_def]

@[simp]
theorem mul_self (P : UPauli n) : P * P = 1 := by
  simp [mul_def, one_def]

lemma toCMatrix_cons {n} a b (P : UPauli n) : (cons a b P).toCMatrix = 
    (Matrix.reindex (finCongr <| by ring) (finCongr <| by ring)
    <| Matrix.kron (a := 2) (b := 2) 
        (toCMatrix.bitsToMat (a, b)) P.toCMatrix) := by
          simp [toCMatrix]

theorem toCMatrix_bitsToMat_injective :
  Function.Injective (toCMatrix.bitsToMat) := by
    simp only [Function.Injective]
    intro ⟨ax, az⟩ ⟨bx, bz⟩ h
    cases ax <;> cases az <;> cases bx <;> cases bz
      <;> simp_all [toCMatrix.bitsToMat]
      <;> first | simp_all | (symm at h; try simp_all)

  
@[simp]
lemma one_toCMatrix : (1 : UPauli n).toCMatrix = 1 := by
  induction n with
  | zero => simp [toCMatrix]
  | succ n' ih =>
    rw [show 1 = cons false false 1 by simp [cons, one_def], toCMatrix_cons, ih]
    simp [toCMatrix.bitsToMat]

@[simp]
lemma X_toCMatrix : X.toCMatrix = σx := by
  simp [X, toCMatrix, toCMatrix.bitsToMat]

@[simp]
lemma IY_toCMatrix : negIY.toCMatrix = -(Complex.I • σy) := by
  simp [negIY, toCMatrix, toCMatrix.bitsToMat]

@[simp]
lemma Z_toCMatrix : Z.toCMatrix = σz := by
  simp [Z, toCMatrix, toCMatrix.bitsToMat]

example : 
  negIY * Z = X := by
    simp [negIY, Z, X, mul_def]

example : 
  negIY * negIY = 1 := by
    rw [mul_self]


@[simps]
def equivProd (n : ℕ) : UPauli n ≃ BitVec n × BitVec n where
  toFun P := ⟨P.x, P.z⟩
  invFun p := ⟨p.1, p.2⟩
  left_inv := by rintro ⟨x, z⟩; rfl
  right_inv := by rintro ⟨x, z⟩; rfl

instance : Fintype (UPauli n) :=
  Fintype.ofEquiv (BitVec n × BitVec n) (equivProd n).symm

end UPauli

namespace PauliMap

theorem one_def : (1 : PauliMap n) = Finsupp.single 1 1 := rfl

theorem mul_def (pm qm : PauliMap n) :
  pm * qm = 
  pm.sum (fun P c₁ => qm.sum (fun Q c₂ =>
    let R := P * Q
    let neg := (-1) ^ (P.phaseFlipsWith Q).toNat
    Finsupp.single R (c₁ * c₂ * neg)))
 := rfl


noncomputable
instance : MulOneClass (PauliMap n) where
  one_mul := by
    simp [mul_def, one_def]
  mul_one := by
    simp [mul_def, one_def]

example : 
  (fun₀ 
    | UPauli.X => (1 : ℂ)) * 
  (fun₀
    | UPauli.X => (1 : ℂ)  
    ) =
  fun₀
    | 1 => (1 : ℂ) := by 
      simp [mul_def, UPauli.X, UPauli.phaseFlipsWith]

example : 
  (fun₀ 
    | UPauli.X => (1 : ℂ)) * 
  (fun₀
    | UPauli.X => 1
    | 1 => 1
    ) =
  fun₀
    | UPauli.X => 1
    | 1 => (1 : ℂ) := by 
      simp [mul_def, Finsupp.sum, Finsupp.update, Finsupp.single]
      rw [@Finset.sum_insert, Finset.sum_singleton]
      · simp [UPauli.phaseFlipsWith, UPauli.X]
        simp [UPauli.one_def]
        ext P
        fin_cases P <;> simp [UPauli.equivProd, EquivLike.toEquiv]
      · simp [UPauli.one_def, UPauli.X]

end PauliMap
