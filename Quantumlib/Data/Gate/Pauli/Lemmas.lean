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

@[simp]
theorem neg_c (P : UPauli n) :
  (-P).c = -P.c := by
    simp [(-·), Pauli.neg]

@[simp]
theorem neg_x (P : UPauli n) :
  (-P).x = P.x := by
    simp [(-·), Pauli.neg]

@[simp]
theorem neg_z (P : UPauli n) :
  (-P).z = P.z := by
    simp [(-·), Pauli.neg]

@[simp]
theorem cons_c (P : UPauli n) a b :
  (cons a b P).c = P.c := by 
    simp [cons]
  

theorem tail_neg (P : UPauli (n + 1)) :
  (-P).tail = -P.tail := by 
    simp [tail, (-·), neg]

@[simp]
theorem neg_def (P : UPauli n) : -P = {P with c := -P.c} := rfl

@[simp]
theorem neg_weight (P : UPauli n) : (-P).weight = P.weight := rfl

theorem neg_mul (P Q : UPauli n) : -P * Q = -(P * Q) := by
  simp [phaseFlipsWith]

@[simp]
theorem mul_neg (P Q : UPauli n) : P * -Q = -(P * Q) := by
  simp [phaseFlipsWith]

@[simp]
theorem neg_one_mul (P : UPauli n) : -1 * P = -P := by
  rw [neg_mul, one_mul]

@[simp]
theorem smul_def (c : ℂ) (P : UPauli n) : c • P = {P with c := c * P.c} := rfl 

@[simp]
theorem neg_one_smul (P : UPauli n) : (-1 : ℂ) • P = -P := by
  simp

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

@[simp]
theorem one_def : (1 : UPauli n) = {
  x := 0,
  z := 0
} := by rfl

@[simp]
lemma one_weight : (1 : UPauli n).weight = 0 := by
  simp [weight]

theorem of_length_zero (P : UPauli 0) : P = 1 := by
  let ⟨x, z⟩ := P
  simp [x.eq_nil, z.eq_nil]

theorem phaseFlipsWith_cons (P Q : UPauli n) {a b c d} :
  (cons a b P).phaseFlipsWith (cons c d Q) ↔
    (b && c) ^^ P.phaseFlipsWith Q := by
      cases b <;> cases c
        <;> simp_all [phaseFlipsWith, Nat.succ_mod_two_eq_one_iff]

@[simp]
theorem mul_def (P Q : UPauli n) : P * Q = {
  x := P.x ^^^ Q.x,
  z := P.z ^^^ Q.z
} := by
  conv =>
    lhs
    tactic => simp_rw [(· * ·), Mul.mul, UPauli.mul]

theorem mul_cons (P Q : UPauli n) {a b c d} : 
  cons a b P * cons c d Q =
  cons (a ^^ c) (b ^^ d) (P * Q) := by
    simp [cons]

@[simp]
theorem mul_one (P : UPauli n) : P * 1 = P := by
  simp [phaseFlipsWith]

@[simp]
theorem one_mul (P : UPauli n) : 1 * P = P := by
  simp [phaseFlipsWith]

@[simp]
theorem commutesWith_comm (P Q : UPauli n) : P.commutesWith Q ↔ Q.commutesWith P := by
  simp_rw [commutesWith, Bool.beq_comm]

theorem mul_comm (P Q : UPauli n) : P * Q = Q * P := by
  simp only [mul_def, mk.injEq]
  constructor <;> simp only [BitVec.xor_comm]

@[simp]
theorem one_phaseFlipsWith : phaseFlipsWith 1 P = false := by
  simp [phaseFlipsWith]

@[simp]
theorem phaseFlipsWith_one : phaseFlipsWith P 1 = false := by
  simp [phaseFlipsWith]

@[simp]
theorem mul_self (P : UPauli n) : P * P = 1 := by
  simp

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

lemma toCMatrix_bitsToMat_mul {a b c d} :
  toCMatrix.bitsToMat (a, b) * toCMatrix.bitsToMat (c, d)
  = let r := toCMatrix.bitsToMat (a ^^ c, b ^^ d)
    if b && c then r else -r := by
      cases a <;> cases b <;> cases c <;> cases d
        <;> simp [toCMatrix.bitsToMat, smul_smul]


theorem mul_toCMatrix_eq_toCMatrix_mul_toCMatrix (P Q : UPauli n) :
  (P * Q).toCMatrix = P.toCMatrix * Q.toCMatrix := by
    induction n with
    | zero => 
      simp [toCMatrix]
    | succ n' ih =>
      conv_rhs =>
        rw [
          UPauli.cons_msb_tail P, UPauli.cons_msb_tail Q,
          toCMatrix_cons, toCMatrix_cons,
          Matrix.reindex_apply, finCongr_symm,
          Matrix.reindex_apply, finCongr_symm,
          Matrix.submatrix_mul_equiv, ←Matrix.mul_kron_mul,
          toCMatrix_bitsToMat_mul
        ]
      conv_lhs =>
        rw [
          UPauli.cons_msb_tail P, UPauli.cons_msb_tail Q,
          mul_cons
        ]
      rw [
        toCMatrix_cons, ih P.tail Q.tail,
      ]
      simp

      split_ifs
        <;> simp only [
            toCMatrix_cons,
            ih P.tail Q.tail,
            Matrix.neg_kron,
            Matrix.submatrix_neg,
          ]
        <;> simp

theorem mul_assoc (P Q R : UPauli n) : P * Q * R = P * (Q * R) := by
  simp [BitVec.xor_assoc]
  
@[simp]
lemma one_toCMatrix : (1 : UPauli n).toCMatrix = 1 := by
  induction n
  case zero => simp [toCMatrix]
  case succ n' ih =>
    rw [show 1 = cons false false 1 by simp [cons], toCMatrix_cons, ih]
    simp [toCMatrix.bitsToMat]

@[simp]
lemma X_toCMatrix : X.toCMatrix = σx := by
  simp [X, toCMatrix, toCMatrix.bitsToMat]

@[simp]
lemma IY_toCMatrix : IY.toCMatrix = Complex.I • σy := by
  simp [IY, toCMatrix, toCMatrix.bitsToMat]

@[simp]
lemma Z_toCMatrix : Z.toCMatrix = σz := by
  simp [Z, toCMatrix, toCMatrix.bitsToMat]

example : 
  IY * Z = X := by
    simp [IY, Z, X]

example : 
  IY * IY = 1 := by
    rw [mul_self]

end UPauli

namespace PauliMap

open Lean (RBMap)

@[simp]
theorem one_def : (1 : PauliMap n) = RBMap.ofList [1] := rfl

@[simp]
theorem add_def (pm qm : PauliMap n) : 
  pm + qm = pm.mergeBy (fun _ => (· + ·)) qm := rfl

@[simp]
theorem smul_def (a : ℂ) (pm : PauliMap n) : 
  a • pm = pm.filterMap (fun _ c => some (a * c)) := rfl

@[simp]
theorem mul_def (pm qm : PauliMap n) :
  pm * qm = pm.fold (init := ∅) fun acc' P c₁ =>
    qm.fold (init := acc') fun acc Q c₂ =>
      let R := P * Q
      let factor := (-1 : ℂ) ^ (UPauli.phaseFlipsWith P Q).toNat * c₁ * c₂
      match acc.find? R with
      | none   => acc.insert R factor
      | some c => acc.insert R (c + factor) := rfl

@[simp]
theorem one_mul {pm : PauliMap n} : 1 * pm = pm := by
  sorry

end PauliMap
