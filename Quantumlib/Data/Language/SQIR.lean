import Quantumlib.Data.Language.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose


open Real


open Matrix

open MatrixSemantics

open Kronecker in
def Matrix.bvkron [Mul R] {n m o p} (A : Matrix (BitVec n) (BitVec m) R)
  (B : Matrix (BitVec o) (BitVec p) R) : Matrix (BitVec (n + o)) (BitVec (m + p)) R :=
  (A ⊗ₖ B).reindex BitVec.addEquiv.symm BitVec.addEquiv.symm

def BitVec.castEquiv {n m} (Hn : n = m) : BitVec n ≃ BitVec m :=
  ⟨.cast Hn, .cast Hn.symm, fun i => by simp, fun i => by simp⟩

@[simp]
lemma BitVec.castEquiv_apply {n m} (Hn : n = m) (v : BitVec n) :
  BitVec.castEquiv Hn v = v.cast Hn := rfl

@[simp]
lemma BitVec.castEquiv_symm_apply {n m} (Hn : n = m) (v : BitVec m) :
  (BitVec.castEquiv Hn).symm v = v.cast Hn.symm := rfl

@[simp]
lemma BitVec.castEquiv_id {n} (Hn : n = n) : BitVec.castEquiv Hn = Equiv.refl _ := by {
  ext; simp
}

def Matrix.reindex₂ {n m α} (e : n ≃ m) : Matrix n n α ≃ Matrix m m α :=
  reindex e e

lemma Fin.to_castAdd_natAdd {n} (i : Fin n) :
  i = .cast (by omega) (((0 : Fin 1).natAdd i).castAdd (n - (i + 1))) := by {
  ext; simp
}

lemma gen_pad_matrix_cast [Zero R] {n n' n'' m m' m''}
  (v : Vector (Fin n') n) (u : Vector (Fin m') m)
  (U : Matrix (BitVec n) (BitVec m) R) (eqn : n' = n'') (eqm : m' = m'') :
  gen_pad_matrix (v.map (.cast eqn)) (u.map (.cast eqm)) U =
  (gen_pad_matrix v u U).reindex (BitVec.castEquiv eqn) (BitVec.castEquiv eqm) := by {
  subst n'' m''
  simp
}

lemma BitVec.vectorNotIndexed_id {n} (v : BitVec n) :
  v.vectorNotIndexed (.ofFn id) = [] := by {
  unfold vectorNotIndexed
  simp only [List.map_eq_nil_iff]
  unfold Vector.listNotIndexed
  simp
}

lemma BitVec.vectorReindex_id {n} (v : BitVec n) :
  v.vectorReindex (.ofFn id) = v := by {
  unfold vectorReindex
  ext i hi
  simp
}

lemma gen_pad_matrix_id [Zero R] {n}
  (U : Matrix (BitVec n) (BitVec n) R) :
  gen_pad_matrix (.ofFn id) (.ofFn id) U = U := by {
  ext i j
  unfold gen_pad_matrix
  simp [BitVec.vectorNotIndexed_id, BitVec.vectorReindex_id]
}


lemma gen_pad_matrix_id_1 [Zero R] (v u : Vector (Fin 1) 1)
  (U : Matrix (BitVec 1) (BitVec 1) R) :
  gen_pad_matrix v u U = U := by {
  have Hv : v = .ofFn id := by ext; simp
  have Hu : u = .ofFn id := by ext; simp
  simp [Hv, Hu, gen_pad_matrix_id]
}

lemma pad_matrix_one [Semiring R] {n} (v : NoDupVector (Fin n) 1)
  (U : Matrix (BitVec 1) (BitVec 1) R) :
  pad_matrix v U =
    let i := v.val[0]'Nat.zero_lt_one
    (bvkron
    (bvkron (1 : Matrix (BitVec i) (BitVec i) R) U)
    (1 : Matrix (BitVec (n - (i + 1))) (BitVec (n - (i + 1))) R)).reindex₂
    (BitVec.castEquiv (by omega)) := by {
  obtain ⟨v, Hv⟩ := v
  have ⟨xs, Hxs⟩ := v.size_eq_one
  subst v
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero]
  unfold pad_matrix
  simp only
  trans
  rw [xs.to_castAdd_natAdd]
  rw [← Vector.map_singleton, gen_pad_matrix_cast]
  congr 1
  rw [← Vector.map_singleton, gen_pad_matrix_whiskerR]
  congr 2
  rw [← Vector.map_singleton, gen_pad_matrix_whiskerL]
  congr 2
  apply gen_pad_matrix_id_1
}

@[simp]
lemma bvkron_1_0_l [Semiring R] (U : Matrix (BitVec n) (BitVec m) R) :
  bvkron (1 : Matrix (BitVec 0) (BitVec 0) R) U =
    U.reindex (BitVec.castEquiv n.zero_add.symm) (BitVec.castEquiv m.zero_add.symm) := by {
  unfold bvkron
  simp only [reindex_apply, Equiv.symm_symm]
  ext i j
  simp only [submatrix_apply, kroneckerMap_apply, BitVec.castEquiv_symm_apply]
  simp only [BitVec.addEquiv, BitVec.append_zero_width, Equiv.coe_fn_mk]
  rw [Matrix.one_apply]
  rw [ite_cond_eq_true]
  · rw [one_mul]
    congr 1
    · ext k hk
      simp only [BitVec.getElem_extractLsb', zero_add, BitVec.getElem_cast]
      rw [BitVec.getLsbD_eq_getElem (n.zero_add.symm ▸ hk)]
    · ext k hk
      simp only [BitVec.getElem_extractLsb', zero_add, BitVec.getElem_cast]
      rw [BitVec.getLsbD_eq_getElem (m.zero_add.symm ▸ hk)]
  · simp only [eq_iff_iff, iff_true]
    ext i; omega
}

lemma bvkron_1_0_r [Semiring R] (U : Matrix (BitVec n) (BitVec m) R) :
  bvkron U (1 : Matrix (BitVec 0) (BitVec 0) R) =
    U := by {
  unfold bvkron
  simp only [Nat.add_zero, reindex_apply, Equiv.symm_symm]
  ext i j
  simp only [submatrix_apply, kroneckerMap_apply]
  simp only [BitVec.addEquiv, Nat.add_zero, BitVec.setWidth_eq, BitVec.extractLsb'_eq_zero,
    BitVec.zero_width_append, BitVec.cast_cast, BitVec.cast_eq, Equiv.coe_fn_mk]
  rw [Matrix.one_apply]
  rw [ite_cond_eq_true]
  · rw [mul_one]
  · simp only [eq_iff_iff, iff_true]
    ext i; omega
}

@[simp]
lemma bvkron_smul_l [Semiring R] (r : R) (A : Matrix (BitVec n) (BitVec m) R)
  (B : Matrix (BitVec n) (BitVec m) R) :
  bvkron (r • A) B = r • bvkron A B := by {
  ext i j
  simp [bvkron, mul_assoc]
}

@[simp]
lemma bvkron_smul_r [CommSemiring R] (r : R) (A : Matrix (BitVec n) (BitVec m) R)
  (B : Matrix (BitVec n) (BitVec m) R) :
  bvkron A (r • B) = r • bvkron A B := by {
  ext i j
  simp only [bvkron, reindex_apply, Equiv.symm_symm, submatrix_apply, kroneckerMap_apply,
    smul_apply, smul_eq_mul]
  ring
}

@[simp]
lemma bvkron_mul_bvkron {n m o p q r} [CommSemiring R]
  (A : Matrix (BitVec n) (BitVec m) R) (B : Matrix (BitVec m) (BitVec o) R)
  (C : Matrix (BitVec p) (BitVec q) R) (D : Matrix (BitVec q) (BitVec r) R) :
  bvkron A C * bvkron B D =
  bvkron (A * B) (C * D) := by {
  unfold bvkron
  simp only [reindex_apply, Equiv.symm_symm, submatrix_mul_equiv]
  rw [Matrix.mul_kronecker_mul]
}

lemma Matrix.reindex_mul {n m o n' m' o'}
  [Fintype m] [Fintype m'] [CommSemiring R]
  (en : n ≃ n') (em : m ≃ m') (eo : o ≃ o')
  (A : Matrix n m R) (B : Matrix m o R) :
  A.reindex en em * B.reindex em eo =
  (A * B).reindex en eo := by {
  simp
}

def ofFinMx {α} {n m : ℕ} (M : Matrix (Fin (2^n)) (Fin (2^m)) α) : Matrix (BitVec n) (BitVec m) α :=
  M.reindex (BitVec.equivFin.toEquiv).symm (BitVec.equivFin.toEquiv).symm

@[simp]
lemma Matrix.ofFinMx_mul [CommSemiring R] {n m o}
  (A B : Matrix (Fin _) (Fin _) R) :
  @ofFinMx R n m A * @ofFinMx R m o B = @ofFinMx R n o (A * B) :=
  Matrix.reindex_mul _ _ _ _ _


@[simp]
lemma Matrix.ofFinMx_sub [Sub R] {n m}
  (A B : Matrix (Fin (2^n)) (Fin (2^m)) R) :
  @ofFinMx R n m A - @ofFinMx R n m B = @ofFinMx R n m (A - B) := by {
  rfl
}

lemma Matrix.smul_submatrix [SMul R α] {n m n' m'}
  (r : R) (A : Matrix n m α) (en : n' → n) (em : m' → m) :
  r • A.submatrix en em = (r • A).submatrix en em := by simp [Matrix.submatrix_smul]

lemma bvkron_neg_l [Ring R] {n m o p} (A B : Matrix _ _ R) :
  @bvkron R  _ n m o p (-A) B = - bvkron A B := by {
  ext i j
  simp [bvkron]
}

lemma bvkron_neg_r [Ring R] {n m o p} (A B : Matrix _ _ R) :
  @bvkron R  _ n m o p (A) (- B) = - bvkron A B := by {
  ext i j
  simp [bvkron]
}


inductive base_U : nat -> Type where
  | U_R (θ φ Λ : ℝ) : base_U 1
  | U_CNOT : base_U 2

open base_U

open Complex in
noncomputable instance : MatrixSemantics base_U ℂ :=
  ⟨fun G =>
  match G with
  | .U_R θ φ Λ => Matrix.reindex (@BitVec.equivFin 1).symm (@BitVec.equivFin 1).symm
    (!![(Real.cos (θ/2)), - .exp (Λ * I) * Real.sin (θ/2);
      .exp (φ * I) * Real.sin (θ/2), .exp ((φ + Λ) * I) * Real.cos (θ/2)])
  | .U_CNOT => fun u v => if (u[0]'Nat.zero_lt_two = v[0]'Nat.zero_lt_two
    ∧ u[1]'Nat.one_lt_two = u[0]'Nat.zero_lt_two ^^ v[1]'Nat.one_lt_two) then 1 else 0⟩

abbrev base_ucom := Circuit base_U


def I {dim} (n : Fin dim) : base_ucom dim :=
  .ofGateOn (U_R 0 0 0) #v[n]

noncomputable section

-- (* Some useful shorthands. *)
def H {dim} (n : Fin dim) : base_ucom dim :=
  .ofGateOn (U_R (π/2) 0 π) #v[n]
def X {dim} (n : Fin dim) : base_ucom dim :=
  .ofGateOn (U_R π 0 π) #v[n]
def Y {dim} (n : Fin dim) : base_ucom dim :=
  .ofGateOn (U_R π (π/2) (π/2)) #v[n]
def Z {dim} (n : Fin dim) : base_ucom dim :=
  .ofGateOn (U_R 0 0 π) #v[n]
-- def Rx {dim} θ n : base_ucom dim := uapp1 (U_R θ (-(π/2)) (π/2)) n.
-- def Ry {dim} θ n : base_ucom dim := uapp1 (U_R θ 0 0) n.
-- def Rz {dim} λ n : base_ucom dim := uapp1 (U_R 0 0 λ) n.
-- def T {dim} n : base_ucom dim := Rz (π / 4) n.
-- def TDAG {dim} n : base_ucom dim := Rz (- (π / 4)) n.
-- def P {dim} n : base_ucom dim := Rz (π / 2) n.
-- def PDAG {dim} n : base_ucom dim := Rz (- (π / 2)) n.
def CNOT {dim} (m n : Fin dim) (Hmn : m ≠ n := by omega) : base_ucom dim :=
  .ofGateOn U_CNOT #v[m, n]


def f0 : base_ucom 2 := 1
def f1 : base_ucom 2 := X 1
def f2 : base_ucom 2 := CNOT 0 1
def f3 : base_ucom 2 := CNOT 0 1 * X 1

def deutsch (c : base_ucom 2) : base_ucom 2 := H 0 * H 1 * c * H 0

open MatrixSemantics
def constant (c : base_ucom 2) :=
  semantics c = semantics f0 \/ semantics c = semantics f1

-- Definition balanced (c : base_ucom 2) := c ≡ f2 \/ c ≡ f3.

open Matrix

abbrev ket0 : Matrix (BitVec 1) (BitVec 0) ℂ :=
  ofFinMx (!![1; 0] : Matrix (Fin 2) (Fin 1) ℂ)

abbrev ket1 : Matrix (BitVec 1) (BitVec 0) ℂ :=
  ofFinMx (!![0; 1] : Matrix (Fin 2) (Fin 1) ℂ)


abbrev bra0 : Matrix (BitVec 0) (BitVec 1) ℂ :=
  ket0ᴴ

abbrev bra1 : Matrix (BitVec 0) (BitVec 1) ℂ :=
  ket1ᴴ


noncomputable section

def xbasisPlus : Matrix (BitVec 1) (BitVec 0) ℂ :=
  (√ 2⁻¹ : ℂ) • (ket0 + ket1)

def xbasisMinus : Matrix (BitVec 1) (BitVec 0) ℂ :=
  (√ 2⁻¹ : ℂ) • (ket0 - ket1)

def ybasisPlus : Matrix (BitVec 1) (BitVec 0) ℂ :=
  (√ 2⁻¹ : ℂ) • (ket0 + Complex.I • ket1)

def ybasisMinus : Matrix (BitVec 1) (BitVec 0) ℂ :=
  (√ 2⁻¹ : ℂ) • (ket0 + Complex.I • ket1)

def EPRpair : Matrix (BitVec 2) (BitVec 0) ℂ :=
  (√ 2⁻¹ : ℂ) • (ofFinMx !![1;0;0;1])

end section
notation "∣+⟩" => xbasisPlus
notation "∣-⟩" => xbasisMinus







lemma semantics_H_aux :
  semantics (U_R (π/2) 0 π) = (√ 2⁻¹ : ℂ) • ofFinMx !![1,1;1,-1] := by {
  simp only [semantics, Nat.reducePow, RingEquiv.coe_toEquiv_symm, Complex.exp_pi_mul_I, neg_neg,
    one_mul, Complex.ofReal_zero, zero_mul, Complex.exp_zero, zero_add, neg_mul, reindex_apply,
    Equiv.symm_symm, EquivLike.coe_coe, sqrt_inv, Complex.ofReal_inv, ofFinMx,
    RingEquiv.toEquiv_eq_coe]
  ring_nf
  rw [← div_eq_mul_one_div]
  rw [Real.cos_pi_div_four]
  rw [Real.sin_pi_div_four]
  rw [← Complex.ofReal_inv]
  rw [← Real.sqrt_div_self]
  ext i j
  obtain ⟨i⟩ := i
  obtain ⟨j⟩ := j
  fin_cases i <;> fin_cases j <;> simp [BitVec.equivFin]
}

lemma EmbeddedGate.semantics_1 [Semiring R] {U : ℕ → Type u} [MatrixSemantics U R]
  (u : U 1) (v : NoDupVector (Fin n) 1) :
  semantics (embedGate u v) =
    let i := v.val[0]'Nat.zero_lt_one
    (bvkron
    (bvkron (1 : Matrix (BitVec i) (BitVec i) R) (semantics u))
    (1 : Matrix (BitVec (n - (i + 1))) (BitVec (n - (i + 1))) R)).reindex₂
    (BitVec.castEquiv (by omega)) := by {
  simp only [semantics]
  rw [pad_matrix_one]
}

lemma semantics_H {n} (i : Fin n) :
  semantics (H i) =
  (bvkron
    (bvkron (1 : Matrix (BitVec i) (BitVec i) ℂ)
      ((√ 2⁻¹ : ℂ) • ofFinMx (n:=1) (m:=1) !![1,1;1,-1]))
    (1 : Matrix (BitVec (n - (i + 1))) (BitVec (n - (i + 1))) ℂ)).reindex₂
    (BitVec.castEquiv (by omega)) := by {
  unfold H
  simp only [Circuit.semantics_defn, Circuit.ofGateOn, List.reverse_singleton,
    List.map_singleton, List.prod_singleton]
  rw [EmbeddedGate.semantics_1]
  rw [semantics_H_aux]
  simp ; rfl
}


lemma semantics_H_0_2 :
  semantics (H ⟨0, Nat.zero_lt_two⟩) =
  bvkron ((√ 2⁻¹ : ℂ) • ofFinMx (n:=1) (m:=1) !![1,1;1,-1])
    (1 : Matrix (BitVec 1) (BitVec 1) ℂ) := by {
  rw [semantics_H]
  simp [reindex₂, bvkron_1_0_l]
}

lemma semantics_H_1_2 :
  semantics (H ⟨1, Nat.one_lt_two⟩) =
  bvkron (1 : Matrix (BitVec 1) (BitVec 1) ℂ)
    ((√ 2⁻¹ : ℂ) • ofFinMx (n:=1) (m:=1) !![1,1;1,-1]) := by {
  rw [semantics_H]
  simp [reindex₂, bvkron_1_0_r]
}


lemma semantics_gate_1 [MatrixSemantics U R] [Semiring R]
  (u : U 1) {n} (i : Fin n) :
  semantics (Circuit.ofGateOn u #v[i]) =
  (bvkron
    (bvkron (1 : Matrix (BitVec i) (BitVec i) R)
      (semantics u))
    (1 : Matrix (BitVec (n - (i + 1))) (BitVec (n - (i + 1))) R)).reindex₂
    (BitVec.castEquiv (by omega)) := by {
  simp only [Circuit.semantics_defn, Circuit.ofGateOn, List.reverse_singleton,
    List.map_singleton, List.prod_singleton]
  rw [EmbeddedGate.semantics_1]
  simp; rfl
}

lemma semantics_gate_0_2 [MatrixSemantics U R] [Semiring R]
  (u : U 1) :
  semantics (Circuit.ofGateOn u #v[0]) =
  bvkron (semantics u) (1 : Matrix (BitVec 1) (BitVec 1) R) := by {
  rw [semantics_gate_1]
  trans; apply Matrix.reindex_refl_refl
  congr 1
  apply bvkron_1_0_l (semantics u)
}

lemma semantics_gate_1_2 [MatrixSemantics U R] [Semiring R]
  (u : U 1) :
  semantics (Circuit.ofGateOn u #v[1]) =
  bvkron (1 : Matrix (BitVec 1) (BitVec 1) R) (semantics u) := by {
  rw [semantics_gate_1]
  trans; apply Matrix.reindex_refl_refl
  apply bvkron_1_0_r
}

lemma semantics_H_0_2' :
  semantics (H (0 : Fin 2)) =
  bvkron ((√ 2⁻¹ : ℂ) • ofFinMx (n:=1) (m:=1) !![1,1;1,-1])
    (1 : Matrix (BitVec 1) (BitVec 1) ℂ) := semantics_H_0_2

lemma semantics_H_1_2' :
  semantics (H (1 : Fin 2)) =
  bvkron (1 : Matrix (BitVec 1) (BitVec 1) ℂ)
    ((√ 2⁻¹ : ℂ) • ofFinMx (n:=1) (m:=1) !![1,1;1,-1]) := semantics_H_1_2

lemma semantics_f0 : semantics f0 = 1 := by {
  ext i j
  obtain ⟨i⟩ := i
  obtain ⟨j⟩ := j
  fin_cases i <;> fin_cases j <;> rfl
}

lemma semantics_f1 : semantics f1 = bvkron (1 : Matrix (BitVec 1) (BitVec 1) ℂ)
  (ofFinMx (n:=1) (m:=1) !![0,1;1,0]) := by {
  unfold f1 X
  rw [semantics_gate_1_2]
  congr 1
  simp only [semantics, Nat.reducePow, RingEquiv.coe_toEquiv_symm, cos_pi_div_two,
    Complex.ofReal_zero, Complex.exp_pi_mul_I, neg_neg, sin_pi_div_two, Complex.ofReal_one, mul_one,
    zero_mul, Complex.exp_zero, zero_add, mul_zero, reindex_apply, Equiv.symm_symm,
    EquivLike.coe_coe]
  rfl
}

lemma semantics_CNOT_0_1 : semantics (CNOT 0 1) = semantics U_CNOT := by {
  unfold CNOT
  rw [← gen_pad_matrix_id (semantics U_CNOT)]
  simp only [Circuit.ofGateOn, Fin.isValue, Circuit.semantics_defn, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one]
  simp only [semantics, Fin.isValue, Bool.decide_and, bne_iff_ne, ne_eq, ite_not]
  unfold pad_matrix
  rfl
}

lemma semantics_f2 : semantics f2 = semantics U_CNOT := semantics_CNOT_0_1

lemma semantics_f3 : semantics f3 = semantics f1 * semantics U_CNOT := by {
  unfold f3
  simp only [Fin.isValue, Circuit.semantics_mul]
  rw [semantics_CNOT_0_1]
  rfl
}

open Kronecker in
lemma deutsch_constant_correct_f0 :
   forall (c : base_ucom 2), semantics c = semantics f0 ->
   ((semantics (deutsch c)) * bvkron ket0 ket1) =
   bvkron ket0 xbasisMinus := by {
  intros c Hc
  unfold deutsch
  simp only [Nat.add_zero, Nat.reduceAdd, Fin.isValue, Circuit.semantics_mul]
  rw [semantics_H_0_2', semantics_H_1_2']
  simp only [sqrt_inv, Complex.ofReal_inv, bvkron_smul_l, Nat.reduceAdd, bvkron_smul_r,
    Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_mul]
  rw [Hc, semantics_f0]
  simp only [one_mul]
  rw [bvkron_mul_bvkron]
  rw [bvkron_mul_bvkron]
  simp only [one_mul, mul_one]
  simp only [ofFinMx_mul, Nat.reducePow, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons,
    head_cons, one_smul, tail_cons, empty_vecMul, add_zero, add_cons, add_neg_cancel,
    empty_add_empty, neg_smul, neg_cons, neg_neg, neg_empty, empty_mul, Equiv.symm_apply_apply]
  rw [bvkron_mul_bvkron]
  simp only [ofFinMx_mul, Nat.reducePow, Nat.pow_zero, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd,
    vecMul_cons, head_cons, smul_cons, smul_eq_mul, mul_one, smul_empty, tail_cons, zero_smul,
    empty_vecMul, add_zero, mul_zero, zero_add, empty_mul, Equiv.symm_apply_apply, one_smul,
    add_cons, empty_add_empty, neg_smul, neg_cons, neg_empty]
  rw [← bvkron_smul_l, ← bvkron_smul_l, ← bvkron_smul_r]
  congr 1
  · unfold ket0
    unfold ofFinMx
    simp only [Nat.reducePow, Nat.pow_zero, RingEquiv.toEquiv_eq_coe, reindex_apply,
      Equiv.symm_symm, EquivLike.coe_coe]
    rw [← mul_smul]
    rw [← _root_.mul_inv_rev]
    rw [← Complex.ofReal_mul]
    simp only [Nat.ofNat_nonneg, mul_self_sqrt, Complex.ofReal_ofNat]
    rw [Matrix.smul_submatrix]
    simp only [smul_of, smul_cons, smul_eq_mul, smul_empty, mul_zero]
    ring_nf
  · congr 1
    · simp
    · simp [ket0, ket1]
}


open Kronecker in
lemma deutsch_constant_correct_f1 :
   forall (c : base_ucom 2), semantics c = semantics f1 ->
   ((semantics (deutsch c)) * bvkron ket0 ket1) =
   - bvkron ket0 xbasisMinus := by {
  intros c Hc
  unfold deutsch
  simp only [Nat.add_zero, Nat.reduceAdd, Fin.isValue, Circuit.semantics_mul]
  rw [semantics_H_0_2', semantics_H_1_2']
  simp only [sqrt_inv, Complex.ofReal_inv, bvkron_smul_l, Nat.reduceAdd, bvkron_smul_r,
    Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_mul]
  rw [Hc, semantics_f1]
  rw [bvkron_mul_bvkron]
  rw [bvkron_mul_bvkron]
  rw [bvkron_mul_bvkron]
  rw [bvkron_mul_bvkron]
  rw [← bvkron_smul_l, ← bvkron_smul_l, ← bvkron_smul_r]
  rw [← bvkron_neg_r]
  congr 1
  · unfold ket0
    simp only [one_mul, ofFinMx_mul, Nat.reducePow, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd,
      vecMul_cons, head_cons, one_smul, tail_cons, empty_vecMul, add_zero, add_cons, add_neg_cancel,
      empty_add_empty, neg_smul, neg_cons, neg_neg, neg_empty, empty_mul, Equiv.symm_apply_apply,
      Nat.pow_zero, smul_cons, smul_eq_mul, mul_one, smul_empty, zero_smul, mul_zero, zero_add]
    rw [← mul_smul]
    rw [← _root_.mul_inv_rev]
    rw [← Complex.ofReal_mul]
    simp only [Nat.ofNat_nonneg, mul_self_sqrt, Complex.ofReal_ofNat]
    unfold ofFinMx
    simp only [Nat.reducePow, Nat.pow_zero, RingEquiv.toEquiv_eq_coe, reindex_apply,
      Equiv.symm_symm, EquivLike.coe_coe]
    rw [Matrix.smul_submatrix]
    simp only [smul_of, smul_cons, smul_eq_mul, smul_empty, mul_zero]
    ring_nf
  · simp only [mul_one, ofFinMx_mul, Nat.reducePow, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd,
    vecMul_cons, head_cons, zero_smul, tail_cons, one_smul, empty_vecMul, add_zero, zero_add,
    empty_mul, Equiv.symm_apply_apply, one_mul, Nat.pow_zero, neg_smul, neg_cons, neg_empty,
    add_cons, empty_add_empty]
    unfold xbasisMinus
    simp only [sqrt_inv, Complex.ofReal_inv, ofFinMx_sub, Nat.reducePow, Nat.pow_zero, of_sub_of,
      sub_cons, head_cons, sub_zero, tail_cons, sub_self, zero_empty, zero_sub]
    rw [← smul_neg]
    congr 1
    unfold ofFinMx
    simp only [Nat.reducePow, Nat.pow_zero, RingEquiv.toEquiv_eq_coe, reindex_apply,
      Equiv.symm_symm, EquivLike.coe_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [BitVec.equivFin]
}


-- open Kronecker in
-- lemma deutsch_constant_correct_f2 :
--    forall (c : base_ucom 2), semantics c = semantics f2 ->
--    ((semantics (deutsch c)) * bvkron ket0 ket1) =
--    bvkron ket1 xbasisMinus := by {

-- }

-- def TELE {dim} ()
-- #check CNOT (dim:=4) 1 2
-- def CZ {dim} m n : base_ucom dim :=
--   H n ; CNOT m n ; H n.
-- def SWAP {dim} m n : base_ucom dim :=
--   CNOT m n; CNOT n m; CNOT m n.
-- def U1 {dim} a n : base_ucom dim := uapp1 (U_R 0 0 a) n.
-- def U2 {dim} a b n : base_ucom dim := uapp1 (U_R (π / 2) a b) n.
-- def U3 {dim} a b c n : base_ucom dim := uapp1 (U_R a b c) n.

-- (* Standard Toffoli decomposition *)
-- def CCX {dim} a b c : base_ucom dim :=
--   H c ; CNOT b c ; TDAG c ; CNOT a c ;
--   T c ; CNOT b c ; TDAG c ; CNOT a c ;
--   CNOT a b ; TDAG b ; CNOT a b ;
--   T a ; T b ; T c ; H c.

-- (* CCZ is the same as CCX, but without the Hadamards *)
-- def CCZ {dim} a b c : base_ucom dim :=
--   CNOT b c ; TDAG c ; CNOT a c ;
--   T c ; CNOT b c ; TDAG c ; CNOT a c ;
--   CNOT a b ; TDAG b ; CNOT a b ;
--   T a ; T b ; T c.
