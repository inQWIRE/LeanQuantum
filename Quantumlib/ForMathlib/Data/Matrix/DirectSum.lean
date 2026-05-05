import Quantumlib.ForMathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Equiv.Fin.Basic

namespace Matrix

open DirectSum

-- Intended type: CMatrix (m1 + m2) (n1 + n2)
-- Convertible?
-- def directSum (A : CMatrix m1 n1) (B : CMatrix m2 n2) : Matrix (Fin m1 ⊕ Fin m2) (Fin n1 ⊕ Fin n2) ℂ :=
--   Matrix.fromBlocks A 0 0 B

-- abbrev directSum0 {α m1 n1 m2 n2} [Zero α] (A : Matrix m1 n1 α) (B : Matrix m2 n2 α)
--   := Matrix.fromBlocks A 0 0 B

-- scoped[DirectSum] notation:100 A " ⊕₀ " B => Matrix.fromBlocks A 0 0 B

-- works, but iffy
-- scoped[DirectSum] notation:100 A " ⊕ₙ " B => Matrix.fromBlocks A 0 0 B

-- lemma dsum_assoc0 {α m1 n1 m2 n2 m3 n3} [AddMonoid α] (A : Matrix m1 n1 α) (B : Matrix m2 n2 α) (C : Matrix m3 n3 α) :
--   reindex (Equiv.sumAssoc _ _ _) (Equiv.sumAssoc _ _ _) ((A ⊕ₙ B) ⊕ₙ C) = A ⊕ₙ (B ⊕ₙ C) :=
--   by
--     ext i j
--     rcases i with i | i | i <;>
--     rcases j with j | j | j <;>
--     rfl

-- lemma dsum_trace0 {n1 n2 α} [Fintype n1] [Fintype n2] [AddCommMonoid α] (A : Matrix n1 n1 α) (B : Matrix n2 n2 α) : Matrix.trace (A ⊕₀ B) = Matrix.trace A + Matrix.trace B :=
--   by
--     rw [fromBlocks]
--     rw [trace]
--     rw [Fintype.sum_sum_type]
--     simp only [diag_apply, of_apply, Sum.elim_inl, Sum.elim_inr]
--     rfl

-- lemma dsum_det0 {n1 n2 α} [DecidableEq n1] [DecidableEq n2] [Fintype n1] [Fintype n2] [CommRing α]
--   (A : Matrix n1 n1 α) (B : Matrix n2 n2 α): Matrix.det (A ⊕₀ B) = Matrix.det A * Matrix.det B :=
--    by simp


-- General form
def directSum {α m1 n1 m2 n2} [Zero α]
  (A : Matrix m1 n1 α) (B : Matrix m2 n2 α) : Matrix (m1 ⊕ m2) (n1 ⊕ n2) α :=
   Matrix.fromBlocks A 0 0 B

#check directSum

scoped[DirectSum] infixl:100 " ⊕ " => Matrix.directSum


lemma dsum_assoc {α m1 n1 m2 n2 m3 n3} [AddMonoid α] (A : Matrix m1 n1 α) (B : Matrix m2 n2 α) (C : Matrix m3 n3 α) :
  reindex (Equiv.sumAssoc _ _ _) (Equiv.sumAssoc _ _ _) ((A ⊕ B) ⊕ C) = (A ⊕ (B ⊕ C)) :=
  by
    ext i j
    rcases i with i | i | i <;>
    rcases j with j | j | j <;>
    rfl


lemma dsum_trace {n1 n2 α} [Fintype n1] [Fintype n2] [AddCommMonoid α] (A : Matrix n1 n1 α) (B : Matrix n2 n2 α) : Matrix.trace (A ⊕ B) = Matrix.trace A + Matrix.trace B :=
  by
    rw [directSum, fromBlocks, trace] -- can also simp this
    rw [Fintype.sum_sum_type]
    simp only [diag_apply, of_apply, Sum.elim_inl, Sum.elim_inr]
    rfl

lemma dsum_det {n1 n2 α} [DecidableEq n1] [DecidableEq n2] [Fintype n1] [Fintype n2] [CommRing α]
  (A : Matrix n1 n1 α) (B : Matrix n2 n2 α): Matrix.det (A ⊕ B) = Matrix.det A * Matrix.det B :=
   by simp [directSum]

-- CMatrix forms



-- FromBlocks version

def directSumC {m1 n1 m2 n2} (A : CMatrix m1 n1) (B : CMatrix m2 n2) : CMatrix (m1 + m2) (n1 + n2) :=
  reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 B)

scoped[DirectSum] infixl:100 " ⊕c " => Matrix.directSumC

def finAddAssoc (a b c : ℕ) :
  Fin ((a + b) + c) ≃ Fin (a + (b + c)) :=
  finCongr (by rw [Nat.add_assoc])
  -- Equiv.cast (by rw [Nat.add_assoc])

lemma dsum_assoc_C
  {m1 n1 m2 n2 m3 n3}
  (A : CMatrix m1 n1)
  (B : CMatrix m2 n2)
  (C : CMatrix m3 n3) :
  (Matrix.reindex (finAddAssoc m1 m2 m3) (finAddAssoc n1 n2 n3) ((A ⊕c B) ⊕c C))
  = (A ⊕c (B ⊕c C)) :=
by
  funext i j
  rw [finAddAssoc, finAddAssoc]
  simp only [reindex_apply, finCongr_symm, submatrix_apply, finCongr_apply]
  simp only [directSumC]
  simp only [reindex_apply, submatrix_apply]
  rcases i with ⟨i, Hi⟩  ; rcases j with ⟨j, Hj⟩
  simp
  unfold finSumFinEquiv
  simp
  unfold Fin.addCases
  simp
  split_ifs <;> simp <;> try split_ifs <;> simp <;>
  omega
  any_goals omega
  simp [fromBlocks]
  split_ifs <;> simp
  any_goals omega
  congr 2 <;> omega

lemma dsum_trace_C (A : CMatrix n1 n1) (B : CMatrix n2 n2) : Matrix.trace (A ⊕ B) = Matrix.trace A + Matrix.trace B :=
  by sorry

lemma dsum_det_C (A : Matrix n1 n1 α) (B : Matrix n2 n2 α): Matrix.det (A ⊕ B) = Matrix.det A * Matrix.det B :=
  by sorry

-- Ugly but direct version:
def directSumC2 {m1 n1 m2 n2}
  (A : CMatrix m1 n1) (B : CMatrix m2 n2) :
  CMatrix (m1 + m2) (n1 + n2) :=
fun x y =>
  if h : x < m1 ∧ y < n1 then
    A ⟨x, h.1⟩ ⟨y, h.2⟩
  else if h : m1 ≤ x ∧ n1 ≤ y then
    B ⟨x - m1, Nat.sub_lt_left_of_lt_add h.1 x.is_lt⟩
      ⟨y - n1, Nat.sub_lt_left_of_lt_add h.2 y.is_lt⟩
  else
0

scoped[DirectSum] infixl:100 " ⊕₂ " => Matrix.directSumC2

lemma dsum_assoc_C2
  {m1 n1 m2 n2 m3 n3}
  (A : CMatrix m1 n1)
  (B : CMatrix m2 n2)
  (C : CMatrix m3 n3) :
  (Matrix.reindex (finAddAssoc m1 m2 m3) (finAddAssoc n1 n2 n3) ((A ⊕₂ B) ⊕₂ C))
  = (A ⊕₂ (B ⊕₂ C)) :=
by
  rw [finAddAssoc, finAddAssoc]
  simp only [reindex_apply, finCongr_symm]
  funext i j
  rcases i with ⟨i, Hi⟩  ; rcases j with ⟨j, Hj⟩
  simp only [submatrix_apply, finCongr_apply, Fin.cast_mk]
  simp [directSumC2]
  split_ifs <;> try rfl
  any_goals omega
  simp [Nat.sub_add_eq]

lemma dsum_trace_C2 (A : CMatrix n1 n1) (B : CMatrix n2 n2) : Matrix.trace (A ⊕₂ B) = Matrix.trace A + Matrix.trace B :=
  by
    unfold directSumC2
    unfold trace
    simp only [diag_apply, and_self]
    sorry

lemma dsum_det_C2 (A : CMatrix n1 n1) (B : CMatrix n2 n2): Matrix.det (A ⊕₂ B) = Matrix.det A * Matrix.det B :=
  by sorry


-- addCases version
def directSumC3  (A : CMatrix m1 n1) (B : CMatrix m2 n2) : CMatrix (m1 + m2) (n1 + n2) :=
fun x y =>
  Fin.addCases
    (fun x₁ => Fin.addCases (A x₁) (fun _ => 0) y)
    (fun x₂ => Fin.addCases (fun _ => 0) (B x₂) y)
    x

scoped[DirectSum] infixl:100 " ⊕₃ " => Matrix.directSumC3

lemma dsum_assoc_C3
  {m1 n1 m2 n2 m3 n3}
  (A : CMatrix m1 n1)
  (B : CMatrix m2 n2)
  (C : CMatrix m3 n3) :
  (Matrix.reindex (finAddAssoc m1 m2 m3) (finAddAssoc n1 n2 n3) ((A ⊕₃ B) ⊕₃ C))
  = (A ⊕₃ (B ⊕₃ C)) :=
by
  unfold directSumC3
  funext i j
  simp only [reindex_apply, submatrix_apply]
  rw?


  -- simp only [reindex_apply]
  -- rw [finAddAssoc, finAddAssoc]

  -- funext i j
  -- rw?



--   rw [finAddAssoc, finAddAssoc]
--   simp only [reindex_apply, finCongr_symm]
--   funext i j
--   rcases i with ⟨i, Hi⟩  ; rcases j with ⟨j, Hj⟩
--   simp only [submatrix_apply, finCongr_apply, Fin.cast_mk]
--   simp [directSumC3]
--   split_ifs <;> try rfl
--   any_goals omega
--   simp [Nat.sub_add_eq]

-- lemma dsum_trace_C3 (A : CMatrix n1 n1) (B : CMatrix n2 n2) : Matrix.trace (A ⊕₂ B) = Matrix.trace A + Matrix.trace B :=
--   by
--     unfold directSumC2
--     unfold trace
--     simp only [diag_apply, and_self]
--     sorry

-- lemma dsum_det_C3 (A : CMatrix n1 n1) (B : CMatrix n2 n2): Matrix.det (A ⊕₂ B) = Matrix.det A * Matrix.det B :=
--   by sorry
