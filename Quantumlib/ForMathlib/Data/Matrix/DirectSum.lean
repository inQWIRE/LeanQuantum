import Quantumlib.ForMathlib.Data.Matrix.Basic

namespace Matrix

-- Intended type: CMatrix (m1 + m2) (n1 + n2)
-- Convertible?
-- def directSum (A : CMatrix m1 n1) (B : CMatrix m2 n2) : Matrix (Fin m1 ⊕ Fin m2) (Fin n1 ⊕ Fin n2) ℂ :=
--   Matrix.fromBlocks A 0 0 B


-- Most (?) general form
def directSum [AddMonoid α] (A : Matrix m1 n1 α) (B : Matrix m2 n2 α) : Matrix (m1 ⊕ m2) (n1 ⊕ n2) α :=
   Matrix.fromBlocks A 0 0 B

#check directSum

scoped[DirectSum] infixl:100 " ⊕ " => Matrix.directSum

open DirectSum

lemma dsum_assoc [AddMonoid α] (A : Matrix m1 n1 α) (B : Matrix m2 n2 α) (C : Matrix m3 n3 α) :
  reindex (Equiv.sumAssoc _ _ _) (Equiv.sumAssoc _ _ _) ((A ⊕ B) ⊕ C) = (A ⊕ (B ⊕ C)) :=
  by
    ext i j
    rcases i with i | i | i <;>
    rcases j with j | j | j <;>
    rfl


lemma dsum_trace [Fintype n1] [Fintype n2] [AddCommMonoid α] (A : Matrix n1 n1 α) (B : Matrix n2 n2 α) : Matrix.trace (A ⊕ B) = Matrix.trace A + Matrix.trace B :=
  by
    rw [directSum]
    rw [fromBlocks]
    rw [trace]
    rw [Fintype.sum_sum_type]
    simp only [diag_apply, of_apply, Sum.elim_inl, Sum.elim_inr]
    rfl

lemma dsum_det [DecidableEq n1] [DecidableEq n2] [Fintype n1] [Fintype n2] [CommRing α]
  (A : Matrix n1 n1 α) (B : Matrix n2 n2 α): Matrix.det (A ⊕ B) = Matrix.det A * Matrix.det B :=
   by
     rw [← det_fromBlocks_zero₂₁ A 0 B]
     rfl


-- lemma dsum_assoc (A : CMatrix m1 n1) (B : CMatrix m2 n2) (C : CMatrix m3 n3) : (A ⊕ B) ⊕ C = A ⊕ (B ⊕ C) :=
--   by sorry

-- lemma dsum_trace (A B : CMatrix) : Matrix.trace (A ⊕ B) = Matrix.trace A + Matrix.trace B :=
--   by sorry

-- lemma dsum_det (A B : CMatrix) : Matrix.det (A ⊕ B) = Matrix.det A * Matrix.det B :=
--   by sorry

-- CMatrix form

def directSumC (A : CMatrix m1 n1) (B : CMatrix m2 n2) : CMatrix (m1 + m2) (n1 + n2) :=
   of fun x y => if x < m1 && y < n1 then A x y else if x >= m1 && y >= n1 then B (x - m1) (y - n1) else 0
