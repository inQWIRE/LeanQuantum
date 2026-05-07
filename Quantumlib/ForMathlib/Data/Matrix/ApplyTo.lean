import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Data.Matrix.PEquiv
import Mathlib.Data.Finset.Image
import QuantumLib.ForMathlib.Data.Matrix.Basic

def toFront [DecidableEq m] (f : n → m) -- (Hf : Function.Injective f)
  [Zero R] [One R] :
  Matrix m (n ⊕ {x : m // x ∉ Set.range f}) R := Matrix.fromCols (fun i j => if f j = i then 1 else 0) (fun i j => if ↑ j = i then 1 else 0)

def fromFront [DecidableEq m] (f : n → m) -- (Hf : Function.Injective f)
  [Zero R] [One R] :
  Matrix (n ⊕ {x : m // x ∉ Set.range f}) m R := Matrix.fromRows (fun i j => if f i = j then 1 else 0) (fun i j => if ↑ i = j then 1 else 0)


namespace Function.Embedding

def inv_cases [Fintype α] [DecidableEq β] (f : α ↪ β) (b : β) : {a : α // f a = b} ⊕' (b ∉ Set.range f) :=
  if h : ∃ a, f a = b then .inl (Fintype.chooseX (f · = b) (by {
    obtain ⟨a, Ha⟩ := h
    exists a
    refine ⟨Ha, ?_⟩
    rw [← Ha]
    simp
  })) else .inr (by simp [h])

@[simp]
lemma inv_cases_apply [Fintype α] [DecidableEq β] (f : α ↪ β) (a : α) : f.inv_cases (f a) = .inl ⟨a, rfl⟩ := by {
  unfold inv_cases
  split_ifs with Ha
  · obtain ⟨a', Ha'⟩ := Fintype.chooseX _ _
    apply f.injective at Ha'
    subst a'
    rfl
  · apply Ha
    simp
}

lemma inv_cases_notin [Fintype α] [DecidableEq β] (f : α ↪ β) (Hb : b ∉ Set.range f) : f.inv_cases b = .inr Hb := by {
  unfold inv_cases
  split_ifs with Ha
  · apply Hb
    simp [Ha]
  · rfl
}

def inv [Fintype α] [DecidableEq β] (f : α ↪ β) : β → Option α :=
  fun b => if h : ∃ a, f a = b then some (Fintype.choose (f · = b) (by {
    obtain ⟨a, Ha⟩ := h
    exists a
    refine ⟨Ha, ?_⟩
    rw [← Ha]
    simp
  })) else none


def equivComplRange
  [Fintype n] [DecidableEq m]
  (f : n ↪ m) : n ⊕ {x : m // x ∉ Set.range f} ≃ m :=
  ⟨Sum.elim f Subtype.val, fun b => PSum.rec (.inl ∘ Subtype.val) (fun Hb => .inr ⟨b, Hb⟩) (f.inv_cases b),
  by {
    intros a
    rcases a with a | ⟨b, Hb⟩
    · simp
    · simp only [Sum.elim_inr]
      rw [f.inv_cases_notin Hb]
  },
  by {
    intros b
    simp only
    rcases f.inv_cases b with ⟨a, Ha⟩ | Hb
    · apply Ha
    · rfl
  }⟩

end Function.Embedding


def applyOn
  [Fintype n] [DecidableEq m] [CommRing R]
  (f : n ↪ m) (M : Matrix n n R) : Matrix m m R :=
  (Matrix.fromBlocks M 0 0 1).reindex f.equivComplRange f.equivComplRange


-- def applyOnQ
--   [Fintype n] [DecidableEq m] [CommRing R]
--   (f : n ↪ m) (M : Matrix (2 ^ n) (2 ^ n) R) : Matrix (2 ^ m) (2 ^ m) R :=
--   (Matrix.fromBlocks M 0 0 1).reindex f.equivComplRangeQ f.equivComplRangeQ

-- lemma applyOn_alt [DecidableEq n] [DecidableEq m]
--   [Fintype n] [Fintype m] [CommRing R]
--   (f : n ↪ m) (M : Matrix n n R) :
--   applyOn f M =
--   toFront f * (Matrix.fromBlocks M 0 0 1) * fromFront f
  --  := by {
  -- ext i j
  -- simp only [Matrix.reindex_apply, Matrix.submatrix_apply]

  -- unfold Function.Embedding.inv
  -- split_ifs with hi hj <;> simp only
  -- · unfold applyOn


-- }

inductive UCOM (U : ∀ (n : Type v) [Fintype n], Type w) (n : Type u) [Fintype n] : Type (max u w (v + 1)) where
  | useq : UCOM U n -> UCOM U n -> UCOM U n
  | uapp [Fintype m] (f : m ↪ n) : U m -> UCOM U n


def UCOM_semantics [CommRing R] {U : ∀ (n : Type v) [Fintype n], Type w} (UM : ∀ {n : Type v} [Fintype n] (u : U n), Matrix n n R)
  {n : Type u} [Fintype n] [DecidableEq n] : UCOM U n → Matrix n n R
  | .useq u v => UCOM_semantics UM u * UCOM_semantics UM v
  | @UCOM.uapp _ _ _ _m _Hm f u => applyOn f (UM u)
