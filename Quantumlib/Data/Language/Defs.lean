import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Data.Matrix.PEquiv
import Mathlib.Data.Finset.Image
import QuantumLib.ForMathlib.Data.Matrix.Basic
import QuantumLib.ForMathlib.Data.BitVec.Basic
import Mathlib.Data.BitVec
import Batteries.Data.BitVec
import Init.Data.Vector
import Batteries.Data.Vector.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Finset

lemma filter_card_lt_of_exists_not {p : α → Prop} [DecidablePred p]
  {s : Finset α} (H : ∃ a, a ∈ s ∧ ¬ p a) :
  {x ∈ s | p x}.card < s.card := by {
  apply Finset.card_lt_card
  exact filter_ssubset.mpr H
}

end Finset

def NoDupVector (A : Type) (n : ℕ) := { v : Vector A n // v.toList.Nodup}

namespace NoDupVector

def image (f : A -> B) (Hf : f.Injective) {n} (v : NoDupVector A n) :
  NoDupVector B n := ⟨v.val.map f, by {
    rw [Vector.toList_map]
    rw [List.nodup_map_iff Hf]
    apply v.property
  }⟩

def map (f : A ↪ B) {n} (v : NoDupVector A n) : NoDupVector B n :=
  image f f.injective v

lemma is_le {n m} (v : NoDupVector (Fin n) m) : m ≤ n := by {
  rw [← Vector.length_toList (xs:=v.val)]
  trans
  · apply v.property.length_le_card
  · simp
}

lemma card_mem {n m} (v : NoDupVector (Fin n) m) :
  Finset.card {x | x ∈ v.val} = m := by {
  refine Eq.trans ?_ (Vector.length_toList (xs:=v.val))
  rw [← List.toFinset_card_of_nodup v.property]
  congr 1
  ext
  simp
}

lemma card_nmem {n m} (v : NoDupVector (Fin n) m) :
  Finset.card {x | x ∉ v.val} = n - m := by {
  have : Finset.card {x | x ∈ v.val} = m := v.card_mem
  have Heq := Finset.card_filter_add_card_filter_not (s:=Finset.univ) (· ∈ v.val)
  simp only [Finset.card_univ, Fintype.card_fin] at Heq
  have := v.is_le
  omega
}

def finCompl {n m} (v : NoDupVector (Fin n) m) : NoDupVector (Fin n) (n - m) :=
  ⟨⟨Array.mk ((List.finRange n).filter (·∉v.val)), by {
    simp only [decide_not, List.size_toArray]
    rw [← List.toFinset_card_of_nodup]
    · simp only [List.toFinset_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
        decide_eq_false_iff_not, List.toFinset_finRange]
      apply v.card_nmem
    · apply (List.nodup_finRange n).filter
  }⟩, by {
    simp only [decide_not, Vector.toList_mk]
    apply (List.nodup_finRange _).filter
  }⟩

@[simp]
lemma mem_finCompl {n m} (v : NoDupVector (Fin n) m) i :
  i ∈ v.finCompl.val ↔ i ∉ v.val := by {
  unfold finCompl
  simp
}

@[simp]
lemma finIdxOf?_get [BEq α] [LawfulBEq α] {m} (v : NoDupVector α m) (i : Fin m) :
  v.val.finIdxOf? (v.val.get i) = some i := by {
  simp only [Vector.finIdxOf?_eq_some_iff, true_and]
  intros j Hji
  unfold Vector.get
  simp only [← Array.getElem_toList]
  rw [List.getElem_inj (by apply v.property)]
  apply Fin.ne_of_lt at Hji
  simp_all [Fin.val_inj]
}

@[simp]
lemma finIdxOf?_getElem [BEq α] [LawfulBEq α] {m} (v : NoDupVector α m) (i : ℕ) hi :
  v.val.finIdxOf? (v.val[i]'hi) = some ⟨i, hi⟩ := finIdxOf?_get v ⟨i, hi⟩

def indexedEquiv {n m} (v : NoDupVector (Fin n) m) :
  Fin n ≃ Fin m ⊕ Fin (n - m) :=
  ⟨fun i =>
     match h : v.val.finIdxOf? i with
    | none => .inr ((v.finCompl.val.finIdxOf? i).get (by {
        rw [Vector.finIdxOf?_eq_none_iff] at h
        rw [Vector.isSome_finIdxOf?]
        simp_all
      }))
    | some i => .inl i,
  Sum.elim v.val.get v.finCompl.val.get,
  by {
    intros i
    simp only
    split
    · rename_i Hnone
      rw [Vector.finIdxOf?_eq_none_iff, ← mem_finCompl, ← Vector.contains_iff_mem,
        ← Vector.isSome_finIdxOf?] at Hnone
      rw [Option.isSome_iff_exists] at Hnone
      obtain ⟨j, Hj⟩ := Hnone
      simp only [Sum.elim_inr]
      trans (v.finCompl.val.get j)
      · congr 1
        apply Option.get_of_eq_some
        apply Hj
      · simp_all
    · rename_i j Hj
      simp_all
  },
  by {
    intros i
    cases i with
    | inl i =>
      simp only [Sum.elim_inl]
      split <;> rename_i Heq <;> rw [finIdxOf?_get] at Heq <;> simp_all
    | inr i =>
      simp only [Sum.elim_inr, finIdxOf?_get, Option.get_some]
      rw [Vector.finIdxOf?_eq_none_iff.mpr (by {
        have Hin : (v.finCompl.val.get i) ∈ v.finCompl.val := Vector.mem_of_getElem rfl
        simp_all
      })]
  }⟩

@[simp]
lemma indexedEquiv_apply_get {n m} (v : NoDupVector (Fin n) m) (i:ℕ) hi :
  v.indexedEquiv (v.val[i]'hi) = .inl ⟨i, hi⟩ := by {
  unfold indexedEquiv
  simp only [Equiv.coe_fn_mk]
  have Heq := v.finIdxOf?_getElem i hi
  split <;> rename_i Heq' <;> rw [Heq] at Heq' <;> simp_all
}

end NoDupVector


namespace Vector

def listNotIndexed {n m} (v : Vector (Fin n) m) : List (Fin n) :=
  (List.finRange n).filter (fun i => (v.contains i).not)



lemma length_listNotIndexed {n m} (v : NoDupVector (Fin n) m) :
  v.val.listNotIndexed.length = n - m := by {
  rw [← List.toFinset_card_of_nodup]
  · unfold listNotIndexed
    simp only [contains_eq_mem, List.toFinset_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not, List.toFinset_finRange]
    apply v.card_nmem
  · apply (List.nodup_finRange n).filter
}

end Vector

namespace BitVec

def vectorReindex {n m} (v : Vector (Fin n) m) (bv : BitVec n) : BitVec m :=
  BitVec.ofFnLE (fun i => bv.getLsb (v[i]))

def vectorNotIndexed {n m} (v : Vector (Fin n) m) (bv : BitVec n) : List Bool :=
  v.listNotIndexed.map bv.getLsb

def toVectorLE {n} (bv : BitVec n) : Vector Bool n :=
  (Vector.finRange n).map bv.getLsb

def ofVectorLE {n} (v : Vector Bool n) : BitVec n :=
  BitVec.ofFnLE v.get

@[simp]
lemma getElem_ofVectorLE {n} (v : Vector Bool n) (i : ℕ) (Hi : i < n) :
  (ofVectorLE v)[i] = v[i] := by {
  simp [ofVectorLE, Vector.get]
}

@[simp]
lemma getElem_toVectorLE {n} (v : BitVec n) (i : ℕ) (Hi : i < n) :
  v.toVectorLE[i] = v[i] := by {
  simp [toVectorLE]
}

@[simp]
lemma getElem?_ofVectorLE {n} (v : Vector Bool n) (i : ℕ) :
  (ofVectorLE v)[i]? = v[i]? := by {
  rw [getElem?_def, getElem?_def]
  simp
}

@[simp]
lemma getElem?_toVectorLE {n} (v : BitVec n) (i : ℕ) :
  v.toVectorLE[i]? = v[i]? := by {
  rw [getElem?_def, getElem?_def]
  simp
}

@[simp]
lemma toVectorLE_ofVectorLE {n} (v : Vector Bool n) :
  (ofVectorLE v).toVectorLE = v := by {
  ext; simp
}

@[simp]
lemma ofVectorLE_toVectorLE {n} (v : BitVec n) :
  ofVectorLE v.toVectorLE = v := by {
  ext; simp
}

def vectorEquiv {n} : BitVec n ≃ Vector Bool n :=
  ⟨toVectorLE, ofVectorLE, ofVectorLE_toVectorLE, toVectorLE_ofVectorLE⟩

lemma toVectorLE_injective {n} : (BitVec.toVectorLE (n:=n)).Injective := vectorEquiv.injective
lemma ofVectorLE_injective {n} : (BitVec.ofVectorLE (n:=n)).Injective := vectorEquiv.symm.injective

lemma length_vectorNotIndexed {n m} (v : NoDupVector (Fin n) m) (bv : BitVec n) :
  (bv.vectorNotIndexed v.val).length = n - m := by {
  unfold vectorNotIndexed
  simp [Vector.length_listNotIndexed]
}


def vectorNotIndexed' {n m} (v : NoDupVector (Fin n) m) (bv : BitVec n) : BitVec (n - m) :=
  (ofBoolListLE (bv.vectorNotIndexed v.val)).cast (length_vectorNotIndexed v bv)

def mk_of_vecNotIndexed {n m} (v : NoDupVector (Fin n) m)
  (indexed : BitVec m) (notindexed : BitVec (n - m)) : BitVec n :=
  ofFnLE (fun k =>
    Sum.elim indexed.getLsb notindexed.getLsb (v.indexedEquiv k))

lemma vectorReindex_alt {n m} (v : NoDupVector (Fin n) m) (bv : BitVec n) :
  bv.vectorReindex v.val = ofFnLE (fun k => bv[v.indexedEquiv.symm (.inl k)]) := by {
  ext i hi
  unfold vectorReindex
  simp only [Fin.getElem_fin, getLsb_eq_getElem, getElem_ofFnLE]
  unfold NoDupVector.indexedEquiv
  simp only [Equiv.coe_fn_symm_mk, Sum.elim_inl]
  rfl
}

lemma vectorNotIndexed'_alt {n m} (v : NoDupVector (Fin n) m) (bv : BitVec n) :
  bv.vectorNotIndexed' v = ofFnLE (fun k => bv[v.indexedEquiv.symm (.inr k)]) := by {
  ext i hi
  unfold vectorNotIndexed'
  simp only [getElem_cast, Fin.getElem_fin, getElem_ofFnLE]

  rw [← BitVec.getLsbD_eq_getElem]
  rw [BitVec.getLsbD_ofBoolListLE]
  simp only [List.getD_eq_getElem?_getD]
  unfold vectorNotIndexed
  simp only [List.getElem?_map]
  unfold NoDupVector.indexedEquiv
  simp only [Equiv.coe_fn_symm_mk, Sum.elim_inr]
  unfold NoDupVector.finCompl
  simp only [decide_not, Vector.get_mk, Fin.getElem_fin, List.getElem_toArray]
  unfold Vector.listNotIndexed
  simp only [Vector.contains_eq_mem]
  rw [getElem?_pos]
  simp only [Option.map_some, getLsb_eq_getElem, Option.getD_some]
  rfl
}

lemma vectorNotIndexed_alt {n m} (v : NoDupVector (Fin n) m) (bv : BitVec n) :
  bv.vectorNotIndexed v.val = (ofFnLE (fun k => bv[v.indexedEquiv.symm (.inr k)])).toVectorLE.toList := by {
  rw [← vectorNotIndexed'_alt]
  unfold vectorNotIndexed vectorNotIndexed'
  unfold toVectorLE
  unfold vectorNotIndexed
  ext i b
  simp only [List.getElem?_map, Option.map_eq_some_iff, getLsb_eq_getElem, Fin.getElem_fin,
    Vector.getElem?_toList, Vector.getElem?_map, getElem_cast]
  simp only [← BitVec.getLsbD_eq_getElem, getLsbD_ofBoolListLE]
  simp only [Fin.is_lt, getLsbD_eq_getElem, List.getD_eq_getElem?_getD, List.getElem?_map]
  rw [Vector.finRange]
  simp only [Vector.getElem?_ofFn, Option.dite_none_right_eq_some, Option.some.injEq,
    exists_exists_eq_and, exists_prop]
  have Himpl : v.val.listNotIndexed[i]?.isSome = true <-> i < n - m := by
    simp [Vector.length_listNotIndexed]
  revert Himpl
  cases (v.val.listNotIndexed[i]?) <;> simp_all
}

lemma vectorNotIndexed_alt' {n m} (v : NoDupVector (Fin n) m) (bv : BitVec n) :
  bv.vectorNotIndexed v.val = (bv.vectorNotIndexed' v).toVectorLE.toList := by {
  rw [vectorNotIndexed_alt, vectorNotIndexed'_alt]
}

@[simp]
lemma mk_of_vecNotIndexed_id {n m} (v : NoDupVector (Fin n) m) (bv : BitVec n) :
  mk_of_vecNotIndexed v (vectorReindex v.val bv) (vectorNotIndexed' v bv) = bv := by {
  ext i hi
  rw [vectorReindex_alt, vectorNotIndexed'_alt]
  unfold mk_of_vecNotIndexed
  simp only [getElem_ofFnLE]
  have Heq := v.indexedEquiv.symm_apply_apply ⟨i, hi⟩
  revert Heq
  cases (v.indexedEquiv ⟨i, hi⟩) <;> simp_all
}

@[simp]
lemma vectorReindex_mk_of_vecNotIndexed {n m} (v : NoDupVector (Fin n) m)
  (bv : BitVec m) (bv' : BitVec (n - m)) :
  vectorReindex (v.val) (mk_of_vecNotIndexed v bv bv') = bv := by {
  ext i hi
  unfold vectorReindex mk_of_vecNotIndexed
  simp
}

@[simp]
lemma vectorNotIndexed'_mk_of_vecNotIndexed {n m} (v : NoDupVector (Fin n) m)
  (bv : BitVec m) (bv' : BitVec (n - m)) :
  vectorNotIndexed' v (mk_of_vecNotIndexed v bv bv') = bv' := by {
  ext i hi
  unfold mk_of_vecNotIndexed
  rw [vectorNotIndexed'_alt]
  simp
}


lemma id_mk_of_vecNotIndexed {n m} (v : NoDupVector (Fin n) m)
  (k : BitVec m × BitVec (n - m)) :
   (vectorReindex (v.val) (mk_of_vecNotIndexed v k.1 k.2),
   vectorNotIndexed' v (mk_of_vecNotIndexed v k.1 k.2)) = k := by {
  simp
}

def indexedEquiv {n m} (v : NoDupVector (Fin n) m) :
  BitVec n ≃ BitVec m × BitVec (n - m) :=
  ⟨fun bv => ⟨bv.vectorReindex v.val, bv.vectorNotIndexed' v⟩,
   fun ⟨idx, nidx⟩ => mk_of_vecNotIndexed v idx nidx,
   mk_of_vecNotIndexed_id v,
   id_mk_of_vecNotIndexed v⟩

end BitVec



def gen_pad_matrix {n m n' m'} (idxs_n : Vector (Fin n') n)
  (idxs_m : Vector (Fin m') m) [Zero R]
  (U : Matrix (BitVec n) (BitVec m) R) : Matrix (BitVec n') (BitVec m') R :=
  fun v w =>
    if v.vectorNotIndexed idxs_n = w.vectorNotIndexed idxs_m then
      U (v.vectorReindex idxs_n) (w.vectorReindex idxs_m) else 0

def pad_matrix {n m} (v : NoDupVector (Fin n) m) [Zero R]
  (U : Matrix (BitVec m) (BitVec m) R) : Matrix (BitVec n) (BitVec n) R :=
  gen_pad_matrix v.val v.val U


def BitVec.addEquiv {n m} : BitVec (n + m) ≃ BitVec n × BitVec m :=
  ⟨fun v => ⟨v.setWidth n, v.extractLsb' n m⟩, fun v_w => (v_w.2 ++ v_w.1).cast (Nat.add_comm _ _), by {
    intros v
    simp only
    ext i Hi
    simp only [getElem_cast, getElem_append, getElem_setWidth, getElem_extractLsb', dite_eq_ite]
    split_ifs
    · rfl
    · congr
      simp only
      omega
  }, by {
    rintro ⟨v, w⟩
    simp only [setWidth_cast, Prod.mk.injEq]
    rw [setWidth_append_eq_right]
    simp only [true_and]
    ext i Hi
    simp only [getElem_extractLsb', getLsbD_cast, getLsbD_append, add_lt_iff_neg_left,
      _root_.not_lt_zero, ↓reduceIte, add_tsub_cancel_left]
    rfl
  }⟩

def BitVec.addEquiv' {n m} : BitVec (n + m) ≃ BitVec n × BitVec m :=
  ⟨fun v => ⟨v.extractLsb' m n,v.setWidth m⟩, fun v_w => v_w.1 ++ v_w.2, by {
    intros v
    simp only
    ext i Hi
    simp only [getElem_append, getElem_setWidth, getElem_extractLsb', dite_eq_ite]
    split_ifs
    · rfl
    · congr
      simp only
      omega
  }, by {
    rintro ⟨v, w⟩
    simp only [Prod.mk.injEq]
    rw [extractLsb'_append_eq_left, setWidth_append_eq_right]
    trivial
  }⟩

lemma List.finRange_cast {n : ℕ} m (H : m = n) :
  List.finRange n = (List.finRange m).map (Fin.cast H) := by subst n; simp

lemma List.finRange_add (n m : ℕ) :
  List.finRange (n + m) = (List.finRange n).map (Fin.castAdd m) ++
    (List.finRange m).map (Fin.natAdd n) := by {
  induction n with
  | zero =>
    rw [finRange_cast m (by simp)]
    simp
  | succ n IHn =>
    rw [finRange_cast ((n + m) + 1) (by linarith)]
    rw [finRange_succ, finRange_succ, IHn]
    simp only [map_append, map_map, map_cons, Fin.cast_zero, cons_append, cons.injEq]
    constructor; ext; simp
    congr 1
    -- unfold Function.comp
    simp only [map_inj_left, mem_finRange, Function.comp_apply, forall_const]
    intros k
    ext
    simp +arith
}

lemma Vector.listNotIndexed_whiskerL {n} n'
  (idxs : Vector (Fin n) m) :
  (idxs.map (Fin.natAdd n')).listNotIndexed =
  (List.finRange n').map (Fin.castAdd n) ++
  idxs.listNotIndexed.map (Fin.natAdd n') := by {
  unfold listNotIndexed
  rw [List.finRange_add]
  simp only [contains_eq_mem, mem_map, List.filter_append]
  congr 1
  · refine List.filter_eq_self.mpr ?_
    simp only [List.mem_map, List.mem_finRange, true_and, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not, not_exists, not_and, forall_exists_index, forall_apply_eq_imp_iff]
    intros k x _ Hkx
    apply (congrArg Fin.toNat) at Hkx
    simp only [Fin.toNat_eq_val, Fin.val_natAdd, Fin.val_castAdd] at Hkx
    have := k.is_lt
    linarith
  · rw [List.filter_map]
    congr 1
    refine List.filter_congr ?_
    intros k _
    simp
}

lemma BitVec.vectorNotIndexed_whiskerL {n n' m}
  (idxs : Vector (Fin n) m) (bv : BitVec (n' + n)) :
  bv.vectorNotIndexed (idxs.map (Fin.natAdd n')) =
  (bv.setWidth n').toVectorLE.toList ++
  (bv.extractLsb' n' n).vectorNotIndexed idxs := by {
  unfold vectorNotIndexed
  rw [Vector.listNotIndexed_whiskerL]
  simp only [List.map_append, List.map_map]
  congr 1
  · ext i b
    simp only [getElem?_def, List.length_map, List.length_finRange, List.getElem_map,
      List.getElem_finRange, Fin.cast_mk, Function.comp_apply, Fin.castAdd_mk, getLsb_eq_getElem,
      Fin.getElem_fin, Option.dite_none_right_eq_some, Option.some.injEq, Vector.length_toList,
      Vector.getElem_toList, getElem_toVectorLE, getElem_setWidth, dite_eq_ite,
      Option.ite_none_right_eq_some]
    apply Iff.intro
    · rintro ⟨w, h⟩
      subst h
      simp_all only [true_and]
      rfl
    · rintro ⟨left, right⟩
      simp_all only [exists_true_left]
      subst right
      rfl
  · simp
}

lemma BitVec.vectorReindex_whiskerL {n n' m}
  (idxs : Vector (Fin n) m) (bv : BitVec (n' + n)) :
  bv.vectorReindex (idxs.map (Fin.natAdd n')) =
  (bv.extractLsb' n' n).vectorReindex idxs := by {
  unfold vectorReindex
  ext i Hi
  simp
}

lemma Vector.listNotIndexed_whiskerR {n} n'
  (idxs : Vector (Fin n) m) :
  (idxs.map (Fin.castAdd n')).listNotIndexed =
  idxs.listNotIndexed.map (Fin.castAdd n') ++
  (List.finRange n').map (Fin.natAdd n) := by {
  unfold listNotIndexed
  rw [List.finRange_add]
  simp only [contains_eq_mem, mem_map, List.filter_append]
  congr 1
  · rw [List.filter_map]
    congr 1
    refine List.filter_congr ?_
    intros k _
    simp
  · refine List.filter_eq_self.mpr ?_
    simp only [List.mem_map, List.mem_finRange, true_and, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not, not_exists, not_and, forall_exists_index, forall_apply_eq_imp_iff]
    intros k x _ Hkx
    apply (congrArg Fin.toNat) at Hkx
    simp only [Fin.toNat_eq_val, Fin.val_natAdd, Fin.val_castAdd] at Hkx
    have := x.is_lt
    linarith
}

lemma BitVec.vectorNotIndexed_whiskerR {n n' m}
  (idxs : Vector (Fin n') m) (bv : BitVec (n' + n)) :
  bv.vectorNotIndexed (idxs.map (Fin.castAdd n)) =
  (bv.setWidth n').vectorNotIndexed idxs ++
  (bv.extractLsb' n' n).toVectorLE.toList := by {
  unfold vectorNotIndexed
  rw [Vector.listNotIndexed_whiskerR]
  simp only [List.map_append, List.map_map]
  congr 1
  · simp
    intros
    rfl
  · ext i b
    simp only [getElem?_def, List.length_map, List.length_finRange, List.getElem_map,
      List.getElem_finRange, Fin.cast_mk, Function.comp_apply, Fin.natAdd_mk, getLsb_eq_getElem,
      Fin.getElem_fin, Option.dite_none_right_eq_some, Option.some.injEq, Vector.length_toList,
      Vector.getElem_toList, getElem_toVectorLE, getElem_extractLsb', dite_eq_ite,
      Option.ite_none_right_eq_some]
    apply Iff.intro
    · rintro ⟨w, h⟩
      subst h
      simp_all only [add_lt_add_iff_left, getLsbD_eq_getElem, _root_.and_self]
    · rintro ⟨left, right⟩
      simp_all only [exists_true_left]
      subst right
      rfl
}

lemma BitVec.vectorReindex_whiskerR {n n' m}
  (idxs : Vector (Fin n') m) (bv : BitVec (n' + n)) :
  bv.vectorReindex (idxs.map (Fin.castAdd n)) =
  (bv.setWidth n').vectorReindex idxs := by {
  unfold vectorReindex
  ext i Hi
  simp
  rfl
}


open Kronecker in
lemma gen_pad_matrix_whiskerL {n m n' m'} (k : ℕ) (vn : Vector (Fin n') n)
  (vm : Vector (Fin m') m) [Semiring R]
  (U : Matrix (BitVec n) (BitVec m) R) :
  gen_pad_matrix (vn.map (Fin.natAdd k)) (vm.map (Fin.natAdd k)) U =
  ((1 : Matrix (BitVec k) (BitVec k) R) ⊗ₖ
   gen_pad_matrix vn vm U).reindex BitVec.addEquiv.symm BitVec.addEquiv.symm := by {
  ext i j
  simp only [Matrix.reindex_apply, Equiv.symm_symm, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply]
  unfold gen_pad_matrix
  rw [Matrix.one_apply]
  simp only [mul_ite, ite_mul, one_mul, zero_mul, mul_zero]
  rw [← ite_and]
  congr 1
  · rw [BitVec.vectorNotIndexed_whiskerL,BitVec.vectorNotIndexed_whiskerL]
    unfold BitVec.addEquiv
    simp only [Equiv.coe_fn_mk, eq_iff_iff]
    constructor
    · rw [List.append_eq_append_iff_of_size_eq_left (by simp)]
      rintro ⟨Hl, Hr⟩
      refine And.intro Hr ?_
      rw [Vector.toList_inj] at Hl
      apply (congrArg BitVec.ofVectorLE) at Hl
      simp_all
    · simp_all
  · simp [BitVec.vectorReindex_whiskerL]; rfl
}

open Kronecker in
lemma gen_pad_matrix_whiskerR {n m n' m'} (k : ℕ) (vn : Vector (Fin n') n)
  (vm : Vector (Fin m') m) [Semiring R]
  (U : Matrix (BitVec n) (BitVec m) R) :
  gen_pad_matrix (vn.map (Fin.castAdd k)) (vm.map (Fin.castAdd k)) U =
  (gen_pad_matrix vn vm U ⊗ₖ
   (1 : Matrix (BitVec k) (BitVec k) R)).reindex BitVec.addEquiv.symm BitVec.addEquiv.symm := by {
  ext i j
  simp only [Matrix.reindex_apply, Equiv.symm_symm, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply]
  unfold gen_pad_matrix
  rw [Matrix.one_apply]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← ite_and]
  congr 1
  · rw [BitVec.vectorNotIndexed_whiskerR,BitVec.vectorNotIndexed_whiskerR]
    unfold BitVec.addEquiv
    simp only [Equiv.coe_fn_mk, eq_iff_iff]
    constructor
    · rw [List.append_eq_append_iff_of_size_eq_right (by simp)]
      rintro ⟨Hl, Hr⟩
      refine And.intro ?_ Hl
      rw [Vector.toList_inj] at Hr
      apply (congrArg BitVec.ofVectorLE) at Hr
      simp_all
    · simp_all
  · simp [BitVec.vectorReindex_whiskerR]; rfl
}

lemma BitVec.setWidth_eq_cast {n m} (H : n = m) (bv : BitVec n) :
  bv.setWidth m = bv.cast H := by {
  subst m
  simp
}

@[simp]
lemma BitVec.toVectorLE_cast {n m} (H : n = m) (bv : BitVec n) :
  (bv.cast H).toVectorLE = bv.toVectorLE.cast H := by {
  subst m
  simp
}

lemma gen_pad_matrix_ill_sized [Zero R] {n m n' m'}
  (vn : NoDupVector (Fin n') n) (vm : NoDupVector (Fin m') m)
  (U : Matrix (BitVec n) (BitVec m) R) :
  n' - n ≠ m' - m ->
  gen_pad_matrix vn.val vm.val U = 0 := by {
  intros Hne
  ext i j
  unfold gen_pad_matrix
  simp only [Matrix.zero_apply, ite_eq_right_iff]
  simp only [BitVec.vectorNotIndexed_alt']
  intros Heq
  apply (congrArg List.length) at Heq
  simp_all
}


lemma gen_pad_matrix_compose {n m o n' m' o'} (k : ℕ) (vn : NoDupVector (Fin n') n)
  (vm : NoDupVector (Fin m') m) (vo : NoDupVector (Fin o') o) [Semiring R]
  (U : Matrix (BitVec n) (BitVec m) R)
  (V : Matrix (BitVec m) (BitVec o) R)
  (Hsize : n' - n = m' - m <-> m' - m = o' - o)
  (Hsize' : n' - n = m' - m <-> n' - n = o' - o) :
  gen_pad_matrix vn.val vo.val (U * V) =
  gen_pad_matrix vn.val vm.val U * gen_pad_matrix vm.val vo.val V := by {
  ext i j
  rw [Matrix.mul_apply]
  unfold gen_pad_matrix
  rw [Matrix.mul_apply]
  simp only [mul_ite, ite_mul, zero_mul, mul_zero]
  split <;> rename_i Heq
  · apply Fintype.sum_of_injective (fun x => BitVec.mk_of_vecNotIndexed vm x ((BitVec.vectorNotIndexed' vo j).setWidth _))
    · intros k l Heq
      simp only at Heq
      apply (congrArg (BitVec.vectorReindex vm.val)) at Heq
      simp_all
    · simp only [Set.mem_range, not_exists, ite_eq_right_iff]
      intros i' Hx
      specialize (Hx (BitVec.vectorReindex vm.val i'))
      intros Hi'j Hii'
      simp only [BitVec.vectorNotIndexed_alt'] at *
      have hi'j := congrArg (List.length) Hi'j
      simp only [Vector.length_toList] at hi'j
      exfalso
      apply Hx
      refine Eq.trans ?_ (BitVec.mk_of_vecNotIndexed_id vm _)
      congr 1
      apply BitVec.toVectorLE_injective
      apply Vector.toList_inj.mp
      rw [← Hii']
      rw [BitVec.setWidth_eq_cast hi'j.symm]
      simp only [BitVec.toVectorLE_cast]
      rw [Vector.toList_cast]
      simp_all
    · intros i'
      simp only [BitVec.vectorNotIndexed_alt'] at *
      simp only [BitVec.vectorNotIndexed'_mk_of_vecNotIndexed,
        BitVec.vectorReindex_mk_of_vecNotIndexed]
      have Hno := congrArg List.length Heq
      simp only [Vector.length_toList] at Hno
      have Hnm := Hsize'.mpr Hno
      have Hmo := Hsize.mp Hnm
      rw [BitVec.setWidth_eq_cast Hmo.symm]
      simp_all [Vector.toList_cast]
  · symm
    apply Fintype.sum_eq_zero
    intros a
    simp_all
}



class MatrixSemantics (U : ℕ -> Type u) (R : outParam Type) where
  semantics {n} (u : U n) : Matrix (BitVec n) (BitVec n) R


open MatrixSemantics



inductive EmbeddedGate (U : ℕ -> Type u) (n : ℕ) : Type u where
  | embedGate {m} (u : U m) (bits : NoDupVector (Fin n) m) : EmbeddedGate U n

namespace EmbeddedGate

instance [MatrixSemantics U R] [Zero R] : MatrixSemantics (EmbeddedGate U) R :=
  ⟨fun G =>
  match G with
  | .embedGate u bits => pad_matrix bits (semantics u)
  ⟩


-- def semantics {U : ℕ -> Type u} [Zero R]
--   (SU : forall n, U n -> Matrix (BitVec n) (BitVec n) R) {n} (G : EmbeddedGate U n) :
--     Matrix (BitVec n) (BitVec n) R :=
--   match G with
--   | .embedGate u bits => pad_matrix bits (SU _ u)

def whiskerL {U : ℕ -> Type u} (m : ℕ) {n} (G : EmbeddedGate U n) : EmbeddedGate U (m + n) :=
  match G with
  | .embedGate u bits =>
    .embedGate u (bits.image (Fin.natAdd m) (Fin.natAdd_injective n m))

def whiskerR {U : ℕ -> Type u} (m : ℕ) {n} (G : EmbeddedGate U n) : EmbeddedGate U (n + m) :=
  match G with
  | .embedGate u bits =>
    .embedGate u (bits.image (Fin.castAdd m) (Fin.castAdd_injective n m))

open Kronecker in
lemma semantics_whiskerL {U : ℕ -> Type u} [Semiring R] [MatrixSemantics U R]
  k {n} (G : EmbeddedGate U n) :
  semantics (G.whiskerL k) =
  ((1 : Matrix (BitVec k) (BitVec k) R) ⊗ₖ semantics G
    ).reindex BitVec.addEquiv.symm BitVec.addEquiv.symm := by {
  simp [semantics, whiskerL, pad_matrix, NoDupVector.image, gen_pad_matrix_whiskerL]
}

open Kronecker in
lemma semantics_whiskerR {U : ℕ -> Type u} [Semiring R]
  [MatrixSemantics U R] k {n} (G : EmbeddedGate U n) :
  semantics (G.whiskerR k) =
  (semantics G ⊗ₖ (1 : Matrix (BitVec k) (BitVec k) R)
    ).reindex BitVec.addEquiv.symm BitVec.addEquiv.symm := by {
  simp [semantics, whiskerR, pad_matrix, NoDupVector.image, gen_pad_matrix_whiskerR]
}

end EmbeddedGate







structure Circuit (U : ℕ -> Type u) (n : ℕ) : Type u where
  toList : List (EmbeddedGate U n)

namespace Circuit

instance [MatrixSemantics U R] [One R] [Mul R] [AddCommMonoid R]
  : MatrixSemantics (Circuit U) R :=
  ⟨fun C => (C.toList.map (fun g => semantics g)).prod⟩

lemma semantics_defn [MatrixSemantics U R] [One R] [Mul R] [AddCommMonoid R]
  {n} (C : Circuit U n) :
  semantics C = (C.toList.map (fun g => semantics g)).prod := rfl


@[simp]
def toList_mk {U : ℕ → Type u} {n : ℕ} l : (⟨l⟩ : Circuit U n).toList = l := rfl

instance : OfNat (Circuit U n) 1 := ⟨.mk []⟩

@[simp]
lemma toList_one : toList (1 : Circuit U n) = [] := rfl

instance : Mul (Circuit U n) := ⟨fun C D => .mk (C.toList ++ D.toList)⟩

lemma mul_def {U : ℕ -> Type u} {n} (C D : Circuit U n) : C * D = .mk (C.toList ++ D.toList) := rfl

@[simp]
lemma toList_mul {U : ℕ -> Type u} {n}
  (C D : Circuit U n) : (C * D).toList = (C.toList ++ D.toList) := rfl

def whiskerL {U : ℕ -> Type u} (m : ℕ) {n} (G : Circuit U n) : Circuit U (m + n) :=
  ⟨G.toList.map (.whiskerL m)⟩

def whiskerR {U : ℕ -> Type u} (m : ℕ) {n} (G : Circuit U n) : Circuit U (n + m) :=
  ⟨G.toList.map (.whiskerR m)⟩

def stack {U : ℕ -> Type u} {n m} (G : Circuit U n) (H : Circuit U m) : Circuit U (n + m) :=
  G.whiskerR m * H.whiskerL n


lemma semantics_mul [Semiring R] {U : ℕ -> Type u}
  [MatrixSemantics U R] {n} (C D : Circuit U n) :
  semantics (C * D) = semantics (R:=R) C * semantics D := by {
  simp [semantics_defn]
}

open Kronecker in
lemma semantics_whiskerL [CommSemiring R] {U : ℕ -> Type u}
  [MatrixSemantics U R] k {n} (C : Circuit U n) :
  semantics (C.whiskerL k) =
  ((1 : Matrix (BitVec k) (BitVec k) R) ⊗ₖ semantics C
    ).reindex BitVec.addEquiv.symm BitVec.addEquiv.symm := by {
  simp only [semantics_defn]
  induction C with
  | mk C =>
    simp only [whiskerL, toList_mk, List.map_map, Matrix.reindex_apply, Equiv.symm_symm]
    induction C with
    | nil => simp
    | cons G C IHC =>
      simp only [List.map_cons, Function.comp_apply, EmbeddedGate.semantics_whiskerL,
        Matrix.reindex_apply, Equiv.symm_symm, List.prod_cons, IHC, Matrix.submatrix_mul_equiv]
      rw [← one_mul 1]
      rw [Matrix.mul_kronecker_mul]
      simp only [mul_one]
}

open Kronecker in
lemma semantics_whiskerR [CommSemiring R] {U : ℕ -> Type u}
  [MatrixSemantics U R] k {n} (C : Circuit U n) :
  semantics (C.whiskerR k) =
  (semantics C ⊗ₖ (1 : Matrix (BitVec k) (BitVec k) R)
    ).reindex BitVec.addEquiv.symm BitVec.addEquiv.symm := by {
  simp only [semantics_defn]
  induction C with
  | mk C =>
    simp only [whiskerR, toList_mk, List.map_map, Matrix.reindex_apply, Equiv.symm_symm]
    induction C with
    | nil => simp
    | cons G C IHC =>
      simp only [List.map_cons, Function.comp_apply, EmbeddedGate.semantics_whiskerR,
        Matrix.reindex_apply, Equiv.symm_symm, List.prod_cons, IHC, Matrix.submatrix_mul_equiv]
      rw [← one_mul 1]
      rw [Matrix.mul_kronecker_mul]
      simp only [mul_one]
}

open Kronecker in
lemma semantics_stack [CommSemiring R] {U : ℕ -> Type u}
  [MatrixSemantics U R] {n} (C D : Circuit U n) :
  semantics (stack C D) =
  (semantics C ⊗ₖ semantics D
    ).reindex BitVec.addEquiv.symm BitVec.addEquiv.symm := by {
  unfold stack
  rw [semantics_mul]
  rw [semantics_whiskerL, semantics_whiskerR]
  simp [← Matrix.mul_kronecker_mul]
}


end Circuit
