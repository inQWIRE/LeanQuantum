import Quantumlib.Data.Language.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Real

inductive base_UC : nat -> Type where
  | U_R (θ φ Λ : ℝ) : base_UC 1
  | U_C {n} : base_UC n -> base_UC (n + 1)



def base_ucom := Circuit base_UC

open base_UC

def I {dim} (n : Fin dim) : base_ucom dim :=
  [EmbeddedGate.embedGate (U_R 0 0 0) ⟨#v[n], List.nodup_singleton _⟩ ]

noncomputable section

-- (* Some useful shorthands. *)
-- def U_H := .
-- def U_X := U_R π 0 π.
-- def U_Y := U_R π (π/2) (π/2).
-- def U_Z := U_R 0 0 π.
def H {dim} (n : Fin dim) : base_ucom dim :=
  [EmbeddedGate.embedGate (U_R (π/2) 0 π) ⟨#v[n], List.nodup_singleton _⟩ ]
def X {dim} (n : Fin dim) : base_ucom dim :=
  [EmbeddedGate.embedGate (U_R π 0 π) ⟨#v[n], List.nodup_singleton _⟩ ]
def Y {dim} (n : Fin dim) : base_ucom dim :=
  [EmbeddedGate.embedGate (U_R π (π/2) (π/2)) ⟨#v[n], List.nodup_singleton _⟩ ]
def Z {dim} (n : Fin dim) : base_ucom dim :=
  [EmbeddedGate.embedGate (U_R 0 0 π) ⟨#v[n], List.nodup_singleton _⟩ ]
-- def Rx {dim} θ n : base_ucom dim := uapp1 (U_R θ (-(π/2)) (π/2)) n.
-- def Ry {dim} θ n : base_ucom dim := uapp1 (U_R θ 0 0) n.
-- def Rz {dim} λ n : base_ucom dim := uapp1 (U_R 0 0 λ) n.
-- def T {dim} n : base_ucom dim := Rz (π / 4) n.
-- def TDAG {dim} n : base_ucom dim := Rz (- (π / 4)) n.
-- def P {dim} n : base_ucom dim := Rz (π / 2) n.
-- def PDAG {dim} n : base_ucom dim := Rz (- (π / 2)) n.
def CNOT {dim} (m n : Fin dim) (Hmn : m ≠ n := by omega) : base_ucom dim :=
  [EmbeddedGate.embedGate (U_C (U_R π 0 π)) ⟨#v[m, n], by {
    refine List.nodup_iff_pairwise_ne.mpr ?_
    simp [Hmn]
    }⟩ ]
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
