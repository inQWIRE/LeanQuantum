import Lean
import Quantumlib.Data.Gate.Pauli.Defs

namespace Pauli

declare_syntax_cat pauli
syntax ident : pauli
syntax:max "-" pauli : pauli
--- XXX: Messes up with pauli_map's mul?
syntax:55 pauli:55 " * " pauli:56 : pauli

syntax " ( " pauli " ) " : pauli

syntax "[P| " pauli " ]" : term

def parse_ident (id : Lean.TSyntax `ident) := do
  let mut atoms := id.getId.toString
  let mut xs := []
  let mut zs := []
  let mut phase := 0
  if atoms.startsWith "i" then
    phase := 3
    atoms := atoms.drop 1
  for atom in atoms.toList.reverse do
    let (x, z) ←
      match atom with
      | 'X' => pure (1, 0)
      | 'Y' => 
        phase := phase + 1
        pure (1, 1)
      | 'Z' => pure (0, 1)
      | 'I' => pure (0, 0)
      | _ => Lean.Macro.throwUnsupported
    xs := x :: xs
    zs := z :: zs
  let n := atoms.length
  let x_val := xs.foldl (fun acc bit => acc * 2 + bit) 0
  let z_val := zs.foldl (fun acc bit => acc * 2 + bit) 0
  return (n, phase % 4, x_val, z_val)


macro_rules
  | `( [P| -$p:ident ] ) => do
    let (n, phase, x_val, z_val) ← parse_ident p
    `(({
        m := $(Lean.quote ((phase + 2) % 4)),
        x := BitVec.ofNat $(Lean.quote n) $(Lean.quote x_val),
        z := BitVec.ofNat $(Lean.quote n) $(Lean.quote z_val)
      } : Pauli $(Lean.quote n))
    )
  | `( [P| $p:ident ] ) => do
    let (n, phase, x_val, z_val) ← parse_ident p
    `(({
        m := $(Lean.quote phase),
        x := BitVec.ofNat $(Lean.quote n) $(Lean.quote x_val),
        z := BitVec.ofNat $(Lean.quote n) $(Lean.quote z_val)
      } : Pauli $(Lean.quote n))
    )
  | `( [P| -$p:pauli ] ) =>
    `( -[P| $p ] )
  | `( [P| $p₁ * $p₂] ) =>
    `( [P| $p₁ ] * [P| $p₂ ] )
  | `( [P| ( $p:pauli ) ] ) => `( [P| $p] )

declare_syntax_cat pauli_map

syntax pauli : pauli_map
syntax ("#(" term ")" " • ") pauli : pauli_map
syntax pauli_map:30 " + " pauli_map:31 : pauli_map
syntax pauli_map:50 " * " pauli_map:51 : pauli_map
syntax "(" pauli_map ")" : pauli_map

syntax "[PA| " pauli_map " ]" : term

macro_rules 
  | `( [PA| $p:pauli ] ) =>
      ``( PauliMap.normalized (Finsupp.single [P| $p ] 1) )
  | `( [PA| #( $c:term ) • $p:pauli ] ) =>
      ``( PauliMap.normalized (Finsupp.single [P| $p ] $c) )
  | `( [PA| $pa₁ + $pa₂ ] ) =>
      ``( [PA| $pa₁] + [PA| $pa₂ ] )
  | `( [PA| $pa₁ * $pa₂ ] ) =>
      ``( PauliMap.normalized ([PA| $pa₁] * [PA| $pa₂]) )
  | `( [PA| ($pa:pauli_map) ] ) =>
      ``( [PA| $pa] )


private def getId (P : Pauli n) : String := 
  let ys := P.z &&& P.x
  let s := n.fold (fun i h acc => 
    (if ys[i] then "Y"
     else if P.z[i] then "Z"
     else if P.x[i] then "X"
     else "I") ++ acc
  ) ""
  if s.isEmpty then "0" else s

private def getPhase (P : Pauli n) : String :=
  match P.m - (Fin.ofNat 4 <| P.z.dot P.x) with
  | 0 => ""
  | 1 => "-i"
  | 2 => "-"
  | 3 => "i"

open Lean Elab PrettyPrinter Delaborator SubExpr Meta

def formatPauli (P : Pauli n) : Format :=
  Format.bracket "[P| " (.text (getId P ++ getPhase P)) " ]"

instance : Repr (Pauli n) where 
  reprPrec P _ := formatPauli P


@[delab app.Pauli.mk]
unsafe def delabPauli : Delab := do
  let e ← getExpr 
  let #[n, _, _, _] := e.getAppArgs | failure
  let some n' ← (evalNat n).run
    | failure
  try 
    let P ← Meta.evalExpr (Pauli n') (←mkAppM `Pauli #[n]) e
    let mut Pid := getId P
    let mut neg := false
    match P.m - (Fin.ofNat 4 <| P.z.dot P.x) with
    | 0 => Pid := Pid  -- TODO: What's the do-notation NoOp?
    | 1 => 
      neg := true
      Pid := "i" ++ Pid
    | 2 => neg := true
    | 3 => Pid := "i" ++ Pid 
    let Pid' := mkIdent <| Name.mkSimple Pid
    if neg then
      `([P| -$(⟨Pid'⟩) ])
    else
      `([P| $(⟨Pid'⟩) ])
  catch _ =>
    failure

end Pauli
