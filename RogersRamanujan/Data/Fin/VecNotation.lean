module

public meta import Lean.Expr
import Mathlib.Data.Fin.VecNotation

/-! # Vector notation for `Fin n → α`
-/

@[expose] public section

section Meta

open Lean

/-- Extract a `![x₁, ..., xₙ]` vector literal from an expression, if possible. -/
meta partial def Lean.Expr.vecLit? (v : Expr) : Option (List Expr) :=
  match v.getAppFnArgs with
  | (``Matrix.vecCons, #[_R, _n, x, v]) => v.vecLit?.map (x :: ·)
  | (``Matrix.vecEmpty, #[_R]) => some []
  | _ => none

end Meta
