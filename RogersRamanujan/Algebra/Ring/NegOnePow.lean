module

public import Mathlib.Algebra.Ring.NegOnePow -- shake: keep

/-! # `(-1) ^ n` in a ring
-/

@[expose] public section

section Meta

open Lean Meta Qq

/-- Defeq-simplification procedure that reduces `Int.negOnePow n` to `1` or `-1`. -/
dsimproc reduceIntNegOnePow (Int.negOnePow _) := fun e ↦ do
  let ⟨1, ~q(ℤˣ), ~q(Int.negOnePow $nE)⟩ ← inferTypeQ e | return .continue
  let some n := nE.int? | return .continue
  have result : Q(ℤˣ) := if n % 2 = 0 then q(1) else q(-1)
  return .done result

end Meta
