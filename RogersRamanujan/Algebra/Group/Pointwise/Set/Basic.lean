module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-! # Pointwise operations on sets
-/

@[expose] public section

namespace Set

open Pointwise

@[to_additive] theorem range_mul_subset {α β : Type*} [Mul β] {f g : α → β} :
    range (fun i ↦ f i * g i) ⊆ range f * range g := by
  simp [range_subset_iff, mul_mem_mul]

end Set
