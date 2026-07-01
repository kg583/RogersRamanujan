module

public import Mathlib.Algebra.Ring.Subgroup

/-! # Subgroups of rings
-/

@[expose] public section

open scoped Pointwise

namespace AddSubgroup

section NonUnitalNonAssocRing
variable {R : Type*} [NonUnitalNonAssocRing R] {M N P : AddSubgroup R}

@[grind =] theorem mul_le_iff : M * N ≤ P ↔ ∀ x ∈ M, ∀ y ∈ N, x * y ∈ P := M.mul_le

theorem mul_le_iff_coe : M * N ≤ P ↔ (M : Set R) * (N : Set R) ⊆ P := by
  simp [mul_le_iff, Set.subset_def, Set.mem_mul]
  grind

end NonUnitalNonAssocRing

end AddSubgroup
