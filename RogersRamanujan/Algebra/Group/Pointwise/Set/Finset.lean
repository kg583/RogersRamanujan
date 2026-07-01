module

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-! # Pointwise operations on finsets
-/

@[expose] public section

namespace Finset

open scoped Pointwise

theorem prod_mem_of_mul_subset_self {α : Type*} [CommMonoid α] {s : Set α} (hs : s * s ⊆ s)
    {ι : Type*} {f : ι → α} {t : Finset ι} (hts : ∀ i ∈ t, f i ∈ s) (ht : t.Nonempty) :
    ∏ i ∈ t, f i ∈ s := by
  classical
  obtain ⟨t, i, hit, rfl⟩ := ht.exists_cons_eq
  rw [prod_cons]
  clear ht
  induction t using Finset.cons_induction_on with
  | empty => grind
  | cons j t hjt ih =>
    rw [prod_cons, mul_left_comm]
    exact hs <| Set.mul_mem_mul (hts j (by grind)) (by grind)

end Finset
