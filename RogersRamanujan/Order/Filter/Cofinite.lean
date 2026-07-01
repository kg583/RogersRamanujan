module

public import Mathlib.Order.Filter.Cofinite

/-! # Cofinite filter

Compatibility between the cofinite filter and `Filter.map`/equivalences.
-/

@[expose] public section

open Filter

namespace Filter

theorem map_cofinite_le_iff {α β : Type*} {f : α → β} :
    map f cofinite ≤ cofinite ↔ ∀ x, (f ⁻¹' {x}).Finite := by
  refine ⟨fun h x ↦ ?_, fun h s hs ↦ ?_⟩
  · simpa using h (Set.finite_singleton x).compl_mem_cofinite
  · rw [mem_map, mem_cofinite, ← Set.preimage_compl, ← Set.biUnion_of_singleton sᶜ]
    simpa using .biUnion hs (by grind)

end Filter

namespace Equiv

@[simp] theorem map_cofinite {α β : Type*} (e : α ≃ β) :
    map e cofinite = cofinite :=
  comap_equiv_symm e cofinite ▸ e.symm.injective.comap_cofinite_eq

end Equiv
