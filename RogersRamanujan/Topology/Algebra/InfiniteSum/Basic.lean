module

import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-! # Infinite sums
-/

@[expose] public section

open Finset

@[to_additive] theorem HasProd.finsetProd_of_finite_fiber
    {α β M : Type*} [CommMonoid M] [TopologicalSpace M]
    {m : M} {f : α → M} (hf : HasProd f m)
    {g : α → β} (hg : ∀ y, (g ⁻¹' {y}).Finite) :
    HasProd (fun y ↦ ∏ x ∈ (hg y).toFinset, f x) m := by
  have key (v : Finset β) : (g ⁻¹' v).Finite := v.finite_toSet.preimage' fun _ _ ↦ hg _
  classical
  refine hf.hasProd_of_prod_eq fun u ↦ ⟨u.image g, fun v hv ↦ ?_⟩
  refine ⟨(key v).toFinset, by simp; grind, ?_⟩
  rw [← prod_fiberwise_of_maps_to (t := v) (g := g) (by simp)]
  congr!
  simp [Finset.ext_iff]
  grind

/-- With explicit choice of fibers. -/
@[to_additive] theorem HasProd.finsetProd_of_finite_fiber'
    {α β M : Type*} [CommMonoid M] [TopologicalSpace M]
    {m : M} {f : α → M} (hf : HasProd f m)
    {g : α → β} (s : β → Finset α) (hg : ∀ y, s y = g ⁻¹' {y}) :
    HasProd (fun y ↦ ∏ x ∈ s y, f x) m :=
  (hf.finsetProd_of_finite_fiber (g := g) (by simp [← hg])).congr_fun fun y ↦
    prod_congr (by simp [← hg]) fun _ _ ↦ rfl
