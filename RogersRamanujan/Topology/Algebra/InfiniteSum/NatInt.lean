module

import RogersRamanujan.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-! # Infinite sums indexed by `ℕ` and `ℤ`
-/

@[expose] public section

open Filter Finset Topology

/-- More general version of the existing `HasProd.nat_mul_neg`! -/
@[to_additive /-- More general version of the existing `HasSum.nat_add_neg`! -/]
theorem HasProd.ite_nat_mul_neg
    {M : Type*} [CommMonoid M] [TopologicalSpace M] {m : M} {f : ℤ → M} (hf : HasProd f m) :
    HasProd (fun n : ℕ ↦ if n = 0 then f 0 else f n * f (-n)) m := by
  refine (hf.finsetProd_of_finite_fiber' (g := Int.natAbs)
    (s := fun n : ℕ ↦ ({(n : ℤ), (-n : ℤ)})) fun x ↦ ?_).congr_fun ?_ <;> grind

@[to_additive] theorem hasProd_conditional_iff_tendsto_prod
    {M : Type*} [CommMonoid M] [TopologicalSpace M] {m : M} {f : ℕ → M} :
    HasProd f m (.conditional ℕ) ↔ Tendsto (∏ i ∈ range ·, f i) atTop (𝓝 m) := by
  rw [HasProd, SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff]
  rfl

/-- Generalization of `HasProd.tendsto_prod_nat`. -/
@[to_additive] theorem HasProd.tendsto_prod_range
    {M : Type*} [CommMonoid M] [TopologicalSpace M] {m : M} {f : ℕ → M}
    (h : HasProd f m (.conditional ℕ)) :
    Tendsto (∏ i ∈ range ·, f i) atTop (𝓝 m) :=
  hasProd_conditional_iff_tendsto_prod.mp h
