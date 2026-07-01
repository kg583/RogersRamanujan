module

public import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-! # Summation filters

Convergence of an infinite sum along a chosen summation filter.
-/

@[expose] public section

open Filter Finset Topology SummationFilter

@[nontriviality] theorem HasSum.of_subsingleton
    {α β : Type*} [AddCommMonoid β] [TopologicalSpace β] [Subsingleton β]
    {f : α → β} {y : β} {L : SummationFilter α} : HasSum f y L := by
  simp_rw [HasSum, IndiscreteTopology.nhds_eq, tendsto_top]

@[to_additive] theorem multipliable_conditional_nat_iff
    {α : Type*} [CommMonoid α] [TopologicalSpace α] (f : ℕ → α) :
    Multipliable f (conditional ℕ) ↔ ∃ l, Tendsto (∏ i ∈ range ·, f i) atTop (𝓝 l) := by
  simp_rw [Multipliable, HasProd, conditional_filter_eq_map_range, tendsto_map'_iff]
  rfl
