module

public import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-! # Definitions of infinite sums
-/

@[expose] public section

open Filter Finset Topology

namespace HasProd

@[to_additive] theorem unique_inseparable
    {α β : Type*} [CommMonoid α] [TopologicalSpace α]
    {L : SummationFilter β} {f : β → α} [R1Space α] [L.NeBot] {a₁ a₂ : α}
    (h₁ : HasProd f a₁ L) (h₂ : HasProd f a₂ L) : Inseparable a₁ a₂ :=
  tendsto_nhds_unique_inseparable h₁ h₂

end HasProd

@[to_additive] theorem Multipliable.hasProd_of_le
    {α β : Type*} [CommMonoid α] [TopologicalSpace α]
    {L₁ L₂ : SummationFilter β} {f : β → α} [R1Space α] [L₂.NeBot]
    (h : Multipliable f L₁) (hL : L₂.filter ≤ L₁.filter) :
    HasProd f (∏'[L₂] i, f i) L₁ := by
  have h₁ := (h.mono_filter hL).hasProd.unique_inseparable (h.hasProd.mono_left hL)
  rw [HasProd, h₁.nhds_eq]
  exact h.hasProd
