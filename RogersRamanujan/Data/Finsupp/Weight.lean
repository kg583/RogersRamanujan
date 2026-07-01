module

public import Mathlib.Data.Finsupp.Weight

/-! # Weighted degree of a `Finsupp`
-/

@[expose] public section

open Finset

namespace Finsupp

theorem degree_strictMono {σ R : Type*} [AddCommMonoid R] [PartialOrder R]
    [IsOrderedCancelAddMonoid R] :
    StrictMono (degree (σ := σ) (R := R)) := fun f g hfg ↦ by
  classical
  rw [lt_iff_le_and_ne, Finsupp.ne_iff] at hfg
  obtain ⟨hfg, a, hfga⟩ := hfg
  rw [degree_apply, degree_apply, sum_subset subset_union_left (by simp),
    sum_subset (s₁ := g.support) subset_union_right (by simp)]
  exact Finset.sum_lt_sum (fun _ _ ↦ hfg _) ⟨a, by grind [lt_iff_le_and_ne, hfg a]⟩

-- more general than `degree_mono`
theorem degree_mono' {σ R : Type*} [AddCommMonoid R] [PartialOrder R] [IsOrderedAddMonoid R] :
    Monotone (degree (σ := σ) (R := R)) := fun f g hfg ↦ by
  classical
  rw [degree_apply, degree_apply, sum_subset subset_union_left (by simp),
    sum_subset (s₁ := g.support) subset_union_right (by simp)]
  exact Finset.sum_le_sum fun i a ↦ hfg i

end Finsupp
