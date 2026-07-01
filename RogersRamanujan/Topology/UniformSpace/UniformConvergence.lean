module

import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-! # Uniform convergence in topological groups

Reformulating `TendstoUniformly` in terms of a basis of `nhds 0`.
-/

@[expose] public section

open Filter

namespace Filter.HasBasis

theorem tendstoUniformly_iff'
    {ι α G : Type*} [AddGroup G] [UniformSpace G] [IsUniformAddGroup G]
    {p : Filter ι} {κ : Type*} {pp : κ → Prop} {sp : κ → Set G} (h : (nhds 0).HasBasis pp sp)
    (F : ι → α → G) (f : α → G) :
    TendstoUniformly F f p ↔ ∀ k, pp k → ∀ᶠ i in p, ∀ a, F i a - f a ∈ sp k := by
  rw [IsTopologicalAddGroup.tendstoUniformly_iff _ _ _ IsUniformAddGroup.rightUniformSpace_eq]
  exact ⟨fun H k hk ↦ H _ (h.mem_of_mem hk), fun H u hu ↦
    let ⟨k, hk, hk'⟩ := h.mem_iff.mp hu; (H k hk).mono (by grind)⟩

end Filter.HasBasis
