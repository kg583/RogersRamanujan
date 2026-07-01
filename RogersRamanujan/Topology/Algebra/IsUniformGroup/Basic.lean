module

public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.UniformSpace.Cauchy

/-! # Cauchy sequences in uniform groups
-/

@[expose] public section

open Filter Topology

namespace CauchySeq

@[to_additive]
theorem tendsto_div_nhds_one
    {G : Type*} [Group G] [UniformSpace G] [IsUniformGroup G]
    {f : ℕ → G} (hf : CauchySeq f) : Tendsto (fun n ↦ f (n + 1) / f n) atTop (𝓝 1) := by
  rw [cauchySeq_iff_tendsto, uniformity_eq_comap_nhds_one_swapped, tendsto_comap_iff] at hf
  refine hf.comp (f := fun n ↦ (n + 1, n)) ?_
  rw [← prod_atTop_atTop_eq, tendsto_prod_iff']
  exact ⟨tendsto_add_atTop_nat 1, tendsto_id⟩

end CauchySeq
