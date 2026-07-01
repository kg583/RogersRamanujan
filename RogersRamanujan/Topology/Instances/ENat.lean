module

public import Mathlib.Topology.Instances.ENat

/-! # Topology on `ℕ∞`
-/

@[expose] public section

open Filter Topology

public theorem ENat.tendsto_nat_nhds_top :
    Tendsto (fun n : ℕ ↦ (n : ℕ∞)) atTop (𝓝 ⊤) := by
  simp [ENat.tendsto_nhds_top_iff_natCast_lt]
  aesop
