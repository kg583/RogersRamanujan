module

import RogersRamanujan.RingTheory.MvPowerSeries.Basic
import RogersRamanujan.Topology.Algebra.TopologicallyNilpotent
public import Mathlib.RingTheory.MvPowerSeries.PiTopology

/-! # Product topology on multivariate power series
-/

@[expose] public section

open Finset Filter Topology

set_option backward.isDefEq.respectTransparency false

namespace MvPowerSeries
namespace WithPiTopology

theorem hasBasis_nhds_of_discrete
    {R σ : Type*} [Semiring R] [TopologicalSpace R] [DiscreteTopology R] (p : MvPowerSeries σ R) :
    HasBasis (𝓝 p) (fun s : Set (σ →₀ ℕ) ↦ s.Finite)
      (fun s ↦ {q | ∀ i ∈ s, q.coeff i = p.coeff i}) := by
  rw [nhds_pi, nhds_discrete]
  exact Filter.hasBasis_pi_pure p

theorem hasBasis_nhds_zero_of_discrete
    {R σ : Type*} [Semiring R] [TopologicalSpace R] [DiscreteTopology R] :
    HasBasis (𝓝 (0 : MvPowerSeries σ R)) (fun s : Set (σ →₀ ℕ) ↦ s.Finite)
      (fun s ↦ (⨅ i ∈ s, (coeff i).ker : Submodule R _)) := by
  convert hasBasis_nhds_of_discrete (0 : MvPowerSeries σ R) with s
  simp [Set.ext_iff]

variable {R σ : Type*} [Semiring R] [TopologicalSpace R] (f : MvPowerSeries σ R)

@[scoped simp] theorem isTopologicallyNilpotent_iff_constantCoeff_isNilpotent'
    [DiscreteTopology R] : IsTopologicallyNilpotent f ↔ IsNilpotent f.constantCoeff := by
  refine ⟨fun h ↦ by simpa using h.map (continuous_constantCoeff R), fun ⟨n, hn⟩ ↦
    .of_pow' (n := n) ?_⟩
  rw [← map_pow] at hn
  simpa [IsTopologicallyNilpotent, tendsto_iff_coeff_tendsto] using fun d ↦
    ⟨d.degree + 1, fun b hb ↦ coeff_pow_eq_zero_of_constantCoeff_eq_zero hn (by grind)⟩

end WithPiTopology

end MvPowerSeries
