module

public import RogersRamanujan.Analysis.Seminorm
import RogersRamanujan.Topology.Algebra.OpenSubgroup
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-! # Locally convex spaces with seminorms
-/

@[expose] public section

open Filter Topology

namespace WithSeminorms

variable {𝕜 E ι : Type*}
variable [NormedField 𝕜] [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable {p : SeminormFamily 𝕜 E ι} (hp : WithSeminorms p)
include hp

theorem tendsto_nhds_le {F : Type*} (u : F → E) (f : Filter F) (y : E) :
    Tendsto u f (𝓝 y) ↔ ∀ i ε, 0 < ε → ∀ᶠ x in f, p i (u x - y) ≤ ε := by
  rw [hp.tendsto_nhds]
  refine ⟨fun h i ε hε ↦ ?_, fun h i ε hε ↦ ?_⟩
  · filter_upwards [h i ε hε] with x hx
    grind
  · filter_upwards [h i (ε / 2) (by positivity)] with x hx
    grind

theorem tendsto_nhds_zero {F : Type*} (u : F → E) (f : Filter F) :
    Tendsto u f (𝓝 0) ↔ ∀ i ε, 0 < ε → ∀ᶠ x in f, p i (u x) < ε := by
  simpa using hp.tendsto_nhds u 0

/-- The open ball of radius `r` around `0` for an ultrametric seminorm in a `WithSeminorms`
family, as an open additive subgroup. -/
def ballOpenAddSubgroup (i : ι) (hi : ∀ x y, p i (x + y) ≤ max (p i x) (p i y))
    (r : ℝ) (hr : 0 < r) : OpenAddSubgroup E where
  __ := (p i).ballAddSubgroup hi r hr
  isOpen' := by
    let h := hp.topologicalAddGroup
    exact ((p i).ballAddSubgroup hi r hr).isOpen_of_mem_nhds <| by
      simpa using hp.hasBasis_zero_ball.mem_of_mem (i := ({i}, r)) hr

@[simp] theorem coe_ballOpenAddSubgroup
    (i : ι) (hi : ∀ x y, p i (x + y) ≤ max (p i x) (p i y)) (r : ℝ) (hr : 0 < r) :
    (hp.ballOpenAddSubgroup i hi r hr : Set E) = (p i).ball 0 r := (p i).coe_ballAddSubgroup hi r hr

/-- A topology induced by an ultrametric family of seminorms is nonarchimedean. -/
theorem nonarchimedeanAddGroup (hadd : ∀ i x y, p i (x + y) ≤ max (p i x) (p i y)) :
    NonarchimedeanAddGroup E where
  __ := hp.topologicalAddGroup
  is_nonarchimedean U hU :=
    let ⟨⟨s, r⟩, (hr : 0 < r), hsub⟩ := hp.hasBasis_zero_ball.mem_iff.mp hU
    ⟨s.inf fun i ↦ hp.ballOpenAddSubgroup _ (hadd i) _ hr, by
      simpa [hr, Seminorm.ball_finset_sup] using hsub⟩

end WithSeminorms
