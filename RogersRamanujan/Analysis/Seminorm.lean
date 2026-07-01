module

public import Mathlib.Analysis.Seminorm

/-! # Seminorms
-/

@[expose] public section

namespace Seminorm

/-- The open ball of radius `r` around `0` for an ultrametric seminorm, as an additive subgroup. -/
def ballAddSubgroup
    {𝕜 E : Type*} [NormedRing 𝕜] [AddGroup E] [SMul 𝕜 E]
    (p : Seminorm 𝕜 E) (hp : ∀ x y, p (x + y) ≤ max (p x) (p y))
    (r : ℝ) (hr : 0 < r) : AddSubgroup E where
  carrier := {x | p x < r}
  zero_mem' := by grind
  add_mem' := by grind
  neg_mem' := by simp

@[simp] theorem coe_ballAddSubgroup
    {𝕜 E : Type*} [NormedRing 𝕜] [AddCommGroup E] [SMul 𝕜 E]
    (p : Seminorm 𝕜 E) (hp : ∀ x y, p (x + y) ≤ max (p x) (p y))
    (r : ℝ) (hr : 0 < r) :
    ((p.ballAddSubgroup hp r hr : AddSubgroup E) : Set E) = p.ball 0 r := by
  ext; simp [Seminorm.ballAddSubgroup]

@[simp] theorem finset_sup_apply_le_iff
    {𝕜 E ι : Type*} [SeminormedRing 𝕜]
    [AddCommGroup E] [Module 𝕜 E] {p : ι → Seminorm 𝕜 E} {s : Finset ι}
    {x : E} {a : ℝ} (ha : 0 ≤ a) :
    s.sup p x ≤ a ↔ ∀ i ∈ s, p i x ≤ a := by
  lift a to NNReal using ha
  simp [Seminorm.finset_sup_apply]
  simp [← NNReal.coe_le_coe]

@[simp] theorem finset_sup_apply_lt_iff
    {𝕜 E ι : Type*} [SeminormedRing 𝕜]
    [AddCommGroup E] [Module 𝕜 E] {p : ι → Seminorm 𝕜 E} {s : Finset ι}
    {x : E} {a : ℝ} (ha : 0 < a) :
    s.sup p x < a ↔ ∀ i ∈ s, p i x < a := by
  lift a to NNReal using ha.le
  replace ha : 0 < a := ha
  simp [Seminorm.finset_sup_apply, Finset.sup_lt_iff ha]
  simp [← NNReal.coe_lt_coe]

end Seminorm
