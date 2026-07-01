module

import RogersRamanujan.Algebra.Group.Pointwise.Set.Basic
import RogersRamanujan.Tactic.CongrApply
import RogersRamanujan.Topology.Algebra.Group.Basic
import RogersRamanujan.Topology.Algebra.InfiniteSum.Nonarchimedean
import RogersRamanujan.Topology.Algebra.Monoid
import RogersRamanujan.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.Algebra.TopologicallyNilpotent
public import Mathlib.Topology.UniformSpace.Cauchy

/-! # Topologically bounded sets in nonarchimedean rings -/

@[expose] public section

open scoped Pointwise
open Filter Topology

/-- A set `S` is topologically bounded if for sufficiently small `U ∈ nhds 0`,
there is `V ∈ nhds 0` with `S * V ⊆ U`. -/
@[mk_iff] structure Set.TopologicallyBounded
    {R : Type*} [Zero R] [Mul R] [TopologicalSpace R] (S : Set R) : Prop where
  exists_mul_subset {U : Set R} (hU : U ∈ 𝓝 0) : ∃ V ∈ 𝓝 0, (S * V : Set R) ⊆ U

theorem Set.topologicallyBounded_iff_eventually_mul_mem
    {R : Type*} [Zero R] [Mul R] [TopologicalSpace R] (S : Set R) :
    S.TopologicallyBounded ↔ ∀ U ∈ 𝓝 0, ∀ᶠ x in 𝓝 0, ∀ s ∈ S, s * x ∈ U := by
  rw [topologicallyBounded_iff]
  refine ⟨fun h U hU ↦ ?_, fun h U hU ↦ ⟨_, h U hU, by grind [mul_subset_iff]⟩⟩
  obtain ⟨V, hVn, hfvu⟩ := h hU
  filter_upwards [hVn] with x hx s hs using hfvu <| Set.mul_mem_mul hs hx

theorem Set.TopologicallyBounded.exists_subset_mul_mem
    {R : Type*} [Zero R] [Mul R] [TopologicalSpace R] {S : Set R}
    (hs : S.TopologicallyBounded) {U : Set R} (hU : U ∈ 𝓝 0) :
    ∃ V ∈ 𝓝 0, V ⊆ U ∧ ∀ s ∈ S, ∀ v ∈ V, s * v ∈ U :=
  let ⟨V, hVn, hfvu⟩ := hs.exists_mul_subset hU
  ⟨U ∩ V, inter_mem hU hVn, Set.inter_subset_left, fun _ hs _ hv ↦ hfvu <| Set.mul_mem_mul hs hv.2⟩

theorem Filter.HasBasis.exists_subset_mul_mem_of_topologicallyBounded
    {R : Type*} [Zero R] [Mul R] [TopologicalSpace R]
    {ι : Type*} {p : ι → Prop} {s : ι → Set R} (h : (𝓝 0).HasBasis p s)
    {B : Set R} (hb : B.TopologicallyBounded) {U : Set R} (hU : U ∈ 𝓝 0) :
    ∃ i : ι, p i ∧ s i ⊆ U ∧ ∀ b ∈ B, ∀ v ∈ s i, b * v ∈ U :=
  let ⟨_V, hvn, hv⟩ := hb.exists_subset_mul_mem hU
  let ⟨i, hpi, hi⟩ := h.mem_iff.mp hvn
  ⟨i, hpi, hi.trans hv.1, fun _b hb _x hx ↦ hv.2 _ hb _ (hi hx)⟩

theorem Filter.HasBasis.topologicallyBounded_iff
    {R : Type*} [Zero R] [Mul R] [TopologicalSpace R]
    {ι : Type*} {p : ι → Prop} {s : ι → Set R} (h : (𝓝 0).HasBasis p s) (B : Set R) :
    B.TopologicallyBounded ↔ ∀ i, p i → ∃ j, p j ∧ s j ⊆ s i ∧ ∀ b ∈ B, ∀ v ∈ s j, b * v ∈ s i :=
  ⟨fun hb _i hi ↦ h.exists_subset_mul_mem_of_topologicallyBounded hb (h.mem_of_mem hi),
  fun H ↦ ⟨fun hu ↦ let ⟨i, hpi, hiu⟩ := h.mem_iff.mp hu
    let ⟨j, hpj, hj⟩ := H i hpi
    ⟨s j, h.mem_of_mem hpj, Set.mul_subset_iff.mpr hj.2 |>.trans hiu⟩⟩⟩

namespace Set.TopologicallyBounded

section zero
variable {R : Type*} [Zero R] [Mul R] [TopologicalSpace R]

theorem mono {S₁ : Set R} (hS₁ : S₁.TopologicallyBounded) {S₂ : Set R} (hS₂ : S₂ ⊆ S₁) :
    S₂.TopologicallyBounded := by
  rw [topologicallyBounded_iff] at hS₁ ⊢
  intro U hU
  obtain ⟨V, hV₁, hV₂⟩ := hS₁ hU
  exact ⟨V, hV₁, by grw [hS₂, hV₂]⟩

@[simp, grind .]
theorem empty : (∅ : Set R).TopologicallyBounded := by simp [topologicallyBounded_iff]; grind

@[simp, grind .]
theorem union {S₁ S₂ : Set R} (hS₁ : S₁.TopologicallyBounded) (hS₂ : S₂.TopologicallyBounded) :
    (S₁ ∪ S₂).TopologicallyBounded := by
  rw [topologicallyBounded_iff] at hS₁ hS₂ ⊢
  intro U hU
  obtain ⟨V₁, hvn₁, hvu₁⟩ := hS₁ hU
  obtain ⟨V₂, hvn₂, hvu₂⟩ := hS₂ hU
  refine ⟨V₁ ∩ V₂, inter_mem hvn₁ hvn₂, ?_⟩
  nth_grw 1 [Set.union_mul, Set.inter_subset_left, hvu₁, Set.inter_subset_right, hvu₂,
    Set.union_self]

theorem _root_.Filter.Tendsto.topologicallyBounded_mul
    {α : Type*} {f g : α → R} {F : Filter α}
    (hg : Tendsto g F (𝓝 0)) (hf : (Set.range f).TopologicallyBounded) :
    Tendsto (fun i ↦ f i * g i) F (𝓝 0) := by
  rw [tendsto_def] at hg ⊢
  rintro U hU
  obtain ⟨V, hvn, hfvu⟩ := hf.1 hU
  filter_upwards [hg V hvn] with i hi using hfvu <| Set.mul_mem_mul (by simp) hi

end zero

section semigroup
variable {R : Type*} [Semigroup R] [Zero R] [TopologicalSpace R]

theorem mul {S₁ S₂ : Set R} (hS₁ : S₁.TopologicallyBounded) (hS₂ : S₂.TopologicallyBounded) :
    (S₁ * S₂).TopologicallyBounded := by
  rw [topologicallyBounded_iff] at hS₁ hS₂ ⊢
  intro U hU
  obtain ⟨V₁, hvn₁, hvu₁⟩ := hS₁ hU
  obtain ⟨V₂, hvn₂, hvu₂⟩ := hS₂ hvn₁
  refine ⟨V₂, hvn₂, ?_⟩
  simp only [Set.mul_subset_iff, Set.mem_mul] at *
  grind

end semigroup

section comm_magma
variable {R : Type*} [CommMagma R] [Zero R] [TopologicalSpace R]

theorem _root_.Filter.Tendsto.mul_topologicallyBounded
    {α : Type*} {f g : α → R} {F : Filter α}
    (hf : Tendsto f F (𝓝 0)) (hg : (Set.range g).TopologicallyBounded) :
    Tendsto (fun i ↦ f i * g i) F (𝓝 0) := by
  simp_rw [mul_comm (f _)]
  exact hf.topologicallyBounded_mul hg

end comm_magma

section mul_zero
variable {R : Type*} [MulZeroClass R] [TopologicalSpace R]

section
variable [ContinuousConstSMul R R]

@[grind .]
theorem singleton (x : R) : ({x} : Set R).TopologicallyBounded where
  exists_mul_subset hU := ⟨_, (continuous_const_smul x).tendsto 0 (by simpa using hU), by simp⟩

@[simp, grind .]
theorem insert (x : R) (s : Set R) (hs : s.TopologicallyBounded) :
    (insert x s).TopologicallyBounded := by
  rw [← Set.union_singleton]
  exact hs.union (.singleton x)

@[grind .]
theorem finset (s : Finset R) : (s : Set R).TopologicallyBounded := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert x s hxs ih => simp [ih]

@[simp, grind .]
theorem of_finite {s : Set R} (hs : s.Finite) : s.TopologicallyBounded :=
  hs.coe_toFinset ▸ .finset _

alias _root_.Set.Finite.topologicallyBounded := of_finite
end

theorem range_of_tendsto_cofinite [ContinuousMul R]
    {ι : Type*} {f : ι → R} {x : R} (hf : Tendsto f cofinite (𝓝 x)) :
    (Set.range f).TopologicallyBounded where
  exists_mul_subset {U} hU := by
    obtain ⟨Vx, hvxn, V, hvn, hvu⟩ := exists_nhds_zero_mul_mem_left hU x
    obtain ⟨V₁, hvn₁, hvu₁⟩ := (of_finite ((hf hvxn).image f)).exists_mul_subset hU
    refine ⟨V ∩ V₁, inter_mem hvn hvn₁, ?_⟩
    simp_rw [Set.mul_subset_iff, Set.forall_mem_range]
    exact fun i y hy ↦ by_cases (fun hi : f i ∈ Vx ↦ hvu _ hi _ hy.1) fun hi ↦
      hvu₁ <| Set.mul_mem_mul ⟨i, hi, rfl⟩ hy.2

alias _root_.Filter.Tendsto.topologicallyBounded' := range_of_tendsto_cofinite

theorem range_of_tendsto [ContinuousMul R] {f : ℕ → R} {x : R} (hf : Tendsto f atTop (𝓝 x)) :
    (Set.range f).TopologicallyBounded :=
  range_of_tendsto_cofinite <| by simpa [Nat.cofinite_eq_atTop] using hf

alias _root_.Filter.Tendsto.topologicallyBounded := range_of_tendsto

end mul_zero

theorem neg {R : Type*} [MonoidWithZero R] [HasDistribNeg R]
    [TopologicalSpace R] [ContinuousNeg R]
    {S : Set R} (hS : S.TopologicallyBounded) :
    (-S).TopologicallyBounded := by
  rw [topologicallyBounded_iff] at hS ⊢
  intro U hU
  obtain ⟨V, hvn, hvu⟩ := hS hU
  refine ⟨_, continuous_neg.continuousAt.preimage_mem_nhds (by simpa using hvn), ?_⟩
  simp_rw [Set.mul_subset_iff]
  exact fun x hx y hy ↦ hvu <| neg_mul_neg x y ▸ Set.mul_mem_mul hx hy

section uniform

-- This feels similar to `Set.TopologicallyBounded.range_of_tendsto_cofinite`
-- but it seems like they don't imply each other.
theorem _root_.CauchySeq.topologicallyBounded_range
    {R : Type*} [Ring R] [UniformSpace R] [IsUniformAddGroup R] [ContinuousMul R]
    {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]
    {f : ι → R} (hf : CauchySeq f) : (Set.range f).TopologicallyBounded := by
  obtain _ | _ := isEmpty_or_nonempty ι
  · simp [range_eq_empty]
  rw [topologicallyBounded_iff_eventually_mul_mem]
  rintro U hu
  obtain ⟨P, hpn, hpu⟩ := exists_nhds_zero_half hu
  obtain ⟨V, hvn, hvp⟩ := exists_nhds_zero_mul_mem hpn
  have := IsUniformAddGroup.cauchy_map_iff_tendsto _ _ |>.mp hf |>.2 hvn
  obtain ⟨N, _, hN⟩ := atTop_basis.prod_self.mem_iff.mp this
  obtain ⟨V₁, hv₁n, hv₁u⟩ := TopologicallyBounded.of_finite ((finite_Iic N).image f) |>.1
    (inter_mem hu hpn)
  filter_upwards [hvn, hv₁n] with x hxv hxv₁
  rw [forall_mem_range]
  rintro i
  by_cases! h : i ≤ N
  · exact (hv₁u (mul_mem_mul ⟨_, h, rfl⟩ hxv₁)).1
  convert hpu _ (hvp _ (@hN (i, N) ⟨h.le, le_refl N⟩) _ hxv) _
    (hv₁u (mul_mem_mul ⟨_, le_refl N, rfl⟩ hxv₁)).2 using 1
  simp [sub_mul]

end uniform

section nonarchimedean
variable {R : Type*} [Ring R] [TopologicalSpace R] [NonarchimedeanRing R]

protected theorem addSubgroupClosure {S : Set R} (hS : S.TopologicallyBounded) :
    (AddSubgroup.closure S : Set R).TopologicallyBounded := by
  simp_rw [hasBasis_nhds_zero_openAddSubgroup.topologicallyBounded_iff,
    true_implies, true_and] at hS ⊢
  congr_apply hS with i j h H b hb x hx : 3
  suffices AddSubgroup.closure S ≤ i.toAddSubgroup.comap (.mulRight x) from this hb
  rw [AddSubgroup.closure_le]
  solve_by_elim

protected theorem closure {S : Set R} (hS : S.TopologicallyBounded) :
    (closure S).TopologicallyBounded := by
  simp_rw [hasBasis_nhds_zero_openAddSubgroup.topologicallyBounded_iff,
    true_implies, true_and] at hS ⊢
  congr_apply hS with i j h H b hb x hx : 3
  suffices closure S ⊆ (· * x) ⁻¹' i from this hb
  rw [(i.isClosed.preimage (by fun_prop)).closure_subset_iff]
  solve_by_elim

theorem range_intCast :
    (Set.range (Int.cast : ℤ → R)).TopologicallyBounded := by
  rw [← coe_addSubgroupClosure_one_eq_range_intCast]
  exact .addSubgroupClosure <| .singleton 1

end nonarchimedean

section complete
variable {R : Type*} [Ring R] [UniformSpace R] [NonarchimedeanRing R]
  [IsUniformAddGroup R] [CompleteSpace R]

theorem summable_mul_pow {f : ℕ → R} {q : R} (hf : (Set.range f).TopologicallyBounded)
    (hq : IsTopologicallyNilpotent q) :
    Summable fun n ↦ f n * q ^ n :=
  NonarchimedeanAddGroup.summable_of_tendsto_atTop_zero <| hq.topologicallyBounded_mul hf

end complete

end Set.TopologicallyBounded

/-! # Define "Bounded Range"

To make chaining proofs easier.

-/

/-- An abbrev for `Set.TopologicallyBounded` in order to chain proofs together using dot notation
more conveniently. -/
abbrev Function.BoundedRange {α β : Type*} [Mul β] [Zero β] [TopologicalSpace β]
    (f : α → β) : Prop :=
  (Set.range f).TopologicallyBounded

theorem Function.BoundedRange.topologicallyBounded
    {α β : Type*} [Mul β] [Zero β] [TopologicalSpace β] {f : α → β}
    (hf : f.BoundedRange) : (Set.range f).TopologicallyBounded := hf
alias Set.TopologicallyBounded.of_boundedRange := Function.BoundedRange.topologicallyBounded

theorem Set.TopologicallyBounded.boundedRange
    {α β : Type*} [Mul β] [Zero β] [TopologicalSpace β] {f : α → β}
    (hf : (Set.range f).TopologicallyBounded) : f.BoundedRange := hf
alias Function.BoundedRange.of_topologicallyBounded := Set.TopologicallyBounded.boundedRange

theorem Filter.Tendsto.boundedRange'
    {α β : Type*} [MulZeroClass β] [TopologicalSpace β] [ContinuousMul β]
    {f : α → β} {x : β} (hf : Tendsto f cofinite (𝓝 x)) : f.BoundedRange :=
  hf.topologicallyBounded'
alias Function.BoundedRange.of_tendsto' := Filter.Tendsto.boundedRange'

theorem Filter.Tendsto.boundedRange
    {β : Type*} [MulZeroClass β] [TopologicalSpace β] [ContinuousMul β]
    {f : ℕ → β} {x : β} (hf : Tendsto f atTop (𝓝 x)) : f.BoundedRange :=
  hf.topologicallyBounded
alias Function.BoundedRange.of_tendsto := Filter.Tendsto.boundedRange

theorem Function.BoundedRange.mul_tendsto_zero
    {α β : Type*} [Mul β] [Zero β] [TopologicalSpace β] {f g : α → β} {s : Filter α}
    (hf : f.BoundedRange) (hg : Tendsto g s (𝓝 0)) :
    Tendsto (fun i ↦ f i * g i) s (𝓝 0) :=
  hg.topologicallyBounded_mul hf

theorem Function.BoundedRange.mul
    {α β : Type*} [Semigroup β] [Zero β] [TopologicalSpace β] {f g : α → β}
    (hf : f.BoundedRange) (hg : g.BoundedRange) :
    (fun i ↦ f i * g i).BoundedRange :=
  (hf.topologicallyBounded.mul hg).mono Set.range_mul_subset

theorem Function.BoundedRange.comp
    {α β γ : Type*} [Mul γ] [Zero γ] [TopologicalSpace γ]
    {f : β → γ} {g : α → β} (hf : f.BoundedRange) : (f ∘ g).BoundedRange :=
  hf.mono <| Set.range_comp_subset_range ..

theorem Function.BoundedRange.neg_one_pow
    {R : Type*} [MonoidWithZero R] [TopologicalSpace R] [ContinuousConstSMul R R]
    [HasDistribNeg R] : ((-1 : R) ^ ·).BoundedRange :=
  .mono (S₁ := {-1, 1}) (by simp) (by grind [neg_one_pow_eq_ite])

theorem CauchySeq.boundedRange
    {R : Type*} [Ring R] [UniformSpace R] [IsUniformAddGroup R] [ContinuousMul R]
    {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]
    {f : ι → R} (hf : CauchySeq f) : f.BoundedRange := hf.topologicallyBounded_range

@[simp] theorem Function.BoundedRange.intCast
    {R : Type*} [Ring R] [TopologicalSpace R] [NonarchimedeanRing R] :
    (Int.cast : ℤ → R).BoundedRange :=
  .range_intCast
