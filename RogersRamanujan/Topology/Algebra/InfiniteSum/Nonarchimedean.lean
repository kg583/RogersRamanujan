module

import RogersRamanujan.Topology.Algebra.IsUniformGroup.Basic
import RogersRamanujan.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.Algebra.TopologicallyNilpotent
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-! # Infinite sums in nonarchimedean groups
-/

@[expose] public section

open Finset Filter Topology

theorem HasSum.mem {G ι : Type*} [AddCommGroup G] [TopologicalSpace G]
    {σ : Type*} [SetLike σ G] [AddSubgroupClass σ G] {L : SummationFilter ι} [L.NeBot]
    {M : σ} (hm : IsClosed (M : Set G)) {f : ι → G} {x : G}
    (hfx : HasSum f x L) (hf : ∀ i, f i ∈ M) :
    x ∈ M :=
  hm.mem_of_tendsto hfx <| .of_forall fun _ ↦ sum_mem fun i _ ↦ hf i

/-- Generalises `tsum_mem`. -/
theorem tsum_mem' {G ι : Type*} [AddCommGroup G] [TopologicalSpace G]
    {σ : Type*} [SetLike σ G] [AddSubgroupClass σ G] {L : SummationFilter ι} [L.NeBot]
    {M : σ} (hm : IsClosed (M : Set G)) {f : ι → G} (hf : ∀ i, f i ∈ M) :
    ∑'[L] i, f i ∈ M := by
  by_cases hs : Summable f L
  · exact hs.hasSum.mem hm hf
  simp [tsum_eq_zero_of_not_summable hs]

theorem HasSum.sub_mem {G ι : Type*}
    [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    {σ : Type*} [SetLike σ G] [AddSubgroupClass σ G] {L : SummationFilter ι} [L.NeBot]
    {M : σ} (hm : IsClosed (M : Set G)) {f g : ι → G} {x y : G}
    (hfs : HasSum f x L) (hgs : HasSum g y L) (hfg : ∀ i, f i - g i ∈ M) :
    x - y ∈ M :=
  hm.mem_of_tendsto (hfs.sub hgs) <| .of_forall fun _ ↦ sum_mem fun i _ ↦ hfg i

theorem Summable.tsum_sub_mem {G ι : Type*}
    [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    {σ : Type*} [SetLike σ G] [AddSubgroupClass σ G] {L : SummationFilter ι} [L.NeBot]
    {M : σ} (hm : IsClosed (M : Set G)) {f g : ι → G}
    (hfs : Summable f L) (hgs : Summable g L) (hfg : ∀ i, f i - g i ∈ M) :
    ∑'[L] i, f i - ∑'[L] i, g i ∈ M :=
  hfs.hasSum.sub_mem hm hgs.hasSum hfg

/-- Dominated convergence theorem for nonarchimedean additive groups.
If `f n` converges to `l` uniformly and each row `f n` tends to `0`,
then `∑' k, f n k → ∑' k, l k`. -/
theorem Filter.tendsto_tsum_tsum {R ι κ : Type*} (f : ι → κ → R) (l : κ → R)
    {s : Filter ι}
    [AddCommGroup R] [UniformSpace R] [NonarchimedeanAddGroup R]
    [CompleteSpace R] [IsUniformAddGroup R]
    (hfl : TendstoUniformly f l s) (hf : ∀ n, Tendsto (f n) cofinite (𝓝 0)) :
    Tendsto (∑' k, f · k) s (𝓝 (∑' k, l k)) := by
  by_cases! hs : ¬s.NeBot
  · simp at hs; simp [hs]
  have hl : Tendsto l cofinite (𝓝 0) :=
    hfl.tendsto_of_eventually_tendsto (.of_forall hf) tendsto_const_nhds
  simp_rw [IsTopologicalAddGroup.tendstoUniformly_iff _ _ _
    IsUniformAddGroup.rightUniformSpace_eq] at hfl
  rw [(hasBasis_nhds_zero_openAddSubgroup.nhds_of_zero _).tendsto_right_iff]
  refine fun U _ ↦ ?_
  filter_upwards [hfl _ U.mem_nhds_zero] with n hn
  exact Summable.tsum_sub_mem U.isClosed
    (NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero <| by
      simpa [Nat.cofinite_eq_atTop] using hf n)
    (NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero <| by
      simpa [Nat.cofinite_eq_atTop] using hl)
    hn

/-- Dominated convergence theorem for nonarchimedean additive groups.
If `f n` converges to `l` uniformly and each row `f n` tends to `0`,
then `∑' k, f n k → ∑' k, l k`. -/
theorem Filter.tendsto_tsum_tsum_nat {R ι : Type*} (f : ι → ℕ → R) (l : ℕ → R)
    [Preorder ι] [AddCommGroup R] [UniformSpace R] [NonarchimedeanAddGroup R]
    [CompleteSpace R] [IsUniformAddGroup R]
    (hfl : TendstoUniformly f l atTop) (hf : ∀ n, Tendsto (f n) atTop (𝓝 0)) :
    Tendsto (∑' k, f · k) atTop (𝓝 (∑' k, l k)) :=
  tendsto_tsum_tsum f l hfl (by simpa [Nat.cofinite_eq_atTop] using hf)

theorem NonarchimedeanAddGroup.summable_iff_tendsto_atTop_zero
    {R : Type*} [AddCommGroup R] [UniformSpace R] [NonarchimedeanAddGroup R]
    [CompleteSpace R] [IsUniformAddGroup R] (f : ℕ → R) :
    Summable f ↔ Tendsto f atTop (𝓝 0) := by
  simpa [Nat.cofinite_eq_atTop] using summable_iff_tendsto_cofinite_zero f

theorem NonarchimedeanAddGroup.summable_of_tendsto_atTop_zero
    {R : Type*} [AddCommGroup R] [UniformSpace R] [NonarchimedeanAddGroup R]
    [CompleteSpace R] [IsUniformAddGroup R] {f : ℕ → R}
    (hf : Tendsto f atTop (𝓝 0)) : Summable f :=
  (summable_iff_tendsto_atTop_zero f).mpr hf

theorem Summable.pow_of_topologicallyNilpotent
    {R : Type*} [Ring R] [UniformSpace R] [NonarchimedeanRing R]
    [IsUniformAddGroup R] [CompleteSpace R] {q : R}
    (hq : IsTopologicallyNilpotent q) :
    Summable fun n ↦ q ^ n :=
  NonarchimedeanAddGroup.summable_of_tendsto_atTop_zero hq

alias IsTopologicallyNilpotent.summable_pow := Summable.pow_of_topologicallyNilpotent

theorem HasSum.mul_of_nonarchimedean' {α β R : Type*} [Ring R] [TopologicalSpace R]
    [NonarchimedeanRing R] {f : α → R} {g : β → R} {a b : R} (hf : HasSum f a) (hg : HasSum g b) :
    HasSum (fun i : α × β ↦ f i.1 * g i.2) (a * b) :=
  let := IsTopologicalAddGroup.rightUniformSpace R
  have := isUniformAddGroup_of_addCommGroup (G := R)
  hf.mul_of_nonarchimedean hg

theorem HasSum.mul_antidiagonal
    {R ι : Type*} [Ring R] [TopologicalSpace R] [NonarchimedeanRing R]
    [AddCommMonoid ι] [HasAntidiagonal ι]
    {f g : ι → R} {x y : R} (hf : HasSum f x) (hg : HasSum g y) :
    HasSum (fun k ↦ ∑ p ∈ antidiagonal k, f p.1 * g p.2) (x * y) :=
  .sigma (Finset.sigmaAntidiagonalEquivProd.hasSum_iff.mpr (hf.mul_of_nonarchimedean' hg)) fun _ ↦
    Finset.hasSum _ _

variable {A R : Type*} [AddCommMonoid A] [HasAntidiagonal A]
  [Ring R] [UniformSpace R] [IsUniformAddGroup R] [NonarchimedeanRing R] [T0Space R]

/-- The **Cauchy product formula** in a nonarchimedean ring: the product of two infinite sums
equals the sum of antidiagonal convolutions, without requiring an explicit summability hypothesis
on the product family (which is automatic in the nonarchimedean setting). -/
theorem Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_nonarchimedean
    {f g : A → R} (hf : Summable f) (hg : Summable g) :
    (∑' n, f n) * ∑' n, g n = ∑' n, ∑ kl ∈ antidiagonal n, f kl.1 * g kl.2 :=
  hf.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg (hf.mul_of_nonarchimedean hg)

@[to_additive]
theorem NonarchimedeanGroup.cauchySeq_iff_tendsto_div_nhds_one
    {G : Type*} [CommGroup G] [UniformSpace G] [IsUniformGroup G] [NonarchimedeanGroup G]
    (f : ℕ → G) : CauchySeq f ↔ Tendsto (fun n ↦ f (n + 1) / f n) atTop (𝓝 1) :=
  ⟨CauchySeq.tendsto_div_nhds_one, cauchySeq_of_tendsto_div_nhds_one⟩
