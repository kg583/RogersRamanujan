module

public import RogersRamanujan.Order.Filter.Unbounded.Basic
public import RogersRamanujan.Topology.Algebra.Nonarchimedean.Bases
import RogersRamanujan.Topology.Instances.Int
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Algebra.TopologicallyNilpotent
import Mathlib.Topology.MetricSpace.Bounded

/-! # IsSubgroupsBasis

A typeclass connecting a family of additive subgroups `B : ι → AddSubgroup A` to the topology
on `A`, asserting that the `B i` form a neighborhood basis of zero. This avoids passing
`hasBasis` hypotheses explicitly.
-/

@[expose] public section

open Filter Topology

/-- `IsSubgroupsBasis B` asserts that the family `B : ι → AddSubgroup A` forms a basis of
neighborhoods of zero for the existing topology on `A`. -/
class IsSubgroupsBasis {A ι : Type*} [AddGroup A] [TopologicalSpace A]
    (B : ι → AddSubgroup A) : Prop where
  hasBasis_nhds_zero (B) : (𝓝 (0 : A)).HasBasis (fun _ ↦ True) (B ·)

namespace IsSubgroupsBasis

section add_group
variable {A ι : Type*} [AddGroup A] [TopologicalSpace A] (B : ι → AddSubgroup A)
  [IsSubgroupsBasis B]
include B

theorem mem_nhds_zero (i : ι) : (B i : Set A) ∈ 𝓝 0 :=
  IsSubgroupsBasis.hasBasis_nhds_zero B |>.mem_of_mem trivial

theorem nonarchimedeanAddGroup [IsTopologicalAddGroup A] : NonarchimedeanAddGroup A where
  is_nonarchimedean U hU := by
    obtain ⟨i, _, hi⟩ := (hasBasis_nhds_zero B).mem_iff.mp hU
    exact ⟨⟨B i, (B i).isOpen_of_mem_nhds (mem_nhds_zero B i)⟩, hi⟩

end add_group

section ring
variable {A ι : Type*} [Nonempty ι] [Ring A] [τ : TopologicalSpace A] {B : ι → AddSubgroup A}
  (hb : RingSubgroupsBasis B) [IsSubgroupsBasis B]

theorem topology_eq [IsTopologicalAddGroup A] : hb.topology = τ :=
  IsTopologicalAddGroup.ext inferInstance inferInstance <| Filter.ext fun _ ↦ by
    rw [hb.hasBasis_nhds_zero.mem_iff, (IsSubgroupsBasis.hasBasis_nhds_zero B).mem_iff]

end ring

end IsSubgroupsBasis

namespace BoundedRingSubgroupsBasis

open scoped Pointwise

variable {A ι : Type*} [Ring A] [UniformSpace A] [IsUniformAddGroup A]
  [CompleteSpace A] [NonarchimedeanAddGroup A]
  {B : ι → AddSubgroup A} [IsSubgroupsBasis B]

/-- In a complete nonarchimedean ring with a `BoundedRingSubgroupsBasis`, the series
`∑ f(a) * q^{n(a)}` is summable whenever `q` is topologically nilpotent, the mode function
`n` is unbounded, and the coefficients `f(a)` are uniformly bounded in some `B k`. -/
theorem summable_mul_pow (hB : BoundedRingSubgroupsBasis B)
    {α : Type*} {n : α → ℕ} (hn : Unbounded n)
    {q : A} (hq : IsTopologicallyNilpotent q)
    {f : α → A} {k : ι} (hf : ∀ a, f a ∈ B k) :
    Summable fun a ↦ f a * q ^ n a := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  refine (IsSubgroupsBasis.hasBasis_nhds_zero B).tendsto_right_iff.mpr fun i _ => ?_
  obtain ⟨j, hj⟩ := hB.mul_bounded_left k i
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (hq.eventually_mem (IsSubgroupsBasis.mem_nhds_zero B j))
  have hfin := Filter.Unbounded.nat_def.mp hn
    (Filter.eventually_atTop.mpr ⟨N, fun _ h => h⟩)
  exact Filter.eventually_cofinite.mpr (hfin.subset
    fun a ha h => ha (hj (Set.mul_mem_mul (hf a) (hN _ h))))

/-- Variant of `summable_mul_pow` with ℤ-valued exponents. When `q` is a unit and topologically
nilpotent, and the mode `n : α → ℤ` tends to `+∞`, the series `∑ f(a) * q ^ n(a)` converges. -/
theorem summable_mul_zpow (hB : BoundedRingSubgroupsBasis B)
    {α : Type*} {n : α → ℤ} (hn : Unbounded n)
    (q : Aˣ) (hq : IsTopologicallyNilpotent q.val)
    {f : α → A} {k : ι} (hf : ∀ a, f a ∈ B k) :
    Summable fun a ↦ f a * ↑(q ^ n a) :=
  (hB.summable_mul_pow (hn.comp_atTop Int.tendsto_toNat_atTop) hq hf).congr_cofinite <| by
    filter_upwards [hn.eventually <| eventually_ge_atTop 0]
    exact fun i hi ↦ by rw [← Int.natCast_toNat_eq_self.mpr hi, zpow_natCast]; rfl

end BoundedRingSubgroupsBasis
