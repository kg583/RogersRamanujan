module

public import RogersRamanujan.Algebra.Group.Units.Basic
import RogersRamanujan.Order.Filter.AtTopBot.Finset
import RogersRamanujan.Order.Filter.Bases.Finite
import RogersRamanujan.RingTheory.NonUnitalSubring.Basic
import RogersRamanujan.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.Algebra.TopologicallyNilpotent
public import Mathlib.Topology.UniformSpace.Cauchy

/-! # Topologically nilpotent elements in nonarchimedean rings

We prove that topologically nilpotent elements form an additive subgroup in a nonarchimedean
commutative ring, and that in a strongly nonarchimedean ring the set of topologically nilpotent
elements is closed.
-/

@[expose] public section

open Filter Topology

open scoped Pointwise

section NonarchimedeanRing
variable {R : Type*} [TopologicalSpace R] [Ring R] [NonarchimedeanRing R]
namespace IsTopologicallyNilpotent

theorem add_of_commute'
    {a b : R} (ha : IsTopologicallyNilpotent a) (hb : IsTopologicallyNilpotent b)
    (h : Commute a b) : IsTopologicallyNilpotent (a + b) := by
  have basis := hasBasis_nhds_zero_openAddSubgroup (G := R)
  simp only [IsTopologicallyNilpotent, true_implies, true_and, atTop_basis.tendsto_iff basis]
  rintro U
  obtain ⟨⟨V₁, V₂⟩, -, hv⟩ := (basis.prod_nhds basis).tendsto_iff basis |>.mp
    (by simpa using continuous_mul.continuousAt (x := ((0 : R), 0)).tendsto) U trivial
  let V := U ⊓ V₁ ⊓ V₂
  obtain ⟨hvu, hv₁, hv₂⟩ : V ≤ U ∧ V ≤ V₁ ∧ V ≤ V₂ := by grind [inf_le_left, inf_le_right]
  have hn := V.mem_nhds_zero
  obtain ⟨N₁, hn₁⟩ := tendsto_atTop'.mp ha _ hn
  obtain ⟨N₂, hn₂⟩ := tendsto_atTop'.mp hb _ hn
  have (x : R) : (x * ·) ⁻¹' V ∈ 𝓝 0 :=
    (continuous_const_mul x).continuousAt.preimage_mem_nhds (by simpa)
  choose N₃ hn₃ using fun i ↦ tendsto_atTop'.mp hb _ (this (a ^ i))
  choose N₄ hn₄ using fun i ↦ tendsto_atTop'.mp ha _ (this (b ^ i))
  let N := (max N₁ ((Finset.range N₂).sup N₄)) + (max N₂ ((Finset.range N₁).sup N₃))
  refine ⟨N, fun n (hn : N ≤ n) ↦ h.add_pow' n ▸ sum_mem fun ⟨m₁, m₂⟩ hm ↦ nsmul_mem (S := U) ?_ _⟩
  rw [Finset.mem_antidiagonal] at hm
  by_cases! hm₁ : m₁ < N₁
  · refine hvu <| hn₃ _ _ <| le_of_add_le_add_left (a := m₁) ?_
    grw [hm, ← hn]
    exact add_le_add (by grind)
      (le_max_of_le_right <| Finset.le_sup <| by simpa)
  by_cases! hm₂ : m₂ < N₂
  · rw [h.pow_pow]
    refine hvu <| hn₄ _ _ <| le_of_add_le_add_right (a := m₂) ?_
    grw [hm, ← hn]
    exact add_le_add
      (le_max_of_le_right <| Finset.le_sup <| by simpa) (by grind)
  exact hv (_, _) ⟨hv₁ <| hn₁ _ hm₁, hv₂ <| hn₂ _ hm₂⟩

theorem zsmul {n : ℤ} {a : R} (ha : IsTopologicallyNilpotent a) :
    IsTopologicallyNilpotent (n • a) := by
  simp only [IsTopologicallyNilpotent, true_and, true_implies, smul_pow,
    atTop_basis.tendsto_iff hasBasis_nhds_zero_openAddSubgroup] at ha ⊢
  exact fun U ↦ (ha U).elim fun N hN ↦ ⟨N, fun n hn ↦ zsmul_mem (hN n hn) _⟩

theorem int_mul {n : ℤ} {a : R} (ha : IsTopologicallyNilpotent a) :
    IsTopologicallyNilpotent (n * a) := by
  simpa using ha.zsmul

theorem nsmul {n : ℕ} {a : R} (ha : IsTopologicallyNilpotent a) :
    IsTopologicallyNilpotent (n • a) := by
  simpa using ha.zsmul (n := n)

theorem nat_mul {n : ℕ} {a : R} (ha : IsTopologicallyNilpotent a) :
    IsTopologicallyNilpotent (n * a) := by
  simpa using ha.zsmul (n := n)

end IsTopologicallyNilpotent
end NonarchimedeanRing

theorem Filter.Tendsto.neg_one_pow_mul
    {G : Type*} [MonoidWithZero G] [HasDistribNeg G]
    [TopologicalSpace G] [ContinuousNeg G]
    {f : ℕ → G} (hf : Tendsto f atTop (𝓝 0)) :
    Tendsto (fun n ↦ (-1) ^ n * f n) atTop (𝓝 0) := by
  rw [tendsto_atTop_nhds] at hf ⊢
  rintro U h0u hou
  obtain ⟨N, hN⟩ := hf (U ∩ (-·) ⁻¹' U) (by simpa) (.inter hou <| hou.preimage continuous_neg)
  refine ⟨N, fun n hn ↦ ?_⟩
  simp [neg_one_pow_eq_ite]
  grind

theorem IsTopologicallyNilpotent.neg
    {G : Type*} [MonoidWithZero G] [HasDistribNeg G]
    [TopologicalSpace G] [ContinuousNeg G] {x : G}
    (hx : IsTopologicallyNilpotent x) : IsTopologicallyNilpotent (-x) := by
  simpa [IsTopologicallyNilpotent, neg_pow x] using hx.neg_one_pow_mul

theorem Filter.Tendsto.neg_one_pow_smul
    {G : Type*} [AddGroup G] [TopologicalSpace G] [ContinuousNeg G]
    {f : ℕ → G} (hf : Tendsto f atTop (𝓝 0)) :
    Tendsto (fun n ↦ (-1) ^ n • f n) atTop (𝓝 0) := by
  rw [tendsto_atTop_nhds] at hf ⊢
  rintro U h0u hou
  obtain ⟨N, hN⟩ := hf (U ∩ (-·) ⁻¹' U) (by simpa) (.inter hou <| hou.preimage continuous_neg)
  refine ⟨N, fun n hn ↦ ?_⟩
  simp [neg_one_pow_eq_ite]
  grind

theorem IsTopologicallyNilpotent.mul_of_commute
    {R : Type*} [MonoidWithZero R] [TopologicalSpace R] [ContinuousMul R]
    {a b : R} (ha : IsTopologicallyNilpotent a)
    (hb : IsTopologicallyNilpotent b)
    (h : Commute a b) : IsTopologicallyNilpotent (a * b) := by
  simpa [IsTopologicallyNilpotent, h.mul_pow] using ha.mul hb

theorem IsTopologicallyNilpotent.mul
    {R : Type*} [CommMonoidWithZero R] [TopologicalSpace R] [ContinuousMul R]
    {a b : R} (ha : IsTopologicallyNilpotent a) (hb : IsTopologicallyNilpotent b) :
    IsTopologicallyNilpotent (a * b) := ha.mul_of_commute hb <| .all ..

section CommNonarchimedean
variable {R : Type*} [TopologicalSpace R] [CommRing R] [NonarchimedeanRing R]

theorem IsTopologicallyNilpotent.add' {a b : R} (ha : IsTopologicallyNilpotent a)
    (hb : IsTopologicallyNilpotent b) :
    IsTopologicallyNilpotent (a + b) :=
  ha.add_of_commute' hb <| .all ..

/-- The set of topologically nilpotent elements forms a non-unital subring
in a nonarchimedean commutative ring. -/
def topologicalNilpotentNonUnitalSubring (R : Type*)
    [TopologicalSpace R] [CommRing R] [NonarchimedeanRing R] : NonUnitalSubring R where
  carrier := {x | IsTopologicallyNilpotent x}
  zero_mem' := .zero
  add_mem' := .add'
  neg_mem' := .neg
  mul_mem' := .mul

@[simp] theorem mem_topologicalNilpotentNonUnitalSubring_iff {x : R} :
    x ∈ topologicalNilpotentNonUnitalSubring R ↔ IsTopologicallyNilpotent x :=
  Iff.rfl

theorem IsTopologicallyNilpotent.one_sub_mul {a b : R}
    (ha : IsTopologicallyNilpotent (1 - a)) (hb : IsTopologicallyNilpotent (1 - b)) :
    IsTopologicallyNilpotent (1 - a * b) :=
  NonUnitalSubring.one_sub_mul_mem (M := topologicalNilpotentNonUnitalSubring R) ha hb

theorem IsTopologicallyNilpotent.sub {a b : R} (ha : IsTopologicallyNilpotent a)
    (hb : IsTopologicallyNilpotent b) :
    IsTopologicallyNilpotent (a - b) := by
  simpa [sub_eq_add_neg] using ha.add' hb.neg

end CommNonarchimedean

theorem isClosed_iff_nhds_zero
    {G : Type*} [TopologicalSpace G] [AddGroup G] [IsTopologicalAddGroup G] {s : Set G} :
    IsClosed s ↔ ∀ x, (∀ U ∈ 𝓝 0, ∃ y ∈ s, y - x ∈ U) → x ∈ s := by
  simp_rw [← closure_subset_iff_isClosed, Set.subset_def, mem_closure_iff_nhds_zero]

theorem neg_one_pow_smul {R : Type*} [Ring R] {n : ℕ} {x : R} :
    (-1) ^ n • x = (-1) ^ n * x := by simp

section CompleteNonarchimedean
variable {R : Type*} [Ring R] [UniformSpace R] [IsUniformAddGroup R]
  [NonarchimedeanRing R] [CompleteSpace R] [T2Space R]
namespace IsTopologicallyNilpotent

theorem isUnit_one_sub_and_bInv_eq_tsum_pow
    {t : R} (ht : IsTopologicallyNilpotent t) :
    IsUnit (1 - t) ∧ bInv (1 - t) = ∑' n, t ^ n :=
  have hs : Summable (t ^ ·) := by
    rwa [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero, Nat.cofinite_eq_atTop]
  isUnit_and_bInv_eq_of_mul_eq_one hs.one_sub_mul_tsum_pow hs.tsum_pow_mul_one_sub

theorem isUnit_one_sub {t : R} (ht : IsTopologicallyNilpotent t) : IsUnit (1 - t) :=
  (isUnit_one_sub_and_bInv_eq_tsum_pow ht).1

theorem isUnit_of_one_sub {t : R} (ht : IsTopologicallyNilpotent (1 - t)) : IsUnit t := by
  simpa using ht.isUnit_one_sub

theorem bInv_one_sub_eq {t : R} (ht : IsTopologicallyNilpotent t) : bInv (1 - t) = ∑' n, t ^ n :=
  (isUnit_one_sub_and_bInv_eq_tsum_pow ht).2
alias _root_.bInv_one_sub_eq_of_isTopologicallyNilpotent := IsTopologicallyNilpotent.bInv_one_sub_eq

end IsTopologicallyNilpotent
end CompleteNonarchimedean

@[simp] theorem isTopologicallyNilpotent_iff_isNilpotent
    {M : Type*} [MonoidWithZero M] [TopologicalSpace M] [DiscreteTopology M] (x : M) :
    IsTopologicallyNilpotent x ↔ IsNilpotent x := by
  refine ⟨?_, IsNilpotent.isTopologicallyNilpotent⟩
  simpa [IsTopologicallyNilpotent, IsNilpotent] using fun n hn ↦ ⟨n, hn n le_rfl⟩

theorem IsTopologicallyNilpotent.pow {R : Type*} [MonoidWithZero R] [TopologicalSpace R]
    {t : R} (ht : IsTopologicallyNilpotent t) {m : ℕ} (hm : m ≠ 0) :
    IsTopologicallyNilpotent (t ^ m) := by
  simp_rw [IsTopologicallyNilpotent, ← pow_mul]
  exact ht.comp (Filter.tendsto_atTop_atTop.mpr fun n ↦
    ⟨n, fun _ h ↦ le_trans h (Nat.le_mul_of_pos_left _ <| pos_of_ne_zero hm)⟩)

theorem IsTopologicallyNilpotent.mul_pow {R : Type*} [CommMonoidWithZero R]
    [TopologicalSpace R] [ContinuousMul R]
    {x y : R} {n : ℕ} (hx : IsTopologicallyNilpotent x) (hy : IsTopologicallyNilpotent y) :
    IsTopologicallyNilpotent (x * y ^ n) := by
  obtain rfl | hn := eq_or_ne n 0
  · simpa
  · exact hx.mul (hy.pow hn)

open scoped Pointwise in
@[simp] theorem isTopologicallyNilpotent_one_iff'
    {R : Type*} [TopologicalSpace R] [MonoidWithZero R] :
    IsTopologicallyNilpotent (1 : R) ↔ 1 ≤ 𝓝 (0 : R) := by
  simp [IsTopologicallyNilpotent, Tendsto, Filter.map_const]

open scoped Pointwise in
theorem isTopologicallyNilpotent_one_iff
    {R : Type*} [TopologicalSpace R] [MonoidWithZero R] [T1Space R] :
    IsTopologicallyNilpotent (1 : R) ↔ (1 : R) = 0 := by simp

theorem IsTopologicallyNilpotent.of_pow
    {M : Type*} [MonoidWithZero M] [TopologicalSpace M] [ContinuousConstSMul M M] {x : M} {n : ℕ}
    (h : IsTopologicallyNilpotent (x ^ n)) (hn : n ≠ 0) : IsTopologicallyNilpotent x := by
  rw [IsTopologicallyNilpotent, atTop_eq_sup hn, tendsto_finsetSup]
  rintro i hi
  simp_rw [tendsto_map'_iff]
  convert h.const_smul (x ^ i) using 2
  · simp [← pow_mul, ← pow_add, add_comm]
  · simp

theorem IsTopologicallyNilpotent.of_pow'
    {M : Type*} [MonoidWithZero M] [TopologicalSpace M]
    [T1Space M] [ContinuousConstSMul M M] {x : M} {n : ℕ}
    (h : IsTopologicallyNilpotent (x ^ n)) : IsTopologicallyNilpotent x := by
  obtain rfl | hn := eq_or_ne n 0
  · simpa [eq_of_zero_eq_one (by simpa [eq_comm] using h) x 0] using .zero
  exact h.of_pow hn
