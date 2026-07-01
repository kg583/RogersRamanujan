module

import RogersRamanujan.Algebra.Group.Pointwise.Set.Finset
public import RogersRamanujan.Algebra.Group.Units.Basic
import RogersRamanujan.RingTheory.NonUnitalSubring.Basic
import RogersRamanujan.Topology.Algebra.InfiniteSum.Nonarchimedean
import RogersRamanujan.Topology.Algebra.InfiniteSum.SummationFilter
import RogersRamanujan.Topology.Algebra.Nonarchimedean.Basic
public import RogersRamanujan.Topology.Algebra.OpenSubrng
import RogersRamanujan.Topology.Algebra.TopologicallyNilpotent
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.Algebra.TopologicallyNilpotent
public import Mathlib.Topology.UniformSpace.Cauchy

/-! # Strongly nonarchimedean rings

A nonarchimedean ring is *strongly* nonarchimedean if for every neighborhood `U` of `0`, every
element of the ring is eventually multiplied into `U`.
-/

@[expose] public section

open scoped Pointwise Topology
open Finset Filter AddSubgroup SummationFilter

/-- A ring is strongly nonarchimedean if every neighborhood of 0 contains an open subset `V`
satisfying `V * V ⊆ V` and `0 ∈ V`. -/
class StrongNonarchimedeanRing (R : Type*) [Ring R] [TopologicalSpace R] :
    Prop extends NonarchimedeanRing R where
  exists_mul_subset_self (U : Set R) (hU : U ∈ 𝓝 0) :
    ∃ V : Set R, 0 ∈ V ∧ IsOpen V ∧ V ⊆ U ∧ V * V ⊆ V

export StrongNonarchimedeanRing (exists_mul_subset_self)

instance (priority := 100) IsLinearTopology.instStrongNonarchimedeanRing
    {R : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R] : StrongNonarchimedeanRing R where
  is_nonarchimedean U hU := by
    obtain ⟨I, hI, hIU⟩ := (IsLinearTopology.hasBasis_open_ideal (R := R)).mem_iff.mp hU
    exact ⟨⟨I.toAddSubgroup, hI⟩, hIU⟩
  exists_mul_subset_self U hU := by
    obtain ⟨I, hI, hIU⟩ := (IsLinearTopology.hasBasis_open_ideal (R := R)).mem_iff.mp hU
    exact ⟨I, I.zero_mem, hI, hIU, Set.mul_subset_iff.mpr fun a ha b hb => I.mul_mem_left a hb⟩

section ring
variable {R : Type*} [Ring R] [TopologicalSpace R] [StrongNonarchimedeanRing R]

/-- Neighbourhoods of `0` in a strongly nonarchimedean ring have a basis of open non-unital
subrings: each `OpenSubrng` bundles "open", "contains `0`" and "closed under multiplication". -/
theorem hasBasis_nhds_zero_openSubrng :
    (𝓝 (0 : R)).HasBasis (fun _ : OpenSubrng R ↦ True) (↑) := by
  refine (nhds_basis_opens 0).to_hasBasis (fun s ⟨hs0, hs⟩ ↦ ?_)
    fun M _ ↦ ⟨M, ⟨zero_mem M, M.isOpen⟩, le_rfl⟩
  obtain ⟨U, hus⟩ := NonarchimedeanRing.is_nonarchimedean _ <| hs.mem_nhds hs0
  obtain ⟨M, hm0, hm, hms, hmm⟩ := exists_mul_subset_self _ <| U.mem_nhds_zero
  have hmul : ∀ {x y}, x ∈ AddSubgroup.closure M → y ∈ AddSubgroup.closure M →
      x * y ∈ AddSubgroup.closure M := by
    intro x y hx hy
    induction hx, hy using AddSubgroup.closure_induction₂ with
    | mem x y hx hy => exact subset_closure <| hmm <| Set.mul_mem_mul hx hy
    | zero_left x hx => simp
    | zero_right x hx => simp
    | add_left x y hx hy hxy => simp [add_mul, add_mem, *]
    | add_right x y hx hy hxy => simp [mul_add, add_mem, *]
    | neg_left x hx => simp [neg_mul, *]
    | neg_right x hx => simp [mul_neg, *]
  refine ⟨{ carrier := AddSubgroup.closure M
            zero_mem' := zero_mem _
            add_mem' := add_mem
            neg_mem' := neg_mem
            mul_mem' := hmul
            isOpen' := isOpen_of_zero_mem_interior _ ⟨M, ⟨hm, subset_closure⟩, hm0⟩ },
    trivial, ?_⟩
  exact .trans (closure_le U.1 |>.mpr hms) hus

theorem exists_openSubrng_mul_mem (U : OpenSubrng R) (x : R) : ∃ V : OpenSubrng R,
    V ≤ U ∧ ∀ y ∈ V, x * y ∈ U := by
  have hn := U.mem_nhds_zero
  obtain ⟨V, -, hV⟩ := hasBasis_nhds_zero_openSubrng.mem_iff.mp <| Filter.inter_mem hn <|
    continuous_const_mul x |>.continuousAt (x := 0) (by simpa using hn)
  refine ⟨V, SetLike.coe_subset_coe.mp (hV.trans Set.inter_subset_left), fun y hy ↦ ?_⟩
  have := (hV.trans Set.inter_subset_right) hy
  simpa using this

/-- In a `StrongNonarchimedeanRing`, if `x i → 0` and `n i → ∞`, then `x i ^ n i → 0`.
Uses `V * V ⊆ V` from the strong nonarchimedean axiom: once `x i ∈ V`, we have
`x i ^ m ∈ V` for every `m ≥ 1`. -/
theorem tendsto_pow_of_tendsto_zero {ι : Type*} {l : Filter ι}
    {x : ι → R} {n : ι → ℕ}
    (hx : Tendsto x l (nhds 0)) (hn : Tendsto n l atTop) :
    Tendsto (fun i => x i ^ n i) l (nhds 0) := by
  rw [tendsto_def] at hx ⊢
  intro U hU
  obtain ⟨V, hV0, hV, hVU, hVmul⟩ := exists_mul_subset_self U hU
  filter_upwards [hx V (hV.mem_nhds hV0), hn.eventually (eventually_ge_atTop 1)]
    with i hi hni
  exact hVU <| by
    suffices ∀ m, 1 ≤ m → x i ^ m ∈ V from this _ hni
    intro m hm
    induction m with
    | zero => omega
    | succ m ih =>
      cases m with
      | zero => simpa using hi
      | succ m => rw [pow_succ]; exact hVmul (Set.mul_mem_mul (ih (by omega)) hi)

/-- Special case of `tendsto_pow_of_tendsto_zero` where `n = id`. -/
theorem tendsto_pow_self_of_tendsto_zero {x : ℕ → R}
    (hx : Tendsto x atTop (nhds 0)) : Tendsto (fun n => x n ^ n) atTop (nhds 0) :=
  tendsto_pow_of_tendsto_zero hx tendsto_id

end ring

section comm_ring
variable {R : Type*} [CommRing R] [TopologicalSpace R] [StrongNonarchimedeanRing R]

theorem prod_tendsto_zero (a : ℕ → R) (ha : Tendsto a atTop (𝓝 0)) :
    Tendsto (∏ i ∈ range ·, a i) atTop (𝓝 0) := by
  rw [tendsto_atTop_nhds] at ha ⊢
  intro U hu0 hu
  obtain ⟨V, hv0, hv, hvu, hvv⟩ := exists_mul_subset_self U <| hu.mem_nhds hu0
  obtain ⟨N₁, hn₁⟩ := ha V hv0 hv
  have h₁ := hv.preimage (continuous_const_mul (∏ i ∈ range N₁, a i))
  obtain ⟨W, hw0, hw, hwv, hww⟩ := exists_mul_subset_self _ <| h₁.mem_nhds <| by simpa
  obtain ⟨N₂, hn₂⟩ := ha W hw0 hw
  refine ⟨max N₁ N₂ + 2, fun n hn ↦ ?_⟩
  rw [← prod_range_mul_prod_Ico a (show max N₁ N₂ + 1 ≤ n by grind),
    ← prod_range_mul_prod_Ico a (show N₁ ≤ max N₁ N₂ + 1 by grind),
    mul_right_comm]
  refine hvu <| hvv <| Set.mul_mem_mul (hwv ?_) ?_
  · exact prod_mem_of_mul_subset_self hww (by grind) ⟨max N₁ N₂ + 1, by grind⟩
  · exact prod_mem_of_mul_subset_self hvv (by grind) ⟨N₁, by grind⟩

theorem exists_openSubrng_add_mem {a : R} {U : Set R}
    (hU : U ∈ 𝓝 a) : ∃ M : OpenSubrng R, ∀ x ∈ M, x + a ∈ U := by
  obtain ⟨M, -, hMU⟩ := hasBasis_nhds_zero_openSubrng.mem_iff.mp
    ((continuous_add_const a).continuousAt.preimage_mem_nhds (by simpa))
  exact ⟨M, fun x hx ↦ hMU hx⟩

theorem exists_openSubrng_const_mul_mem (M₀ : OpenSubrng R)
    (l : R) : ∃ M : OpenSubrng R, M ≤ M₀ ∧ ∀ x ∈ M, l * x ∈ M₀ := by
  obtain ⟨M, -, hMsub⟩ := hasBasis_nhds_zero_openSubrng.mem_iff.mp
    (Filter.inter_mem M₀.mem_nhds_zero <|
      (continuous_const_mul l).continuousAt.preimage_mem_nhds <| by
        simpa using M₀.mem_nhds_zero)
  refine ⟨M, SetLike.coe_subset_coe.mp (hMsub.trans Set.inter_subset_left), fun y hy ↦ ?_⟩
  have := (hMsub.trans Set.inter_subset_right) hy
  simpa using this

theorem tendsto_pow_mul_pow_choose_two {a q : R} (hq : IsTopologicallyNilpotent q) :
    Tendsto (fun n ↦ a ^ n * q ^ n.choose 2) atTop (𝓝 0) := by
  convert prod_tendsto_zero _ <| by simpa using hq.const_mul a
  rw [prod_mul_distrib, prod_pow_eq_pow_sum, sum_range_id, Nat.choose_two_right]
  simp

theorem isClosed_setOf_isTopologicallyNilpotent :
    IsClosed {x : R | IsTopologicallyNilpotent x} := by
  refine isClosed_iff_nhds_zero.mpr fun x hx ↦
    atTop_basis.tendsto_iff hasBasis_nhds_zero_openSubrng |>.mpr fun U _ ↦ ?_
  obtain ⟨V, hvu, hxvu⟩ := exists_openSubrng_mul_mem U x
  obtain ⟨s, hsn, hsxv⟩ := hx V V.mem_nhds_zero
  obtain ⟨N, hN⟩ := tendsto_atTop_nhds.mp hsn _ (zero_mem V) V.isOpen
  have h₁ : s * (s - x) ∈ U := by
    nth_rw 1 [← sub_add_cancel s x, add_mul]
    exact add_mem (hvu <| mul_mem hsxv hsxv) <| hxvu _ hsxv
  have h₂ {i} (hi : i ≠ 0) : s ^ i * (s - x) ^ i ∈ U := by
    rw [← mul_pow]
    exact NonUnitalSubring.pow_mem h₁ hi
  have h₃ {i} (hi : i ≠ 0) : (s - x) ^ i ∈ U :=
    hvu <| NonUnitalSubring.pow_mem hsxv hi
  refine ⟨2 * N + 1, trivial, fun n (hn : 2 * N < n) ↦ ?_⟩
  rw [← sub_sub_cancel s x, sub_pow]
  refine sum_mem fun i hi ↦ ?_
  rw [← neg_one_pow_smul, ← nsmul_eq_mul', smul_mul_assoc]
  refine nsmul_mem (zsmul_mem ?_ _) _
  by_cases! hi1 : i ≤ N
  · by_cases! hi2 : i = 0
    · simpa [hi2] using h₃ (by omega)
    rw [← Nat.add_sub_cancel' (show i ≤ n - i by omega), pow_add, ← mul_assoc]
    exact mul_mem (h₂ hi2) <| h₃ (by omega)
  by_cases hi2 : n - i = 0
  · simpa [hi2] using hvu <| hN _ hi1.le
  exact mul_mem (hvu <| hN _ hi1.le) (h₃ (by omega))

theorem IsTopologicallyNilpotent.of_tendsto
    {ι : Type*} {f : ι → R} {l : R} {s : Filter ι} [s.NeBot]
    (hf : ∀ᶠ i in s, IsTopologicallyNilpotent (f i)) (hfl : Tendsto f s (𝓝 l)) :
    IsTopologicallyNilpotent l := isClosed_setOf_isTopologicallyNilpotent.mem_of_tendsto hfl hf

end comm_ring

section complete_space
variable {R : Type*} [CommRing R] [UniformSpace R] [CompleteSpace R]
variable [StrongNonarchimedeanRing R] [IsUniformAddGroup R]

theorem multipliable_one_add_conditional_of_tendsto_zero
    {a : ℕ → R} (ha : Tendsto a atTop (𝓝 0)) : Multipliable (1 + a ·) (conditional ℕ) := by
  rw [multipliable_conditional_nat_iff, ← cauchy_map_iff_exists_tendsto, ← CauchySeq]
  refine NonarchimedeanAddGroup.cauchySeq_of_tendsto_sub_nhds_zero <|
    hasBasis_nhds_zero_openSubrng.tendsto_right_iff.mpr fun M _ ↦
    eventually_atTop.mpr ?_
  rw [tendsto_atTop_nhds] at ha
  obtain ⟨N₁, hn₁⟩ := ha _ (zero_mem M) M.isOpen
  have h₁ := M.isOpen.preimage (continuous_const_mul (∏ i ∈ range N₁, (1 + a i)))
  obtain ⟨V, -, hvm⟩ :=
    hasBasis_nhds_zero_openSubrng.mem_iff.mp (h₁.mem_nhds <| by simp)
  obtain ⟨N₂, hn₂⟩ := ha V (zero_mem V) V.isOpen
  refine ⟨max N₁ N₂, fun n hn ↦ ?_⟩
  rw [prod_range_succ, ← mul_sub_one, add_sub_cancel_left, ← prod_range_mul_prod_Ico _ hn,
    ← prod_range_mul_prod_Ico _ (show N₁ ≤ max N₁ N₂ by grind),
    show ∀ a b c d : R, a * b * c * d = b * (a * (c * d)) by intros; ring]
  exact NonUnitalSubring.mul_mem_of_sub_one_mem
    (NonUnitalSubring.prod_one_add_sub_one_mem (by simp_all)) <|
    hvm <| NonUnitalSubring.mul_mem_of_sub_one_mem
      (NonUnitalSubring.prod_one_add_sub_one_mem (by simp_all)) <| by simp_all

theorem multipliable_conditional_of_tendsto_one
    {a : ℕ → R} (ha : Tendsto a atTop (𝓝 1)) : Multipliable a (conditional ℕ) := by
  convert multipliable_one_add_conditional_of_tendsto_zero (a := (a · - 1)) _
  · grind
  convert ha.sub_const 1
  · grind

/-- Generalization of every theorem you have seen thus far. -/
theorem multipliable_one_add_of_tendsto_zero
    {a : ℕ → R} (ha : Tendsto a atTop (𝓝 0)) : Multipliable (1 + a ·) := by
  obtain ⟨l, hl⟩ := (multipliable_conditional_nat_iff _).mp
    (multipliable_one_add_conditional_of_tendsto_zero ha)
  refine ⟨l, ?_⟩
  rw [HasProd, SummationFilter.unconditional_filter, tendsto_atTop_nhds]
  intro U hlU hU
  -- Find M₀ with M₀ + l ⊆ U, then M ⊆ M₀ with l * M ⊆ M₀
  obtain ⟨M₀, hM₀U⟩ := exists_openSubrng_add_mem (hU.mem_nhds hlU)
  obtain ⟨M, hMM₀, hlM⟩ := exists_openSubrng_const_mul_mem M₀ l
  -- Find N: a_i ∈ M for i ≥ N, ∏ range N - l ∈ M
  obtain ⟨N₁, hN₁⟩ := tendsto_atTop_nhds.mp ha _ (zero_mem M) M.isOpen
  obtain ⟨N₂, hN₂⟩ :=
    tendsto_atTop_nhds.mp (tendsto_sub_nhds_zero_iff.mpr hl) _ (zero_mem M) M.isOpen
  set N := max N₁ N₂
  refine ⟨range N, fun s hs ↦ ?_⟩
  rw [← prod_sdiff hs, mul_comm]
  set p := ∏ i ∈ range N, (1 + a i)
  set t := ∏ i ∈ s \ range N, (1 + a i)
  have ht : t - 1 ∈ M := NonUnitalSubring.prod_one_add_sub_one_mem <| by simp_all [N]
  have hp : p - l ∈ M := hN₂ N (by omega)
  -- p * t - l = (p - l) + (l * (t - 1) + (p - l) * (t - 1))
  -- (p - l) ∈ M ⊆ M₀; l * (t-1) ∈ M₀ (via hlM); (p-l)*(t-1) ∈ M*M ⊆ M ⊆ M₀
  -- Sum of three M₀ elements is in M₀ (subgroup). Then (p*t - l) + l ∈ U.
  have hmem : p * t - l ∈ M₀ := by
    rw [show p * t - l = (p - l) + (l * (t - 1) + (p - l) * (t - 1)) by ring]
    exact add_mem (hMM₀ hp) (add_mem (hlM _ ht) (hMM₀ (mul_mem hp ht)))
  simpa using hM₀U _ hmem

/-- Generalization of every theorem you have seen thus far. -/
theorem multipliable_of_tendsto_one
    {a : ℕ → R} (ha : Tendsto a atTop (𝓝 1)) : Multipliable a := by
  convert multipliable_one_add_of_tendsto_zero (tendsto_sub_nhds_zero_iff.mpr ha)
  simp

/-- Generalization of every theorem you have seen thus far. -/
theorem multipliable_one_sub_of_tendsto_zero
    {a : ℕ → R} (ha : Tendsto a atTop (𝓝 0)) : Multipliable (1 - a ·) :=
  multipliable_of_tendsto_one <| by simpa using ha.const_sub 1

/-- If `f n → x` with `f n` eventually topologically nilpotent,
then `bInv (1 - f n) → bInv (1 - x)`. -/
theorem tendsto_bInv_one_sub_of_isTopologicallyNilpotent [T2Space R]
    {ι : Type*} {s : Filter ι} {f : ι → R} {x : R}
    (hf : Tendsto f s (𝓝 x)) (hfn : ∀ᶠ n in s, IsTopologicallyNilpotent (f n)) :
    Tendsto (fun n ↦ bInv (1 - f n)) s (𝓝 (bInv (1 - x))) := by
  by_cases! hs : ¬s.NeBot
  · simp at hs; simp [hs]
  have hxn : IsTopologicallyNilpotent x := .of_tendsto hfn hf
  rw [← Filter.tendsto_sub_const_iff, sub_self] at hf ⊢
  simp only [hasBasis_nhds_zero_openSubrng.tendsto_right_iff] at hf ⊢
  rintro U -
  obtain ⟨N₁, -, hN₁⟩ := atTop_basis.mem_iff.mp <| hxn <| U.mem_nhds_zero
  have key (y : R) : (y * ·) ⁻¹' U ∈ 𝓝 (0 : R) :=
    (continuous_const_mul y).continuousAt.preimage_mem_nhds (by simpa using U.mem_nhds_zero)
  set U₀ := ⋂ i : Fin (N₁ + 1), (x ^ i.val * ·) ⁻¹' U
  obtain ⟨V, hvu₀⟩ := exists_openSubrng_add_mem (U := U₀)
    (Filter.iInter_mem.mpr fun _ ↦ key _)
  have hvu : V ≤ U := fun x hxv ↦ by simpa using Set.mem_iInter.mp (hvu₀ x hxv) 0
  filter_upwards [hfn, hf V trivial] with i hin hixv
  rw [hin.bInv_one_sub_eq, hxn.bInv_one_sub_eq, ← hin.summable_pow.tsum_sub hxn.summable_pow]
  refine tsum_mem U.isClosed fun k ↦ ?_
  rw [← sub_add_cancel (f i) x, add_pow, Finset.sum_range_succ', pow_zero, Nat.sub_zero,
    Nat.choose_zero_right, Nat.cast_one, one_mul, mul_one, add_sub_cancel_right]
  refine sum_mem fun j hj ↦ ?_
  rw [← nsmul_eq_mul']
  refine nsmul_mem ?_ _
  have h₁ : (f i - x) ^ (j + 1) ∈ V := NonUnitalSubring.pow_succ_mem hixv j
  by_cases! hi : k - (j + 1) < N₁
  · simpa [mul_comm] using Set.mem_iInter.mp (hvu₀ _ h₁) ⟨k - (j + 1), by grind⟩
  · exact mul_mem (hvu h₁) (hN₁ hi)

theorem tendsto_bInv_one_of_tendsto_zero_of_isTopologicallyNilpotent [T2Space R]
    {ι : Type*} {s : Filter ι} {f : ι → R}
    (hfl : Tendsto f s (𝓝 0)) (hfn : ∀ᶠ n in s, IsTopologicallyNilpotent (f n)) :
    Tendsto (fun n ↦ bInv (1 - f n)) s (𝓝 1) := by
  simpa using tendsto_bInv_one_sub_of_isTopologicallyNilpotent hfl hfn

/-- If `f n → x` with `1 - f n` and `1 - x` topologically nilpotent, then `bInv (f n) → bInv x`. -/
theorem tendsto_bInv_of_isTopologicallyNilpotent [T2Space R]
    {ι : Type*} {s : Filter ι} {f : ι → R} {x : R}
    (hf : Tendsto f s (𝓝 x))
    (hfn : ∀ᶠ n in s, IsTopologicallyNilpotent (1 - f n)) :
    Tendsto (fun n ↦ bInv (f n)) s (𝓝 (bInv x)) := by
  simpa using tendsto_bInv_one_sub_of_isTopologicallyNilpotent (hf.const_sub _) hfn

instance {ι : Type*} {R : ι → Type*}
    [∀ i, Ring (R i)] [∀ i, TopologicalSpace (R i)] [∀ i, StrongNonarchimedeanRing (R i)] :
    StrongNonarchimedeanRing ((i : ι) → R i) where
  exists_mul_subset_self _U hU := by
    obtain ⟨⟨_I, s⟩, ⟨hif, -⟩, hiu⟩ := (nhds_pi (A := R) ▸ Filter.hasBasis_pi fun i ↦
      hasBasis_nhds_zero_openSubrng (R := R i)).mem_iff.mp hU
    exact ⟨OpenSubrng.pi hif s, by simp, (OpenSubrng.pi hif s).isOpen, hiu,
      Set.mul_subset_iff.mpr fun _x hx _y hy _i hi ↦ mul_mem (hx _i hi) (hy _i hi)⟩

instance (priority := 100) {R : Type*}
    [TopologicalSpace R] [DiscreteTopology R] [Ring R] : StrongNonarchimedeanRing R where
  exists_mul_subset_self := by simpa using fun _ _ ↦ ⟨{0}, by simpa⟩

end complete_space
