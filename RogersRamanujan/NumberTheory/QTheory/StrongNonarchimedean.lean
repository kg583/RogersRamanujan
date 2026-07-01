module

import RogersRamanujan.NumberTheory.QTheory.Basic
public import RogersRamanujan.NumberTheory.QTheory.Defs
import RogersRamanujan.NumberTheory.QTheory.Nonarchimedean
import RogersRamanujan.NumberTheory.QTheory.Topology
import RogersRamanujan.RingTheory.MvPowerSeries.Evaluation
import RogersRamanujan.RingTheory.MvPowerSeries.PiTopology
import RogersRamanujan.RingTheory.NonUnitalSubring.Basic
import RogersRamanujan.Topology.Algebra.InfiniteSum.Defs
import RogersRamanujan.Topology.Algebra.InfiniteSum.NatInt
public import RogersRamanujan.Topology.Algebra.Nonarchimedean.Strong
import RogersRamanujan.Topology.Algebra.SeparationQuotient.Basic
import RogersRamanujan.Topology.Algebra.SeparationQuotient.Nonarchimedean
import RogersRamanujan.Topology.Separation.Regular
import Mathlib.RingTheory.MvPowerSeries.LinearTopology

/-! # qPochhammerInf in strong nonarchimedean rings

We prove that in a complete strong nonarchimedean ring, if `q` is topologically nilpotent, then
`(a; q)_∞` is unconditionally multipliable and splits as
`(a; q)_n * (a * q ^ n; q)_∞`.
-/

@[expose] public section

open Finset Filter Topology SummationFilter LeAtTop
open scoped QTheory

section strong
variable {R : Type*} [CommRing R] [UniformSpace R] [CompleteSpace R]
  [StrongNonarchimedeanRing R] [IsUniformAddGroup R]

theorem multipliable_one_sub_mul_pow {a q : R} (hq : IsTopologicallyNilpotent q) :
    Multipliable (1 - a * q ^ ·) :=
  multipliable_of_tendsto_one <| by simpa using (hq.const_mul a).const_sub 1

theorem hasProd_qPochhammerInf {a q : R} (hq : IsTopologicallyNilpotent q) :
    HasProd (1 - a * q ^ ·) (a; q)_∞ :=
  (multipliable_one_sub_mul_pow hq).hasProd_of_le le_atTop

theorem hasProd_qPochhammerInf_conditional {a q : R} (hq : IsTopologicallyNilpotent q) :
    HasProd (1 - a * q ^ ·) (a; q)_∞ (.conditional ℕ) :=
  (hasProd_qPochhammerInf hq).mono_left le_atTop

theorem tendsto_qPochhammer_qPochhammerInf {a q : R} (hq : IsTopologicallyNilpotent q) :
    Tendsto (qPochhammer a q) atTop (𝓝 (a; q)_∞) :=
  (hasProd_qPochhammerInf_conditional hq).tendsto_prod_range

-- TODO: Extract this to a proof that it is uniformly convergent. (remove complete)
theorem tendsto_qPochhammer_nhds_atTop {a q : R} (hq : IsTopologicallyNilpotent q) :
    Tendsto (fun p : R × ℕ ↦ qPochhammer p.1 q p.2) (𝓝 a ×ˢ atTop) (𝓝 (a; q)_∞) := by
  rw [((basis_sets _).prod atTop_basis).tendsto_iff
    (hasBasis_nhds_zero_openSubrng.nhds_of_zero _)]
  rintro U -
  obtain ⟨V, hvu, havu⟩ := exists_openSubrng_mul_mem U (a; q)_∞
  have key : Tendsto (fun p : R × ℕ ↦ p.1 * q ^ p.2) (𝓝 a ×ˢ atTop) (𝓝 0) := by
    simpa using tendsto_fst.mul (hq.comp tendsto_snd)
  obtain ⟨⟨V₁, N₁⟩, ⟨hv₁, -⟩, hN₁⟩ := ((basis_sets _).prod atTop_basis).mem_iff.mp
    (key V.mem_nhds_zero)
  obtain ⟨N₂, -, hN₂⟩ := atTop_basis.mem_iff.mp (tendsto_sub_nhds_zero_iff.mpr
    (tendsto_qPochhammer_qPochhammerInf (a := a) hq) V.mem_nhds_zero)
  set N := max N₁ N₂
  have hv₂ := tendsto_sub_nhds_zero_iff.mpr
    ((qPochhammer_continuous_fst (q := q) (n := N)).tendsto a) V.mem_nhds_zero
  rw [Filter.mem_map] at hv₂
  refine ⟨(_, N), ⟨inter_mem hv₁ hv₂, trivial⟩, fun ⟨x, k⟩ ⟨hx, hk⟩ ↦ ?_⟩
  dsimp at *
  obtain ⟨k, rfl⟩ := exists_add_of_le (show N ≤ k from hk)
  rw [qPochhammer_add',
    show (x; q)_N * (x * q ^ N; q)_k - (a; q)_∞ =
      (((x; q)_N - (a; q)_N) + ((a; q)_N - (a; q)_∞)) * (x * q ^ N; q)_k +
      (a; q)_∞ * ((x * q ^ N; q)_k - 1) by ring]
  have key : (x * q ^ N; q)_k - 1 ∈ V :=
    qPochhammer_sub_one_mem fun i hik ↦ by
    simpa [mul_assoc, ← pow_add] using @hN₁ (_, _) ⟨hx.1, by grind⟩
  exact add_mem (hvu <| NonUnitalSubring.mul_mem_of_mem_of_sub_one_mem
    (add_mem hx.2 (hN₂ (by grind))) key) (havu _ key)

theorem qPochhammerInf_continuous {q : R} (hq : IsTopologicallyNilpotent q) :
    Continuous (qPochhammerInf · q) :=
  continuous_iff_continuousAt.mpr fun _a ↦ (tendsto_qPochhammer_nhds_atTop hq).of_prod' <|
    .of_forall fun _x ↦ tendsto_qPochhammer_qPochhammerInf hq

/-- If `q` is topologically nilpotent, then `(a * q ^ m; q)_∞ → 1` as `m → ∞`.
This follows from continuity of `qPochhammerInf · q` and `a * q ^ m → 0`. -/
theorem tendsto_qPochhammerInf_shift_one {a q : R} (hq : IsTopologicallyNilpotent q) :
    Tendsto (fun m => (a * q ^ m; q)_∞) atTop (nhds 1) := by
  simpa [Function.comp_def] using
    (qPochhammerInf_continuous hq).tendsto 0 |>.comp (by simpa using hq.const_mul a)

variable [T2Space R]

-- TODO: remove Strong
theorem tendsto_bInv_qPochhammer_bInv_qPochhammerInf
    {q : R} (hq : IsTopologicallyNilpotent q) :
    Tendsto (bInv <| qPochhammer q q ·) atTop (𝓝 <| bInv (q; q)_∞) :=
  tendsto_bInv_of_isTopologicallyNilpotent (tendsto_qPochhammer_qPochhammerInf hq)
    (.of_forall fun _ ↦ .one_sub_qPochhammer hq hq _)

theorem qPochhammerInf_eq_tprod {a q : R} (hq : IsTopologicallyNilpotent q) :
    (a; q)_∞ = ∏' i, (1 - a * q ^ i) :=
  tprod_eq_of_multipliable_unconditional <| multipliable_one_sub_mul_pow hq

theorem qPochhammerInf_eq_qPochhammer_mul_qPochhammerInf
    {a q : R} (n : ℕ) (hq : IsTopologicallyNilpotent q) :
    (a; q)_∞ = (a; q)_n * (a * q ^ n; q)_∞ := by
  have hm := multipliable_one_sub_mul_pow hq (a := a * q ^ n)
  simp only [qPochhammerInf_eq_tprod hq, qPochhammer, mul_assoc, ← pow_add, add_comm n] at hm ⊢
  exact hm.prod_mul_tprod_nat_mul' (f := (1 - a * q ^ ·)) |>.symm

theorem qPochhammerInf_eq_prod_range {a q : R} {m : ℕ} (hm : m ≠ 0)
    (hq : IsTopologicallyNilpotent q) :
    (a; q)_∞ = ∏ j ∈ Finset.range m, (a * q ^ j; q ^ m)_∞ := by
  have hqm : IsTopologicallyNilpotent (q ^ m) := by
    simp_rw [IsTopologicallyNilpotent, ← pow_mul]
    exact hq.comp (Filter.tendsto_atTop_atTop.mpr fun n =>
      ⟨n, fun _ h => le_trans h (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hm))⟩)
  have hlim : Tendsto (fun k => (a; q)_(m * k)) atTop (𝓝 (a; q)_∞) :=
    (tendsto_qPochhammer_qPochhammerInf hq).comp (Filter.tendsto_atTop_atTop.mpr fun N =>
      ⟨N, fun n hn => le_trans hn (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hm))⟩)
  have hrlim : Tendsto (fun k => ∏ j ∈ Finset.range m, qPochhammer (a * q ^ j) (q ^ m) k)
      atTop (𝓝 (∏ j ∈ Finset.range m, (a * q ^ j; q ^ m)_∞)) :=
    tendsto_finsetProd _ fun j _ => tendsto_qPochhammer_qPochhammerInf hqm
  exact tendsto_nhds_unique (hlim.congr fun k => qPochhammer_mul_eq_prod_range m k) hrlim

theorem qPochhammer_dvd_qPochhammerInf {a q : R} {n : ℕ}
    (hq : IsTopologicallyNilpotent q) : (a; q)_n ∣ (a; q)_∞ := by
  rw [qPochhammerInf_eq_qPochhammer_mul_qPochhammerInf n hq]
  simp

theorem qPochhammerInf_mul_pow_dvd_qPochhammerInf {a q : R} {n : ℕ}
    (hq : IsTopologicallyNilpotent q) : (a * q ^ n; q)_∞ ∣ (a; q)_∞ := by
  nth_rw 2 [qPochhammerInf_eq_qPochhammer_mul_qPochhammerInf n hq]
  simp

theorem qPochhammerInf_eq_one_sub_mul_qPochhammerInf {a q : R} (hq : IsTopologicallyNilpotent q) :
    (a; q)_∞ = (1 - a) * (a * q; q)_∞ := by
  rw [qPochhammerInf_eq_qPochhammer_mul_qPochhammerInf 1 hq]
  simp

/-- `(a; q)_∞` is unit implies `(a; q)_n` is unit. -/
@[simp] lemma isUnit_qPochhammer_of_isUnit_qPochhammerInf {a q : R}
    (hq : IsTopologicallyNilpotent q)
    (ha : IsUnit (a; q)_∞) (n : ℕ) : IsUnit (a; q)_n :=
  isUnit_of_dvd_unit (qPochhammer_dvd_qPochhammerInf hq) ha

/-- `(a; q)_∞` is unit implies `(aq^n; q)_n` is unit. -/
@[simp] lemma isUnit_qPochhammerInf_mul_pow_of_isUnit_qPochhammerInf {a q : R}
    (hq : IsTopologicallyNilpotent q)
    (ha : IsUnit (a; q)_∞) (n : ℕ) : IsUnit (a * q ^ n; q)_∞ :=
  isUnit_of_dvd_unit (qPochhammerInf_mul_pow_dvd_qPochhammerInf hq) ha

/-- `(a)_(n) = (a)_∞ * ((a * q^n)_∞)⁻¹` when `(a)_∞` is a unit. -/
lemma qPochhammer_eq_qPochhammerInf_mul_bInv_qPochhammerInf_shift {a q : R}
    (hq : IsTopologicallyNilpotent q) (ha : IsUnit (a; q)_∞) (n : ℕ) :
    (a; q)_n = (a; q)_∞ * bInv (a * q ^ n; q)_∞ := by
  have key := isUnit_qPochhammerInf_mul_pow_of_isUnit_qPochhammerInf hq ha n
  rw [qPochhammerInf_eq_qPochhammer_mul_qPochhammerInf n hq]
  simp [mul_assoc, key]

/-- `((a)_(n))⁻¹ = (a * q^n)_∞ * ((a)_∞)⁻¹` when `(a)_∞` is a unit. -/
lemma bInv_qPochhammer_eq_qPochhammerInf_shift_mul_bInv_qPochhammerInf {a q : R} {n : ℕ}
    (hq : IsTopologicallyNilpotent q) (ha : IsUnit (a; q)_∞) :
    bInv (a; q)_n = (a * q ^ n; q)_∞ * bInv (a; q)_∞ := by
  have h₁ := isUnit_qPochhammerInf_mul_pow_of_isUnit_qPochhammerInf hq ha n
  have h₂ := isUnit_qPochhammer_of_isUnit_qPochhammerInf hq ha n
  rw [qPochhammer_eq_qPochhammerInf_mul_bInv_qPochhammerInf_shift hq ha]
  simp [*]

/-- `bInv((a * q^n)_∞) = ((a)_∞)⁻¹ * (a)_(n)` when `(a)_∞` is a unit. -/
lemma bInv_qPochhammerInf_shift {a q : R}
    (hq : IsTopologicallyNilpotent q) (ha : IsUnit (a; q)_∞) (n : ℕ) :
    bInv (a * q ^ n; q)_∞ = bInv (a; q)_∞ * (a; q)_n := by
  rw [qPochhammer_eq_qPochhammerInf_mul_bInv_qPochhammerInf_shift hq ha]
  simp [ha]

/-- `bInv((a * q)_∞) = ((a)_∞)⁻¹ * (1 - a)` when `(a)_∞` is a unit. -/
lemma bInv_qPochhammerInf_mul {a q : R}
    (hq : IsTopologicallyNilpotent q) (ha : IsUnit (a; q)_∞) :
    bInv (a * q; q)_∞ = bInv (a; q)_∞ * (1 - a) := by
  simpa using bInv_qPochhammerInf_shift hq ha 1

/-- `(a * q^m)_∞ = ((a)_(m))⁻¹ * (a)_∞` when `(a)_∞` is a unit. -/
lemma qPochhammerInf_shift_eq_bInv_qPochhammer_mul {a q : R}
    (hq : IsTopologicallyNilpotent q) (ha : IsUnit (a; q)_∞) (m : ℕ) :
    (a * q ^ m; q)_∞ = bInv (a; q)_m * (a; q)_∞ := by
  rw [bInv_qPochhammer_eq_qPochhammerInf_shift_mul_bInv_qPochhammerInf hq ha]
  simp [mul_assoc, ha]

theorem tendsto_bInv_qPochhammer_bInv_qPochhammerInf' {a q : R}
    (hq : IsTopologicallyNilpotent q) (ha : IsUnit (a; q)_∞) :
    Tendsto (bInv (a; q)_·) atTop (𝓝 <| bInv (a; q)_∞) := by
  simpa [bInv_qPochhammer_eq_qPochhammerInf_shift_mul_bInv_qPochhammerInf hq ha, hq] using
    ((qPochhammerInf_continuous hq).tendsto 0).comp (by simpa using hq.const_mul a) |>.mul_const
      (bInv (a; q)_∞)

end strong

section strong_map
variable {R S F : Type*}
  [CommRing R] [UniformSpace R] [StrongNonarchimedeanRing R] [CompleteSpace R] [IsUniformAddGroup R]
  [CommRing S] [TopologicalSpace S]
  [FunLike F R S] [RingHomClass F R S] (f : F) (hf : Continuous f)
  (a : R) {q : R} (hq : IsTopologicallyNilpotent q)
include hf hq

theorem hasProd_map_qPochhammerInf' :
    HasProd (1 - f a * f q ^ ·) (f (a; q)_∞) :=
  ((hasProd_qPochhammerInf hq).map f hf).congr_fun <| by simp

theorem hasProd_map_qPochhammerInf_conditional' :
    HasProd (1 - f a * f q ^ ·) (f (a; q)_∞) (.conditional ℕ) :=
  ((hasProd_qPochhammerInf_conditional hq).map f hf).congr_fun <| by simp

@[simp] theorem map_qPochhammerInf [T2Space S] :
    f (a; q)_∞ = (f a; f q)_∞ :=
  (hasProd_map_qPochhammerInf_conditional' f hf a hq).tprod_eq.symm

theorem hasProd_map_qPochhammerInf [R1Space S] :
    HasProd (1 - f a * f q ^ ·) ((f a; f q)_∞) :=
  (hasProd_map_qPochhammerInf' f hf a hq).multipliable.hasProd_of_le le_atTop

theorem hasProd_map_qPochhammerInf_conditional :
    HasProd (1 - f a * f q ^ ·) ((f a; f q)_∞) (.conditional ℕ) :=
  (hasProd_map_qPochhammerInf_conditional' f hf a hq).multipliable.hasProd

theorem tendsto_map_qPochhammer_qPochhammerInf' :
    Tendsto ((f a; f q)_·) atTop (𝓝 (f (a; q)_∞)) :=
  (hasProd_map_qPochhammerInf_conditional' f hf a hq).tendsto_prod_range

theorem tendsto_map_qPochhammer_qPochhammerInf :
    Tendsto ((f a; f q)_·) atTop (𝓝 (f a; f q)_∞) :=
  (hasProd_map_qPochhammerInf_conditional f hf a hq).tendsto_prod_range

end strong_map

section nilpotent_map
variable {R S F : Type*}
  [CommRing R] [UniformSpace R] [NonarchimedeanRing R] [CompleteSpace R] [IsUniformAddGroup R]
  [CommRing S] [TopologicalSpace S]
  [FunLike F R S] [RingHomClass F R S] (f : F) (hf : Continuous f)
  {a q : R} (ha : IsTopologicallyNilpotent a) (hq : IsTopologicallyNilpotent q)
include ha hq

open MvPowerSeries SeparationQuotient
open scoped WithPiTopology

theorem multipliable_one_sub_mul_pow_of_isTopologicallyNilpotent_of_t2Space [T2Space R] :
    Multipliable (1 - a * q ^ ·) := by
  let g : MvPowerSeries (Fin 2) ℤ →+* R := eval (Int.castRingHom R) ![a, q]
  obtain ⟨g0, g1⟩ : g (.X 0) = a ∧ g (.X 1) = q := by simp [g, ha, hq]
  have hx1 : IsTopologicallyNilpotent (X (R := ℤ) (σ := Fin 2) 1) := by simp
  simpa [Function.comp_def, g0, g1] using
    (multipliable_one_sub_mul_pow (a := X 0) hx1).map g (by fun_prop)

/-- Assuming topological nilpotence, we relax the condition on the ring to being non-archimedean. -/
theorem multipliable_one_sub_mul_pow_of_isTopologicallyNilpotent :
    Multipliable (1 - a * q ^ ·) := by
  refine (SeparationQuotient.isInducing_mk.multipliable_iff_tprod_comp_mem_range
      (g := SeparationQuotient.mkRingHom) _).mpr
    ⟨?_, by simp [-Set.mem_range, SeparationQuotient.surjective_mk.range_eq]⟩
  convert multipliable_one_sub_mul_pow_of_isTopologicallyNilpotent_of_t2Space
    (ha.map (φ := mkRingHom) continuous_mk)
    (hq.map (φ := mkRingHom) continuous_mk)
  all_goals rfl

/-- Assuming topological nilpotence, we relax the condition on the ring to being non-archimedean. -/
theorem hasProd_qPochhammerInf_of_isTopologicallyNilpotent :
    HasProd (1 - a * q ^ ·) (a; q)_∞ :=
  (multipliable_one_sub_mul_pow_of_isTopologicallyNilpotent ha hq).hasProd_of_le le_atTop

include hf

/-- Assuming topological nilpotence, we relax the condition on the ring to being non-archimedean. -/
theorem hasProd_map_qPochhammerInf_of_isTopologicallyNilpotent' :
    HasProd (1 - f a * f q ^ ·) (f (a; q)_∞) := by
  simpa [Function.comp_def] using
    (hasProd_qPochhammerInf_of_isTopologicallyNilpotent ha hq).map f hf

/-- Assuming topological nilpotence, we relax the condition on the ring to being non-archimedean. -/
theorem hasProd_map_qPochhammerInf_conditional_of_isTopologicallyNilpotent' :
    HasProd (1 - f a * f q ^ ·) (f (a; q)_∞) (.conditional ℕ) :=
  (hasProd_map_qPochhammerInf_of_isTopologicallyNilpotent' f hf ha hq).mono_left le_atTop

/-- Assuming topological nilpotence, we relax the condition on the ring to being non-archimedean. -/
@[simp] theorem map_qPochhammerInf_of_isTopologicallyNilpotent [T2Space S] :
    f (a; q)_∞ = (f a; f q)_∞ :=
  (hasProd_map_qPochhammerInf_conditional_of_isTopologicallyNilpotent' f hf ha hq).tprod_eq.symm

theorem hasProd_map_qPochhammerInf_of_isTopologicallyNilpotent [R1Space S] :
    HasProd (1 - f a * f q ^ ·) ((f a; f q)_∞) :=
  (hasProd_map_qPochhammerInf_of_isTopologicallyNilpotent'
    f hf ha hq).multipliable.hasProd_of_le le_atTop

theorem hasProd_map_qPochhammerInf_conditional_of_isTopologicallyNilpotent :
    HasProd (1 - f a * f q ^ ·) ((f a; f q)_∞) (.conditional ℕ) :=
  (hasProd_map_qPochhammerInf_conditional_of_isTopologicallyNilpotent'
    f hf ha hq).multipliable.hasProd

theorem tendsto_map_qPochhammer_qPochhammerInf_of_isTopologicallyNilpotent' :
    Tendsto ((f a; f q)_·) atTop (𝓝 (f (a; q)_∞)) :=
  (hasProd_map_qPochhammerInf_conditional_of_isTopologicallyNilpotent'
    f hf ha hq).tendsto_prod_range

theorem tendsto_map_qPochhammer_qPochhammerInf_of_isTopologicallyNilpotent :
    Tendsto ((f a; f q)_·) atTop (𝓝 (f a; f q)_∞) :=
  (hasProd_map_qPochhammerInf_conditional_of_isTopologicallyNilpotent
    f hf ha hq).tendsto_prod_range

end nilpotent_map
