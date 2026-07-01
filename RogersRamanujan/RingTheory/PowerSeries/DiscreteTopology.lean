module

import RogersRamanujan.Algebra.GroupWithZero.Basic
public import RogersRamanujan.Order.Filter.Unbounded.Basic
import RogersRamanujan.RingTheory.MvPowerSeries.PiTopology
import RogersRamanujan.RingTheory.PowerSeries.Semiring
public import RogersRamanujan.RingTheory.PowerSeries.TruncPoly
import RogersRamanujan.Tactic.OfClass
import RogersRamanujan.Topology.Instances.ENat
import Mathlib.Data.Finsupp.Encodable
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import Mathlib.Topology.Separation.GDelta

/-! API Support for algebraic manipulation of power series

The current API for `R⟦X⟧` assumes a topology on `R`, which might not be suitable for
algebraic manipulations.

Installing the discrete topology on `R` recovers every algebraic API, which we do
privately, and only expose the relevant API.

-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Filter Topology Finset

namespace PowerSeries.DiscreteTopology
variable {R : Type*}

/-- Uniform space structure on `R⟦X⟧` when `R` is equipped with the discrete topology. -/
scoped instance : UniformSpace R⟦X⟧ :=
  let : UniformSpace R := ⊥
  open WithPiTopology in inferInstance

/-- Complete space structure on `R⟦X⟧` when `R` is equipped with the discrete topology. -/
scoped instance : CompleteSpace R⟦X⟧ :=
  open WithPiTopology in inferInstance

scoped instance : TopologicalSpace.IsCompletelyMetrizableSpace R⟦X⟧ :=
  let : UniformSpace R := ⊥
  let := TopologicalSpace.IsCompletelyMetrizableSpace.discrete (X := R)
  open WithPiTopology in TopologicalSpace.IsCompletelyMetrizableSpace.pi_countable

scoped instance : TopologicalSpace.MetrizableSpace R⟦X⟧ :=
  TopologicalSpace.IsCompletelyMetrizableSpace.MetrizableSpace

/-- T0 space structure on `R⟦X⟧` when `R` is equipped with the discrete topology. -/
scoped instance : T0Space R⟦X⟧ :=
  open WithPiTopology in inferInstance

/-- T2 space structure on `R⟦X⟧` when `R` is equipped with the discrete topology. -/
scoped instance : T2Space R⟦X⟧ :=
  open WithPiTopology in inferInstance

/-- T3 space structure on `R⟦X⟧` when `R` is equipped with the discrete topology. -/
scoped instance : T3Space R⟦X⟧ :=
  open WithPiTopology in inferInstance

/-- T3 space structure on `R⟦X⟧` when `R` is equipped with the discrete topology. -/
scoped instance : T4Space R⟦X⟧ :=
  inferInstance

scoped instance : T5Space R⟦X⟧ :=
  inferInstance

scoped instance : T6Space R⟦X⟧ :=
  inferInstance

/-- Topological semiring structure on `R⟦X⟧` when `R` is equipped with the discrete topology. -/
scoped instance [Semiring R] : IsTopologicalSemiring R⟦X⟧ :=
  open WithPiTopology in inferInstance

/-- Topological ring structure on `R⟦X⟧` when `R` is equipped with the discrete topology. -/
scoped instance [Ring R] : IsTopologicalRing R⟦X⟧ :=
  open WithPiTopology in inferInstance

/-- Uniform add group structure on `R⟦X⟧` when `R` is equipped with the discrete topology. -/
scoped instance [Ring R] : IsUniformAddGroup R⟦X⟧ :=
  open WithPiTopology in inferInstance

theorem denseRange_toPowerSeries [CommSemiring R] :
    DenseRange (Polynomial.toPowerSeries (R := R)) :=
  let : UniformSpace R := ⊥
  WithPiTopology.denseRange_toPowerSeries R

variable [Semiring R]

theorem tendsto_iff_coeff_eventually_const
    {ι : Type*} (f : ι → R⟦X⟧) (u : Filter ι) (g : R⟦X⟧) :
    Tendsto f u (𝓝 g) ↔ ∀ d, ∀ᶠ i in u, (f i).coeff d = g.coeff d := by
  simp [WithPiTopology.tendsto_iff_coeff_tendsto]

@[simp] theorem isTopologicallyNilpotent_iff_isNilpotent_constantCoeff {f : R⟦X⟧} :
    IsTopologicallyNilpotent f ↔ IsNilpotent f.constantCoeff :=
  let : UniformSpace R := ⊥
  MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_iff_constantCoeff_isNilpotent' f

theorem isTopologicallyNilpotent_X_pow [Nontrivial R] (n : ℕ) :
    IsTopologicallyNilpotent (X (R := R) ^ n) ↔ n ≠ 0 := by
  simp [isTopologicallyNilpotent_iff_isNilpotent_constantCoeff, zero_pow_eq, apply_ite]

theorem isTopologicallyNilpotent_X :
    IsTopologicallyNilpotent (X (R := R)) := by
  simp [isTopologicallyNilpotent_iff_isNilpotent_constantCoeff]

-- KL: requires Ring!
-- theorem summable_iff_order_tendsto_top {α : Type*} {f : α → R⟦X⟧} :
--     Summable f ↔ Tendsto (fun a ↦ (f a).order) cofinite (𝓝 ⊤) := by

theorem summable_of_order_tendsto_nhds_top {α : Type*} {f : α → R⟦X⟧}
    (h : Tendsto (fun a ↦ (f a).order) cofinite (𝓝 ⊤)) : Summable f := by
  simp_rw [ENat.tendsto_nhds_top_iff_natCast_lt, eventually_cofinite] at h
  use .mk fun d ↦ (h d).toFinset.sum (f · |>.coeff d)
  rw [HasSum, tendsto_iff_coeff_eventually_const]
  intro d
  rw [SummationFilter.unconditional_filter, eventually_atTop]
  refine ⟨(h d).toFinset, fun s hs ↦ ?_⟩
  rw [coeff_mk, map_sum, sum_subset hs]
  simp +contextual [lt_order_iff]

theorem le_order_mul_pow (f : R⟦X⟧) (m : ℕ) {q : R⟦X⟧} (hq : q.constantCoeff = 0 := by simp) :
    (m : ℕ∞) ≤ (f * q ^ m).order := by
  rw [← one_le_order_iff_constCoeff_eq_zero] at hq
  grw [← order_mul_ge, ← le_order_pow, ← hq, nsmul_one, ← le_add_self]

theorem coeff_mul_pow_eq_zero {f : R⟦X⟧} {n : ℕ} {d : ℕ} (hd : d < n)
    {q : R⟦X⟧} (hq : q.constantCoeff = 0 := by simp) : (f * q ^ n).coeff d = 0 :=
  coeff_of_lt_order _ <| (Nat.cast_lt.mpr hd) |>.trans_le <| le_order_mul_pow _ _ hq

theorem summable_mul_pow_of_tendsto_atTop {α : Type*}
    {n : α → ℕ} (h : Tendsto (fun a ↦ n a) cofinite atTop) {f : α → R⟦X⟧}
    {q : R⟦X⟧} (hq : q.constantCoeff = 0 := by simp) :
    Summable fun a ↦ f a * q ^ n a := summable_of_order_tendsto_nhds_top <|
  tendsto_nhds_top_mono' (ENat.tendsto_nat_nhds_top.comp h) fun _ ↦ le_order_mul_pow _ _ hq

theorem _root_.Filter.Unbounded.summable_mul_pow {α : Type*} {n : α → ℕ}
    (h : Filter.Unbounded n)
    {f : α → R⟦X⟧} {q : R⟦X⟧} (hq : q.constantCoeff = 0 := by simp) :
    Summable fun a ↦ f a * q ^ n a := summable_mul_pow_of_tendsto_atTop (Unbounded.nat_def.mp h) hq

theorem _root_.Filter.Unbounded.coeff_tsum_eq_sum {α : Type*} {n : α → ℕ}
    (hn : Filter.Unbounded n)
    (f : α → R⟦X⟧) (d : ℕ) (S : Finset α) (hS : ∀ a ∉ S, d < n a)
    {q : R⟦X⟧} (hq : q.constantCoeff = 0 := by simp) :
    (∑' a, f a * q ^ n a).coeff d = ∑ a ∈ S, (f a * q ^ n a).coeff d := by
  let : UniformSpace R := ⊥
  rw [(hn.summable_mul_pow (f := f) hq).map_tsum _ (WithPiTopology.continuous_coeff _ d)]
  exact tsum_eq_sum fun a ha ↦ coeff_mul_pow_eq_zero (hS a ha) hq

theorem _root_.Filter.Unbounded.truncPoly_tsum_eq_sum {α : Type*} {n : α → ℕ}
    (hn : Filter.Unbounded n)
    (f : α → R⟦X⟧) (d : ℕ) (S : Finset α) (hS : ∀ a ∉ S, d ≤ n a)
    {q : R⟦X⟧} (hq : q.constantCoeff = 0 := by simp) :
    (∑' a, f a * q ^ n a).truncPoly _ d = ∑ a ∈ S, (f a * q ^ n a).truncPoly _ d := by
  rw [← map_sum, truncPoly_eq_iff]
  intro i hi
  rw [map_sum]
  exact hn.coeff_tsum_eq_sum _ _ _ (by grind) hq

theorem _root_.Filter.Unbounded.coeff_tsum_eq_finsum {α : Type*} {n : α → ℕ}
    (hn : Filter.Unbounded n)
    (f : α → R⟦X⟧) (d : ℕ) {q : R⟦X⟧} (hq : q.constantCoeff = 0 := by simp) :
    (∑' a, f a * q ^ n a).coeff d = ∑ᶠ a, (f a * q ^ n a).coeff d := by
  have hf := eventually_cofinite.mp <| tendsto_atTop.mp (Unbounded.nat_def.mp hn) (d + 1)
  rw [hn.coeff_tsum_eq_sum f d hf.toFinset (by simp_all) hq]
  exact .symm <| finsum_eq_sum_of_support_subset _ <| by
      simp_all [- Nat.not_lt, - not_lt, not_imp_not, coeff_mul_pow_eq_zero (hq := hq)]

theorem summable_mul_pow {f : ℕ → R⟦X⟧} {q : R⟦X⟧} (hq : q.constantCoeff = 0 := by simp) :
    Summable fun n ↦ f n * q ^ n := Unbounded.id.summable_mul_pow hq

theorem tsum_mul_pow_eq {f : ℕ → R⟦X⟧} (n : ℕ) {q : R⟦X⟧} (hq : q.constantCoeff = 0 := by simp) :
    ∑' i, f i * q ^ i = ∑ i ∈ range n, f i * q ^ i + (∑' i, f (i + n) * q ^ i) * q ^ n := by
  rw [← Summable.sum_add_tsum_nat_add' (k := n)]
  · simp_rw [pow_add, ← mul_assoc, (summable_mul_pow hq).tsum_mul_right]
  · simp_rw [pow_add, ← mul_assoc]
    exact (summable_mul_pow hq).mul_right _

theorem truncPoly_tsum_mul_pow {f : ℕ → R⟦X⟧} {q : R⟦X⟧} {n : ℕ}
    (hq : q.constantCoeff = 0 := by simp) :
    (∑' i, f i * q ^ i).truncPoly _ n =
      ∑ i ∈ range n, (f i).truncPoly _ n * q.truncPoly _ n ^ i := by
  rw [tsum_mul_pow_eq n hq, map_add, map_mul, map_sum, map_pow, truncPoly_pow_eq_zero hq le_rfl]
  simp

theorem coeff_tsum_mul_pow {f : ℕ → R⟦X⟧} {n m : ℕ} (hnm : n < m)
    {q : R⟦X⟧} (hq : q.constantCoeff = 0 := by simp) :
    (∑' i, f i * q ^ i).coeff n = ∑ i ∈ range m, (f i * q ^ i).coeff n := by
  rw [← coeff_truncPoly hnm, truncPoly_tsum_mul_pow hq, TruncPoly.coeff_sum]
  simp_rw [← map_pow, ← map_mul, coeff_truncPoly hnm]

theorem coeff_tsum_mul_pow_eq_succ {f : ℕ → R⟦X⟧} {n : ℕ} {q : R⟦X⟧}
    (hq : q.constantCoeff = 0 := by simp) :
    (∑' i, f i * q ^ i).coeff n = ∑ i ∈ range (n + 1), (f i * q ^ i).coeff n :=
  coeff_tsum_mul_pow n.lt_succ_self hq

theorem hasBasis_nhds {f : R⟦X⟧} :
    HasBasis (𝓝 f) (fun _ : ℕ ↦ True) fun n ↦ {g | g.truncPoly _ n = f.truncPoly _ n} := by
  let : UniformSpace R := ⊥
  rw [nhds_pi]
  simp_rw [nhds_discrete]
  refine (Filter.hasBasis_pi_pure _).to_hasBasis (fun s hs ↦ ?_) fun n _ ↦ ?_
  · obtain ⟨s, rfl⟩ := hs.exists_finset_coe
    refine ⟨s.sup (· ()) + 1, trivial, fun g hg d hd ↦ ?_⟩
    obtain ⟨d, rfl⟩ := (Finsupp.uniqueAddEquiv ()).symm.surjective d
    rw [Finsupp.uniqueAddEquiv_symm_apply] at hd ⊢
    change PowerSeries.coeff d g = f.coeff d
    have key : d < (s.sup fun x ↦ x ()) + 1 := Nat.lt_succ_iff.mpr <| by
      convert le_sup hd
      all_goals first | rfl | simp
    rw [← coeff_truncPoly key, hg, coeff_truncPoly key]
  · exact ⟨(range n).image (Finsupp.single ()), Finset.finite_toSet _, fun g hg ↦
      truncPoly_eq_iff.mpr fun i hi ↦ hg _ <| by simpa⟩

theorem hasBasis_nhds_zero :
    HasBasis (𝓝 (0 : R⟦X⟧)) (fun _ : ℕ ↦ True) fun n ↦ (Ideal.span {X ^ n} : Ideal R⟦X⟧) := by
  convert hasBasis_nhds (f := (0 : R⟦X⟧))
  simp [Set.ext_iff, Ideal.mem_span_singleton', truncPoly_eq_iff', ← X_pow_dvd_iff, dvd_def]
  simp [(commute_X_pow _ _).eq, eq_comm]

theorem span_X_pow_mem_nhds_zero (n : ℕ) :
    ((Ideal.span {X ^ n} : Ideal R⟦X⟧) : Set R⟦X⟧) ∈ 𝓝 (0 : R⟦X⟧) :=
  hasBasis_nhds_zero.mem_of_mem (i := n) trivial

instance (priority := high) (R : Type*) [Ring R] : NonarchimedeanRing R⟦X⟧ where
  is_nonarchimedean _ hU :=
    let ⟨n, _, hn⟩ := (hasBasis_nhds_zero (R := R)).mem_iff.mp hU
    ⟨⟨(Ideal.span {X ^ n} : Ideal R⟦X⟧).toAddSubgroup,
      AddSubgroup.isOpen_of_mem_nhds _ (span_X_pow_mem_nhds_zero n)⟩, hn⟩

theorem hasSum_C_coeff_mul_X_pow (c : R⟦X⟧) :
    HasSum (fun k => C (c.coeff k) * X ^ k) c :=
  let : UniformSpace R := ⊥
  (summable_mul_pow).hasSum_iff.mpr <| by simpa [monomial_eq_C_mul_X_pow] using (as_tsum c).symm

theorem hasSum_C_mul_X_pow (c : ℕ → R) :
    HasSum (fun k => C (c k) * X ^ k) (mk c) := by
  convert hasSum_C_coeff_mul_X_pow (mk c); simp

theorem coeff_tsum_C_mul_X_pow (c : ℕ → R) (n : ℕ) :
    coeff n (∑' k, C (c k) * X ^ k) = c n := by
  rw [(hasSum_C_mul_X_pow c).tsum_eq, coeff_mk]

theorem _root_.PowerSeries.hasSum_self (p : R⟦X⟧) :
    HasSum (fun n ↦ C (p.coeff n) * X ^ n) p :=
  let : UniformSpace R := ⊥
  p.hasSum_of_monomials_self.congr_fun <| by simp [monomial_eq_C_mul_X_pow]

theorem _root_.PowerSeries.as_tsum_discrete (p : R⟦X⟧) : p = ∑' n, C (p.coeff n) * X ^ n :=
  (hasSum_self p).tsum_eq.symm

@[elab_as_elim, induction_eliminator]
theorem _root_.PowerSeries.inductionOn_discrete {P : R⟦X⟧ → Prop} (p : R⟦X⟧)
    (monomial : ∀ r n, P (C r * X ^ n))
    (add : ∀ f g, P f → P g → P (f + g))
    (lim : ∀ (n : ℕ → R⟦X⟧) l, Tendsto n atTop (𝓝 l) → (∀ i, P (n i)) → P l) :
    P p := by
  rw [p.as_tsum_discrete]
  refine lim _ _ (summable_mul_pow (by simp)).tendsto_sum_tsum_nat fun n ↦ ?_
  induction n with
  | zero => simpa using monomial 0 0
  | succ n ih =>
    rw [sum_range_succ]
    grind

theorem ext_addHomClass
    {S : Type*} [AddCommMonoid S] [TopologicalSpace S] [T2Space S]
    {F : Type*} [FunLike F R⟦X⟧ S] [AddMonoidHomClass F R⟦X⟧ S]
    {f g : F} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ r n, f (C r * X ^ n) = g (C r * X ^ n)) : f = g :=
  DFunLike.ext _ _ fun p ↦ p.inductionOn_discrete (by grind) (by grind) fun n l ht ih ↦
    tendsto_nhds_unique ((hf.tendsto l).comp ht) <| by
      convert (hg.tendsto l).comp ht using 1; grind

theorem ext_ringHomClass
    {S : Type*} [Semiring S] [TopologicalSpace S] [T2Space S]
    {F : Type*} [FunLike F R⟦X⟧ S] [RingHomClass F R⟦X⟧ S]
    {f g : F} (hf : Continuous f) (hg : Continuous g)
    (hc : ∀ r, f (C r) = g (C r)) (hx : f X = g X) : f = g := by
  refine ext_addHomClass hf hg fun r n ↦ by simp_all

theorem ext_addMonoidHom
    {S : Type*} [AddCommMonoid S] [TopologicalSpace S] [T2Space S]
    {f g : R⟦X⟧ →+ S} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ n, f.comp (ofClass% monomial n) = g.comp (ofClass% monomial n)) : f = g :=
  ext_addHomClass hf hg fun r n ↦ by simpa [monomial_eq_C_mul_X_pow] using congr($(h n) r)

theorem ext_ringHom
    {S : Type*} [Semiring S] [TopologicalSpace S] [T2Space S]
    {f g : R⟦X⟧ →+* S} (hf : Continuous f) (hg : Continuous g)
    (hc : f.comp C = g.comp C) (hx : f X = g X) : f = g :=
  ext_ringHomClass hf hg (fun r ↦ congr($hc r)) hx

attribute [fun_prop] WithPiTopology.continuous_constantCoeff
attribute [fun_prop] WithPiTopology.continuous_coeff
attribute [fun_prop] WithPiTopology.continuous_C

theorem tendsto_trunc_atTop (f : R⟦X⟧) : Tendsto (fun d => ↑(f.trunc d)) atTop (𝓝 f) := by
  simp_rw [tendsto_iff_coeff_eventually_const, eventually_atTop]
  exact fun d ↦ ⟨d + 1, fun n hn ↦ coeff_coe_trunc_of_lt' (by grind)⟩

@[fun_prop] theorem continuous_map {S : Type*} [Semiring S] {f : R →+* S} : Continuous (map f) := by
  refine continuous_iff_continuousAt.mpr fun p ↦
    hasBasis_nhds.tendsto_iff hasBasis_nhds |>.mpr fun n h ↦ ⟨n, h, fun x hx ↦ ?_⟩
  simp [truncPoly_eq_iff] at hx ⊢
  grind

-- TODO: This could probably be generalized.
theorem _root_.HasSum.of_C_mul_of_regular
    {R : Type*} [CommRing R] {r : R} (hr : IsRegular r)
    {ι : Type*} {f : ι → R⟦X⟧} {L : R⟦X⟧} (hL : HasSum (C r * f ·) (C r * L)) :
    HasSum f L := by
  refine .of_tendsto_comp (g := (C r * ·)) (c := 𝓝 (C r * L)) ?_ ?_
  · simpa [HasSum, Function.comp_def, Finset.mul_sum] using hL
  · exact ((hasBasis_nhds.comap _).le_basis_iff hasBasis_nhds).mpr fun n hn ↦
      ⟨n, hn, fun x hx ↦ hr.isSMulRegular <| by simpa using hx⟩

end DiscreteTopology

end PowerSeries
