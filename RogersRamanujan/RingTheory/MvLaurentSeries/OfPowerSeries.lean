module

public import RogersRamanujan.Data.Finsupp.NatInt
public import RogersRamanujan.Order.Preorder.Finsupp
public import RogersRamanujan.RingTheory.MvLaurentSeries.Basic
import Mathlib.Data.Finsupp.Interval
import Mathlib.Data.Int.Interval
public import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Topology.MetricSpace.Bounded

/-! # Coercion from MvPowerSeries to MvLaurentSeries

-/

@[expose] public section

open Finsupp

namespace MvLaurentSeries
variable {σ : Type*} {R : Type*} [Finite σ]

section zero
variable [Zero R]

/-- The coercion from multivariate power series to multivariate Laurent series. -/
noncomputable def ofPowerSeries (f : MvPowerSeries σ R) : MvLaurentSeries σ R where
  coeff n := if 0 ≤ SumOrder.of.symm n then f (SumOrder.of.symm n |>.intNat _) else 0
  isPWO_support' := by
    rw [SumOrder.isPWO_iff]
    refine ⟨0, fun n hn ↦ ?_, fun n ↦ ?_⟩
    · simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hn
      exact Finset.sum_nonneg fun i _ ↦ hn.1 i
    · classical
      have := Fintype.ofFinite σ
      refine .subset (Set.finite_Icc 0 (equivFunOnFinite.symm n : σ →₀ ℤ) |>.image SumOrder.of)
        fun i hi ↦ Equiv.image_eq_preimage_symm _ _ ▸ ?_
      simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp,
        Set.mem_setOf_eq] at hi
      simpa [hi.1.1, Finsupp.le_def, ← hi.2, ← SumOrder.degree_symm_of, degree_eq_sum] using
        fun j ↦ Finset.single_le_sum (fun _ _ ↦ hi.1.1 _) (by simp)

theorem coeff_ofPowerSeries (f : MvPowerSeries σ R) (n : σ →₀ ℤ) :
    (ofPowerSeries f).coeff (.of n) = if 0 ≤ n then f (n.intNat _) else 0 := rfl

theorem coeff_ofPowerSeries_natInt (f : MvPowerSeries σ R) (n : σ →₀ ℕ) :
    (ofPowerSeries f).coeff (.of <| n.natInt _) = f n :=
  .trans (if_pos fun i ↦ by simp) <| congr_arg _ <| Finsupp.ext fun i ↦ by simp

theorem ofPowerSeries_injective : Function.Injective (ofPowerSeries (σ := σ) (R := R)) :=
  fun f g hfg ↦ funext fun n ↦ by
    rw [← coeff_ofPowerSeries_natInt f, ← coeff_ofPowerSeries_natInt g, hfg]

@[simp] theorem ofPowerSeries_zero : ofPowerSeries (σ := σ) (R := R) 0 = 0 := by
  ext n
  cases n with | ih n =>
  simp only [coeff_ofPowerSeries, coeff_zero, ite_eq_right_iff]
  exact fun _ ↦ rfl

end zero

section add_comm_monoid
variable [AddCommMonoid R]

theorem ofPowerSeries_add (f g : MvPowerSeries σ R) :
    ofPowerSeries (f + g) = ofPowerSeries f + ofPowerSeries g := by
  ext n
  cases n with | ih n =>
  simp [coeff_ofPowerSeries, ite_add_ite]
  rfl

end add_comm_monoid

section semiring
variable [Semiring R]

theorem ofPowerSeries_one : ofPowerSeries (1 : MvPowerSeries σ R) = 1 := by
  classical
  ext n
  cases n with | ih n =>
  simp_rw [coeff_ofPowerSeries, ← MvPowerSeries.coeff_apply, MvPowerSeries.coeff_one, coeff_one]
  by_cases h0n : 0 ≤ n
  · lift n to σ →₀ ℕ using h0n
    simp
  · simp [h0n]
    grind

theorem ofPowerSeries_mul (f g : MvPowerSeries σ R) :
    ofPowerSeries (f * g) = ofPowerSeries f * ofPowerSeries g := by
  classical
  ext n
  cases n with | ih n =>
  simp_rw [coeff_ofPowerSeries, ← MvPowerSeries.coeff_apply, MvPowerSeries.coeff_mul,
    MvLaurentSeries.coeff_mul]
  split_ifs with hn
  · lift n to σ →₀ ℕ using hn
    conv_lhs => enter [2]; simp +singlePass only [← intNat_natInt]
    refine .trans (Finset.sum_image (f := fun p : (σ →₀ ℤ) × (σ →₀ ℤ) ↦
      f.coeff (p.1.intNat _) * g.coeff (p.2.intNat _))
      ((Prod.map_injective.mpr ⟨natInt_injective,  natInt_injective⟩).injOn)).symm ?_
    rw [← Finset.sum_map_equiv (.prodCongr SumOrder.of.toEquiv SumOrder.of.toEquiv)]
    refine (Finset.sum_subset ?_ ?_).symm.trans (Finset.sum_congr rfl fun i hi ↦ ?_)
    · intro i hi
      obtain ⟨i, j⟩ := i
      cases i with | ih i =>
      cases j with | ih j =>
      simp only [AddEquiv.toEquiv_eq_coe, intNat_natInt, Finset.mem_map_equiv, Equiv.prodCongr_symm,
        Equiv.prodCongr_apply, AddEquiv.coe_toEquiv_symm, Prod.map_apply, AddEquiv.symm_apply_apply,
        Finset.mem_image, Finset.mem_antidiagonal, Prod.exists, Prod.mk.injEq]
      refine ⟨i.intNat _, j.intNat _, ?_⟩
      simp_all [coeff_ofPowerSeries, ← MvPowerSeries.coeff_apply, ← map_add, ← intNat_add]
    · simp +contextual [eq_comm (b := n), eq_comm (a := natInt _ _), SumOrder.of.surjective.forall,
        coeff_ofPowerSeries_natInt, ← MvPowerSeries.coeff_apply, ← or_iff_not_imp_left, or_imp]
    · obtain ⟨i, j⟩ := i
      cases i with | ih i =>
      cases j with | ih j =>
      simp_all [coeff_ofPowerSeries, ← MvPowerSeries.coeff_apply]
  · refine .symm <| Finset.sum_eq_zero fun i hi ↦ ?_
    obtain ⟨i, j⟩ := i
    cases i with | ih i =>
    cases j with | ih j =>
    simp_all [coeff_ofPowerSeries, ← MvPowerSeries.coeff_apply, ← map_add, eq_comm (b := n),
      add_nonneg]

variable (σ R) in
/-- The canonical ring homomorphism from power series to Laurent series. -/
noncomputable def ofPowerSeriesRingHom : MvPowerSeries σ R →+* MvLaurentSeries σ R where
  toFun := ofPowerSeries
  map_zero' := ofPowerSeries_zero
  map_add' := ofPowerSeries_add
  map_one' := ofPowerSeries_one
  map_mul' := ofPowerSeries_mul

noncomputable instance : Coe (MvPowerSeries σ R) (MvLaurentSeries σ R) := ⟨ofPowerSeriesRingHom σ R⟩

section Meta

open Lean PrettyPrinter Delaborator SubExpr

-- the usual attribute `[coe]` makes extra arguments appear
/-- Custom delaborator for `ofPowerSeriesRingHom` to display as `↑`. -/
@[app_delab DFunLike.coe]
meta def ofPowerSeriesRingHomDelab : Delab := whenPPOption getPPCoercions do
  let (_, #[_, _, _, _, f, _]) := (← getExpr).getAppFnArgs | failure
  let (``ofPowerSeriesRingHom, #[_, _, _, _]) := f.getAppFnArgs | failure
  let xD ← withNaryArg 5 delab
  `(↑$xD)

end Meta

@[simp] theorem coeff_coe_of (f : MvPowerSeries σ R) (n : σ →₀ ℤ) :
    coeff f (.of n) = if 0 ≤ n then f.coeff (n.intNat _) else 0 := rfl

theorem coeff_coe_natInt (f : MvPowerSeries σ R) (n : σ →₀ ℕ) :
    coeff f (.of <| n.natInt _) = f n :=
  coeff_ofPowerSeries_natInt f n

@[simp] theorem coe_injective : Function.Injective (ofPowerSeriesRingHom σ R) :=
  ofPowerSeries_injective

@[simp] theorem ofPowerSeries_eq_coe_ofPowerSeriesRingHom :
    ofPowerSeries = ofPowerSeriesRingHom σ R := rfl

@[simp] theorem coe_X
    {σ : Type*} {R : Type*} [Finite σ] [Semiring R] (i : σ) :
    ofPowerSeriesRingHom σ R (.X i (R := R)) = .xPow i 1 := by
  ext x
  obtain ⟨x, rfl⟩ := SumOrder.of.surjective x
  classical
  simp only [coeff_coe_of, MvPowerSeries.coeff_X, ← ite_and, coeff_xPow,
    EmbeddingLike.apply_eq_iff_eq]
  exact ite_cond_congr <| propext
    ⟨fun h ↦ by rw [← natInt_intNat _ h.1, h.2]; simp, by rintro rfl; simp⟩

theorem coe_X_pow
    {σ : Type*} {R : Type*} [Finite σ] [Semiring R] (i : σ) (n : ℕ) :
    (ofPowerSeriesRingHom σ R (.X i (R := R) ^ n)) = .xPow i n := by
  rw [map_pow, coe_X, xPow_natCast]

end semiring

end MvLaurentSeries
