module

public import RogersRamanujan.RingTheory.MvLaurentSeries.OfPowerSeries
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Topology.MetricSpace.Bounded

/-! # Laurent series, take two: basic theory
-/

@[expose] public section

/-- `LaurentSeries` but better -/
abbrev LaurentSeries₁ (R : Type*) [Zero R] := MvLaurentSeries Unit R

namespace LaurentSeries₁
variable {R : Type*}

/-- The `n`-th coefficient of a Laurent series. -/
noncomputable def coeff [Semiring R] (n : ℤ) : LaurentSeries₁ R →ₗ[R] R :=
  MvLaurentSeries.coeffLinearMap R (.of (.single () n))

@[ext] theorem ext [Semiring R] {f g : LaurentSeries₁ R} (h : ∀ n, f.coeff n = g.coeff n) :
    f = g :=
  MvLaurentSeries.ext <| by
    simpa [SumOrder.of.surjective.forall, (Finsupp.uniqueEquiv ()).symm.surjective.forall]

/-- `X ^ n` where `n` can be negative. -/
noncomputable def xPow [Zero R] [One R] (n : ℤ) : LaurentSeries₁ R := MvLaurentSeries.xPow () n

theorem xPow_add [Semiring R] (m n : ℤ) : xPow (R := R) (m + n) = xPow m * xPow n :=
  MvLaurentSeries.xPow_add () m n

@[simp] theorem xPow_zero [Zero R] [One R] : xPow (R := R) 0 = 1 := MvLaurentSeries.xPow_zero ()

theorem xPow_pow [Semiring R] (m : ℤ) (n : ℕ) : xPow (R := R) m ^ n = xPow (m * n) :=
  MvLaurentSeries.xPow_pow () m n

theorem coeff_xPow [Semiring R] (m n : ℤ) : (xPow (R := R) m).coeff n = if n = m then 1 else 0 := by
  convert MvLaurentSeries.coeff_xPow (R := R) () m (.of (.single () n))
  all_goals first | rfl | simp

@[simp] theorem coeff_xPow_same (n : ℤ) [Semiring R] : (xPow (R := R) n).coeff n = 1 := by
  simp [coeff_xPow]

@[simp] theorem coeff_xPow_of_ne [Semiring R] {m n : ℤ} (h : n ≠ m) :
    (xPow (R := R) m).coeff n = 0 := by simp [coeff_xPow, h]

variable (R) in
/-- The canonical ring homomorphism from power series to Laurent series. -/
noncomputable def ofPowerSeries [Semiring R] : PowerSeries R →+* LaurentSeries₁ R :=
  MvLaurentSeries.ofPowerSeriesRingHom Unit R

noncomputable instance [Semiring R] : Coe (PowerSeries R) (LaurentSeries₁ R) := ⟨ofPowerSeries R⟩

section Meta

open Lean PrettyPrinter Delaborator SubExpr

-- the usual attribute `[coe]` makes extra arguments appear
/-- Custom delaborator for `ofPowerSeries` to display as `↑`. -/
@[app_delab DFunLike.coe]
meta def ofPowerSeriesDelab : Delab := whenPPOption getPPCoercions do
  let (_, #[_, _, _, _, f, _]) := (← getExpr).getAppFnArgs | failure
  let (``ofPowerSeries, #[_, _]) := f.getAppFnArgs | failure
  let xD ← withNaryArg 5 delab
  `(↑$xD)

end Meta

@[simp] theorem coeff_coe {R : Type*} [Semiring R] (f : PowerSeries R) (n : ℕ) :
    (f : LaurentSeries₁ R).coeff n = f.coeff n := by
  simp [ofPowerSeries, coeff, PowerSeries.coeff]

@[simp] theorem coeff_coe_eq_zero {R : Type*} [Semiring R] (f : PowerSeries R) {n : ℤ}
    (hn : n < 0) : (f : LaurentSeries₁ R).coeff n = 0 := by
  simp [ofPowerSeries, coeff, hn]

theorem coeff_coe_eq_ite {R : Type*} [Semiring R] (f : PowerSeries R) {n : ℤ} :
    (f : LaurentSeries₁ R).coeff n = if 0 ≤ n then f.coeff n.toNat else 0 := by
  simp [ofPowerSeries, coeff, PowerSeries.coeff]

@[simp] theorem coe_X {R : Type*} [Semiring R] :
    (PowerSeries.X (R := R) : LaurentSeries₁ R) = xPow 1 := by
  simp [ofPowerSeries, PowerSeries.X, xPow]

@[simp] theorem coe_injective [Semiring R] : Function.Injective (ofPowerSeries R) :=
  MvLaurentSeries.coe_injective

@[simp] theorem coe_inj [Semiring R] {f g : PowerSeries R} :
    ofPowerSeries R f = ofPowerSeries R g ↔ f = g := coe_injective.eq_iff

/-- The subgroup of Laurent series of order at least `n`. -/
def orderSubgroup (R : Type*) [AddGroup R] (n : ℤ) : AddSubgroup (LaurentSeries₁ R) :=
  MvLaurentSeries.orderSubgroup Unit R n

theorem mem_orderSubgroup [Ring R] {f : LaurentSeries₁ R} {n : ℤ} :
    f ∈ orderSubgroup R n ↔ ∀ m < n, f.coeff m = 0 := by
  simp [orderSubgroup, MvLaurentSeries.mem_orderSubgroup,
    SumOrder.of.surjective.forall, (Finsupp.uniqueEquiv ()).symm.surjective.forall,
    MvLaurentSeries.mem_support_iff, coeff]
  grind

@[simp] theorem range_coe {R : Type*} [Ring R] :
    Set.range (ofPowerSeries R) = orderSubgroup R 0 := by
  ext f
  simp only [Set.mem_range, SetLike.mem_coe, mem_orderSubgroup]
  exact ⟨by grind [coeff_coe_eq_ite], fun hf ↦ ⟨.mk (f.coeff ·), ext <| by
    simp [coeff_coe_eq_ite]; grind⟩⟩

end LaurentSeries₁
