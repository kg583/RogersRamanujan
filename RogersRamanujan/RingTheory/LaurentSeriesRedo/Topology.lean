module

public import RogersRamanujan.RingTheory.LaurentSeriesRedo.Basic
public import RogersRamanujan.RingTheory.PowerSeries.DiscreteTopology
import RogersRamanujan.Tactic.OfClass

/-! # Laurent series, take two: topology
-/

@[expose] public section

open Filter Topology
open PowerSeries DiscreteTopology LaurentSeries₁

namespace LaurentSeries₁

theorem hasBasis_nhds_zero {R : Type*} [Ring R] :
    HasBasis (𝓝 (0 : LaurentSeries₁ R)) (fun _ ↦ True) (orderSubgroup R ·) :=
  MvLaurentSeries.hasBasis_nhds_zero

theorem hasBasis_nhds_zero_nat {R : Type*} [Ring R] :
    HasBasis (𝓝 (0 : LaurentSeries₁ R)) (fun _ : ℕ ↦ True) (orderSubgroup R ·) :=
  MvLaurentSeries.hasBasis_nhds_zero_nat

@[simp] theorem isOpen_orderSubgroup {R : Type*} [Ring R] (n : ℤ) :
    IsOpen (ofClass% orderSubgroup R n) := MvLaurentSeries.isOpen_orderSubgroup

@[fun_prop] theorem coe_continuous {R : Type*} [Ring R] :
    Continuous (ofPowerSeries R) := by
  refine continuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero, hasBasis_nhds.tendsto_iff hasBasis_nhds_zero_nat]
  refine fun n _ ↦ ⟨n, trivial, ?_⟩
  simp [truncPoly_eq_iff', mem_orderSubgroup, coeff_coe_eq_ite]
  grind

@[fun_prop] theorem isInducing_coe {R : Type*} [Ring R] :
    IsInducing (ofPowerSeries R) := by
  rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero,
    hasBasis_nhds.ext (hasBasis_nhds_zero_nat.comap (ofPowerSeries R))]
  · simp_rw [true_implies, true_and, truncPoly_eq_iff, map_zero]
    exact fun n ↦ ⟨n, fun x hx i hi ↦ by simpa using mem_orderSubgroup.mp hx i (by simpa)⟩
  · simp_rw [true_implies, true_and, truncPoly_eq_iff, map_zero]
    refine fun n ↦ ⟨n, fun x hx ↦ mem_orderSubgroup.mpr fun i hi ↦ ?_⟩
    grind [coeff_coe_eq_ite]

theorem isOpenMap_coe {R : Type*} [Ring R] :
    IsOpenMap (ofPowerSeries R) := isInducing_coe.isOpenMap <| by simp

end LaurentSeries₁
