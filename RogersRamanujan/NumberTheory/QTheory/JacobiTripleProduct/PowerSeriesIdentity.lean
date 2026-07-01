module

import RogersRamanujan.Algebra.Group.Units.Hom
import RogersRamanujan.Data.Nat.Choose.Basic
import RogersRamanujan.NumberTheory.QTheory.Basic
public import RogersRamanujan.NumberTheory.QTheory.BinomialTheorem
import RogersRamanujan.NumberTheory.QTheory.JacobiTripleProduct.NilpotentUnit
import RogersRamanujan.NumberTheory.QTheory.Nonarchimedean
import RogersRamanujan.NumberTheory.QTheory.StrongNonarchimedean
import RogersRamanujan.RingTheory.LaurentSeriesRedo.Topology
public import RogersRamanujan.RingTheory.MvLaurentSeries.Basic
public import RogersRamanujan.RingTheory.PowerSeries.DiscreteTopology
import RogersRamanujan.Topology.Algebra.InfiniteSum.SummationFilter
import Mathlib.RingTheory.MvPowerSeries.LinearTopology
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-! # Power series identity from Jacobi Triple Product

We take a less general version of JTP from
`RogersRamanujan/NumberTheory/QTheory/JacobiTripleProduct/NilpotentUnit.lean` and derive a family of
power series identities from it.

We will then use these identities to prove a more general version of JTP in
`RogersRamanujan/NumberTheory/QTheory/JacobiTripleProduct/Basic.lean`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Filter Topology PowerSeries NonarchimedeanAddGroup
open MvLaurentSeries
open scoped QTheory DiscreteTopology

theorem qPochhammerInfInner_mul_qPochhammerInfInner
    {R : Type*} [CommRing R] (a : Rˣ) (q : R) (m n : ℕ) :
    qPochhammerInfInner (a⁻¹ * q) q m * qPochhammerInfInner ↑a q n =
    bInv (q; q)_m * bInv (q; q)_n * q ^ ((m + 1).choose 2 + n.choose 2) * ↑(a ^ (n - m : ℤ)) := by
  simp [qPochhammerInfInner, zpow_sub, mul_pow, Nat.choose_succ_two, pow_add]
  ring

theorem MvLaurentSeries.qPochhammerInfInner_mul_qPochhammerInfInner
    (R : Type*) [CommRing R] {σ : Type*} (i j : σ) (m n : ℕ) :
    qPochhammerInfInner (xPow (R := R) i (-1) * xPow j 1) (xPow j 1) m *
      qPochhammerInfInner (xPow i 1) (xPow j 1) n =
    bInv (xPow j 1; xPow j 1)_m * bInv (xPow j 1; xPow j 1)_n *
      xPow j ((m + 1).choose 2 + n.choose 2) * xPow i (n - m) := by
  simpa [xPowUnits_zpow, xPow_pow] using _root_.qPochhammerInfInner_mul_qPochhammerInfInner
    (xPowUnits (R := R) i 1) (xPow j 1) m n

local notation "a" => xPow 0 1
local notation "a[" R "]" => xPow (R := R) (0 : Fin 2) 1
local notation "q" => xPow 1 1
local notation "q[" R "]" => xPow (R := R) (1 : Fin 2) 1
local notation "t" => xPow () 1

theorem hasSum_bInv_qPochhammer_mul_bInv_qPochhammer_mul_pow (R : Type*) [CommRing R] (n : ℕ) :
    HasSum (fun k ↦ bInv (X (R := R); X)_k * bInv (X; X)_(k + n) * X ^ (k * (k + n)))
      (bInv (X; X)_∞) := by
  nontriviality R
  let aU : (MvLaurentSeries (Fin 2) R)ˣ := xPowUnits 0 1
  let qU : (MvLaurentSeries (Fin 2) R)ˣ := xPowUnits 1 1
  have ha : IsTopologicallyNilpotent a[R] := by simp
  have hq : IsTopologicallyNilpotent q[R] := by simp
  have ht : IsTopologicallyNilpotent (xPow (R := R) () 1) := by simp
  have h₁ := (hasSum_qPochhammerInf_neg (xPow 0 (-1) * q) hq).mul_of_nonarchimedean
    (hasSum_qPochhammerInf_neg a hq)
  have h₂ := (summable_of_tendsto_cofinite_zero <| tendsto_zpow_mul_zpow_choose_two
    aU («q» := qU) hq).hasSum.mul_left (bInv (q; q)_∞)
  rw [← jacobi_triple_product_units_of_isTopologicallyNilpotent («a» := aU) («q» := qU) hq ha] at h₂
  simp_rw [aU, qU, val_xPowUnits, val_inv_xPowUnits, mul_assoc, xPowUnits_zpow, one_mul,
    (isUnit_qPochhammerInf hq hq).bInv_mul_cancel_assoc, val_xPowUnits] at h₂
  generalize (-(xPow (R := R) (0 : Fin 2) (-1) * q); q)_∞ * (-a; q)_∞ = L at h₁ h₂
  let e : Unit ↪ Fin 2 := ⟨fun _ ↦ 1, by decide⟩
  have he : e () = 1 := rfl
  replace h₁ := h₁.map (comapVar R e (.of <| .single 0 n)) (by fun_prop)
  replace h₂ := h₂.map (comapVar R e (.of <| .single 0 n)) (by fun_prop)
  simp_rw [Function.comp_def, MvLaurentSeries.qPochhammerInfInner_mul_qPochhammerInfInner,
    ← he, ← mapVar_xPow, ← map_qPochhammer (mapVar R e),
    ← map_qPochhammerInf (mapVar R e) (by fun_prop) _ ht,
    ← (isUnit_qPochhammerInf ht ht).map_bInv, ← (isUnit_qPochhammer ht ht _).map_bInv,
    ← map_mul, ← mul_assoc, mul_right_comm _ (xPow 0 _) (mapVar R e _), ← map_mul,
    comapVar_mapVar_mul_xPow_eq_ite e 0 (by decide)] at h₁ h₂
  let f : ℕ → ℕ × ℕ := fun k ↦ (k, k + n)
  have hf : f.Injective := fun _ ↦ by grind
  have hrf : Set.range f = {p | (n : ℤ) = p.2 - p.1} := Set.ext fun i ↦
    ⟨fun h ↦ by grind, fun h ↦ ⟨i.1, by grind⟩⟩
  replace h₁ := (hf.hasSum_iff <| by grind).mpr h₁ |>.mul_right (xPow 0 (-n.choose 2))
  simp_rw [Function.comp_def, f, Nat.cast_add, add_sub_cancel_left, ite_true] at h₁
  replace h₂:= h₂.unique (hasSum_single (n : ℤ) (by grind))
  simp_rw [h₂, ite_true, ← Nat.cast_add, Nat.choose_succ_two_add_choose_add_two, Nat.cast_add,
    Ring.choose_natCast, mul_assoc, ← xPow_add, add_assoc, add_neg_cancel, add_zero, xPow_zero,
    mul_one] at h₁
  have hx : (X (R := R) : LaurentSeries₁ R) = t := by simp [LaurentSeries₁.xPow, xPow]
  have hxn : IsTopologicallyNilpotent (X (R := R)) := by simp
  simp_rw [xPow_natCast, ← hx, ← map_qPochhammer, ← (isUnit_qPochhammer hxn hxn _).map_bInv,
    ← map_qPochhammerInf (LaurentSeries₁.ofPowerSeries R) (by fun_prop) _ hxn,
    ← map_pow, ← map_mul, ← (isUnit_qPochhammerInf hxn hxn).map_bInv, ← mul_assoc] at h₁
  exact (LaurentSeries₁.isInducing_coe.hasSum_iff _ _).mp h₁

theorem tsum_bInv_qPochhammer_mul_bInv_qPochhammer_mul_pow (R : Type*) [CommRing R] (n : ℕ) :
    ∑' k, bInv (X (R := R); X)_k * bInv (X; X)_(k + n) * X ^ (k * (k + n)) =
    bInv (X; X)_∞ :=
  (hasSum_bInv_qPochhammer_mul_bInv_qPochhammer_mul_pow R n).tsum_eq
