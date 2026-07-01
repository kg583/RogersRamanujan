module

import RogersRamanujan.Combinatorics.Enumerative.Pentagonal
public import RogersRamanujan.NumberTheory.QTheory.Defs
import RogersRamanujan.NumberTheory.QTheory.JacobiTripleProduct.Basic
import RogersRamanujan.NumberTheory.QTheory.StrongNonarchimedean
public import RogersRamanujan.RingTheory.PowerSeries.DiscreteTopology
import RogersRamanujan.RingTheory.PowerSeries.Evaluation
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Combinatorics.Enumerative.Pentagonal
import Mathlib.RingTheory.MvPowerSeries.LinearTopology

/-! # Pentagonal number theorem

In this file we prove the well-celebrated pentagonal number theorem:
`(q; q)_∞ = ∑ k : ℤ, (-1)^k q^(k(3k-1)/2)`. This is `tsum_qPochhammerInf_self`.

-/

@[expose] public section

open QTheory PowerSeries DiscreteTopology

theorem hasSum_qPochhammerInf_self_powerSeries :
    HasSum (fun k : ℤ ↦ (k.negOnePow • X ^ pentagonal k : ℤ⟦X⟧)) (X; X)_∞ := by
  convert jacobi_triple_product_hasSum' (by simp) (show (X * X ^ 2 : ℤ⟦X⟧) = X ^ 3 by ring) using 1
  · rfl
  · funext n
    rw [Units.smul_def]
    obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
    · simp [Int.coe_negOnePow_natCast, neg_pow X, mul_assoc, ← pow_mul, ← pow_add, add_comm n]
    · simp [Int.coe_negOnePow_natCast, neg_pow (X ^ 2), mul_assoc, ← pow_mul, ← pow_add,
        add_comm (2 * n)]
  · rw [qPochhammerInf_eq_prod_range (by grind : 3 ≠ 0) (by simp)]
    simp [Finset.prod_range_succ]
    ring_nf

theorem hasSum_qPochhammerInf_self {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
    [NonarchimedeanRing R] [CompleteSpace R] [T2Space R]
    {q : R} (hq : IsTopologicallyNilpotent q := by simp) :
    HasSum (fun k : ℤ ↦ (k.negOnePow • q ^ pentagonal k)) (q; q)_∞ := by
  convert hasSum_qPochhammerInf_self_powerSeries.map (intEval q) (by fun_prop) using 1 <;>
  simp [funext_iff, hq]

/-- **Pentagonal number theorem**: `(q; q)_∞ = ∑ k : ℤ, (-1)^k q^(k(3k-1)/2)`.

For the version with `HasSum`, see `hasSum_qPochhammerInf_self`. -/
theorem tsum_qPochhammerInf_self {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
    [NonarchimedeanRing R] [CompleteSpace R] [T2Space R]
    {q : R} (hq : IsTopologicallyNilpotent q := by simp) :
    ∑' k : ℤ, k.negOnePow • q ^ pentagonal k = (q; q)_∞ :=
  (hasSum_qPochhammerInf_self hq).tsum_eq

alias pentagonal_number_theorem := tsum_qPochhammerInf_self
