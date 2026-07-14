module

public import RogersRamanujan.Algebra.Group.Units.Basic
import RogersRamanujan.Algebra.Group.Units.Hom
import RogersRamanujan.Combinatorics.Enumerative.Pentagonal
public import RogersRamanujan.NumberTheory.QTheory.Defs
import RogersRamanujan.NumberTheory.QTheory.JacobiTripleProduct.Basic
import RogersRamanujan.NumberTheory.QTheory.StrongNonarchimedean
public import RogersRamanujan.RingTheory.PowerSeries.DiscreteTopology
import RogersRamanujan.RingTheory.PowerSeries.Evaluation
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
public import Mathlib.Combinatorics.Enumerative.Pentagonal
import Mathlib.RingTheory.MvPowerSeries.LinearTopology

/-! # Pentagonal number theorem

In this file we prove the well-celebrated pentagonal number theorem:
`(q; q)_∞ = ∑ k : ℤ, (-1)^k q^(k(3k-1)/2)`. This is `tsum_qPochhammerInf_self`.

We also prove the generating function for the partition function:
`∑' n, p(n) q^n = 1/(q; q)_∞`. This is `Nat.Partition.tsum_card`.

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

namespace Nat.Partition

open PowerSeries PowerSeries.WithPiTopology Finset

private theorem mul_qPochhammerInf_self_powerSeries_eq_one :
    (PowerSeries.mk fun n ↦ (Fintype.card (Partition n) : ℤ)) * (X; X)_∞ = 1 := by
  have hprod := hasProd_powerSeriesMk_card_restricted ℤ (fun _ : ℕ ↦ True)
  have hcard : (fun n ↦ (#(restricted n (fun _ : ℕ ↦ True)) : ℤ)) =
      fun n ↦ (Fintype.card (Partition n) : ℤ) := by
    funext n
    simp [restricted]
  simp only [if_true, hcard] at hprod
  rw [← hprod.tprod_eq, qPochhammerInf_eq_tprod]
  · simp_rw [show ∀ i : ℕ, (X : ℤ⟦X⟧) * X ^ i = X ^ (i + 1) from fun i ↦ by ring]
    rw [← hprod.multipliable.tprod_mul (multipliable_one_sub_X_pow ℤ)]
    convert tprod_one with i
    simp_rw [pow_mul]
    exact tsum_pow_mul_one_sub_of_constantCoeff_eq_zero (by simp)
  · simp

theorem hasSum_card_powerSeries :
    HasSum (fun n : ℕ ↦ (Fintype.card (Partition n) : ℤ) • X ^ n) (bInv (X; X)_∞ : ℤ⟦X⟧) := by
  have hgen : (PowerSeries.mk fun n ↦ (Fintype.card (Partition n) : ℤ)) = bInv (X; X)_∞ :=
    eq_bInv_of_mul_eq_one mul_qPochhammerInf_self_powerSeries_eq_one
  rw [← hgen]
  simpa [monomial_eq_C_mul_X_pow, smul_eq_C_mul] using
    hasSum_of_monomials_self (PowerSeries.mk fun n ↦ (Fintype.card (Partition n) : ℤ))

theorem hasSum_card {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
    [NonarchimedeanRing R] [CompleteSpace R] [T2Space R]
    {q : R} (hq : IsTopologicallyNilpotent q := by simp) :
    HasSum (fun n : ℕ ↦ (Fintype.card (Partition n) : ℤ) • q ^ n) (bInv (q; q)_∞) := by
  convert hasSum_card_powerSeries.map (intEval q) (by fun_prop) using 1 <;>
  simp [funext_iff, hq,
    IsUnit.map_bInv (.of_mul_eq_one_right _ mul_qPochhammerInf_self_powerSeries_eq_one) (intEval q),
    map_qPochhammerInf_of_isTopologicallyNilpotent (intEval q) (by fun_prop)]

/-- **Generating function for the partition function**: `∑' n, p(n) q^n = 1/(q; q)_∞`,
where `p(n) = Fintype.card (Nat.Partition n)` is the number of partitions of `n`.

For the version with `HasSum`, see `hasSum_card`. -/
theorem tsum_card {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
    [NonarchimedeanRing R] [CompleteSpace R] [T2Space R]
    {q : R} (hq : IsTopologicallyNilpotent q := by simp) :
    ∑' n : ℕ, (Fintype.card (Partition n) : ℤ) • q ^ n = bInv (q; q)_∞ :=
  (hasSum_card hq).tsum_eq

end Nat.Partition
