module

import RogersRamanujan.Algebra.Group.Commute.Units
import RogersRamanujan.NumberTheory.QTheory.BinomialTheorem
public import RogersRamanujan.NumberTheory.QTheory.Defs
import RogersRamanujan.NumberTheory.QTheory.StrongNonarchimedean
import RogersRamanujan.NumberTheory.QTheory.Topology
import RogersRamanujan.RingTheory.Binomial
import RogersRamanujan.Topology.Algebra.InfiniteSum.Nonarchimedean
import RogersRamanujan.Topology.Algebra.Nonarchimedean.Bounded
public import RogersRamanujan.Topology.Algebra.Nonarchimedean.Strong
import RogersRamanujan.Topology.Algebra.TopologicallyNilpotent
import RogersRamanujan.Topology.Instances.Int
public import Mathlib.RingTheory.Binomial
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-! # Nilpotent unit lemmas for the Jacobi triple product
-/

@[expose] public section

open Ring Finset Filter Topology NonarchimedeanAddGroup
open scoped QTheoryUnsafe

/-- The map `(m, ℓ) ↦ (-(k + ℓ), ℓ)` used in the proof of Jacobi Triple Product. -/
def jtpReindex : ℤ × ℕ ≃ ℤ × ℕ where
  toFun p := (-(p.1 + p.2), p.2)
  invFun p := (-(p.1 + p.2), p.2)
  left_inv p := by simp
  right_inv p := by simp

section topologicalSpace
variable {R : Type*} [CommRing R] [TopologicalSpace R] [StrongNonarchimedeanRing R] {a q : Rˣ}

theorem tendsto_zpow_mul_zpow_choose_two (a : Rˣ) {q : Rˣ}
    (hq : IsTopologicallyNilpotent (q : R)) :
    Tendsto (fun m : ℤ ↦ (↑(a ^ m) * ↑(q ^ choose m 2) : R)) cofinite (𝓝 0) := by
  simp_rw [Int.tendsto_cofinite_iff]
  simpa [choose_natCast, choose_neg_two, choose_succ_two, zpow_add, ← mul_assoc] using
    ⟨tendsto_pow_mul_pow_choose_two hq, by simpa using (tendsto_pow_mul_pow_choose_two hq).mul hq⟩

theorem jtp_tendsto_zero₁
    (hq : IsTopologicallyNilpotent (q : R)) (ha : IsTopologicallyNilpotent (a : R)) :
    Tendsto (fun p : ℤ × ℕ ↦ (↑(a ^ p.1) * ↑(q ^ (choose p.1 2)) * a ^ p.2 : R))
      cofinite (𝓝 0) := by
  rw [IsTopologicallyNilpotent, ← Nat.cofinite_eq_atTop] at ha
  convert tendsto_mul_cofinite_nhds_zero (tendsto_zpow_mul_zpow_choose_two a hq) ha

theorem jtp_tendsto_zero₂
    (hq : IsTopologicallyNilpotent (q : R)) (ha : IsTopologicallyNilpotent (a : R)) :
    Tendsto (fun p : ℤ × ℕ ↦ (↑(a⁻¹ ^ p.1) * ↑(q ^ choose (p.1 + p.2 + 1) 2) : R))
      cofinite (𝓝 0) := by
  convert (jtp_tendsto_zero₁ hq ha).comp jtpReindex.injective.tendsto_cofinite with p
  simp [jtpReindex, ← choose_neg_two, mul_right_comm, zpow_add, ← mul_pow]

end topologicalSpace

section uniformSpace
variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
  [StrongNonarchimedeanRing R] [T2Space R] {a q : Rˣ}

theorem jacobi_triple_product_units_of_isTopologicallyNilpotent
    (hq : IsTopologicallyNilpotent (q : R) := by simp)
    (ha : IsTopologicallyNilpotent (a : R) := by simp) :
    ((q : R))_∞ * ((-(a⁻¹ * q) : R))_∞ * ((-a : R))_∞ =
    ∑' n : ℤ, (↑(a ^ n) * ↑(q ^ choose n 2) : R) :=
  have h₁ : (fun p : ℤ × ℕ ↦ bInv ((q : R))_p.2 * (-1) ^ p.2).BoundedRange :=
    ((tendsto_bInv_qPochhammer_bInv_qPochhammerInf hq).boundedRange.mul .neg_one_pow).comp
  ((isUnit_qPochhammerInf ha.neg hq).eq_mul_bInv_iff_mul_eq _ _).mp <| calc
  ((q : R))_∞ * ((-(a⁻¹ * q) : R))_∞
    = ((q : R))_∞ * ∑' k, qPochhammerInfInner (a⁻¹ * q : R) q k := by
      rw [qPochhammerInf_neg_eq_tsum hq]
  _ = ∑' k, ((q : R))_∞ * qPochhammerInfInner (a⁻¹ * q : R) q k := by
    refine .symm <| Summable.tsum_mul_left _ <| summable_of_tendsto_atTop_zero ?_
    convert (tendsto_bInv_qPochhammer_bInv_qPochhammerInf hq).mul
      (tendsto_pow_mul_pow_choose_two (a := (↑a⁻¹ * ↑q : R)) hq)
    all_goals first | rfl | simp
  _ = ∑' k, (a⁻¹ * q) ^ k * q ^ k.choose 2 * ((q ^ (k + 1) : R))_∞ := by
    congr! 2 with n
    rw [qPochhammerInfInner, pow_succ', qPochhammerInf_shift_eq_bInv_qPochhammer_mul hq
      (isUnit_qPochhammerInf hq hq)]
    ac_rfl
  _ = ∑' k : ℤ, ↑((a⁻¹ * q) ^ k) * ↑(q ^ choose k 2) * ((↑(q ^ (k + 1)) : R))_∞ := by
    rw [← (Nat.cast_injective (R := ℤ)).tsum_eq]
    · simp [choose_natCast, pow_succ, zpow_add]
    · rintro (i | i) hi
      · simp
      · simp [Int.negSucc_eq, ← Units.bInv_coe, bInv_pow, qPochhammerInf_bInv_pow_eq_zero] at hi
  _ = ∑' k : ℤ, ∑' ℓ, bInv ((q : R))_ℓ * (-1) ^ ℓ * (↑(a⁻¹ ^ k) *
        ↑(q ^ (choose k 2 + k + (k + 1) * ℓ + ℓ.choose 2))) := by
    simp_rw [qPochhammerInf_eq_tsum hq, ← (summable_qPochhammerInfInner _ hq).tsum_mul_left,
      qPochhammerInfInner, mul_zpow, zpow_add, zpow_mul, zpow_add, zpow_natCast,
      neg_pow (Units.val _), Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mul]
    congr! 4; ring
  _ = ∑' k : ℤ, ∑' ℓ, bInv ((q : R))_ℓ * (-1) ^ ℓ * (↑(a⁻¹ ^ k) * ↑(q ^ choose (k + ℓ + 1) 2)) := by
    congr! 7 with k l
    simp_rw [choose_succ_two, add_choose_eq' k l]
    simp [antidiagonal, choose_natCast, add_one_mul]
    ac_rfl
  _ = ∑' p : ℤ × ℕ, bInv ((q : R))_p.2 * (-1) ^ p.2 *
        (↑(a⁻¹ ^ p.1) * ↑(q ^ choose (p.1 + p.2 + 1) 2)) := by
    refine .symm <| Summable.tsum_prod <| summable_of_tendsto_cofinite_zero ?_
    exact h₁.mul_tendsto_zero (jtp_tendsto_zero₂ hq ha)
  _ = ∑' p : ℤ × ℕ, bInv ((q : R))_p.2 * (-1) ^ p.2 *
        (↑(a ^ p.1) * ↑(q ^ choose p.1 2) * a ^ p.2) := by
    rw [← jtpReindex.tsum_eq]
    simp [jtpReindex, zpow_add, ← choose_neg_two]
    ac_rfl
  _ = ∑' m : ℤ, ∑' ℓ, ↑(a ^ m) * ↑(q ^ choose m 2) * (bInv ((q : R))_ℓ * (-a) ^ ℓ) := by
    rw [Summable.tsum_prod (NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero <|
        h₁.mul_tendsto_zero (jtp_tendsto_zero₁ hq ha))]
    simp [neg_pow (a : R)]
    ac_rfl
  _ = (∑' n : ℤ, (↑(a ^ n) * ↑(q ^ choose n 2))) * bInv ((-a : R))_∞ := by
    rw [← Summable.tsum_mul_right]
    · congr! 2
      rw [bInv_qPochhammerInf_eq_tsum ha.neg hq, ← Summable.tsum_mul_left]
      refine summable_of_tendsto_atTop_zero ?_
      convert (tendsto_bInv_qPochhammer_bInv_qPochhammerInf hq).mul ha.neg
      simp
    · exact summable_of_tendsto_cofinite_zero <| tendsto_zpow_mul_zpow_choose_two a hq

end uniformSpace
