module

import RogersRamanujan.Algebra.Ring.Basic
import RogersRamanujan.Data.Nat.Choose.Basic
import RogersRamanujan.NumberTheory.QTheory.Basic
public import RogersRamanujan.NumberTheory.QTheory.Defs
import RogersRamanujan.NumberTheory.QTheory.JacobiTripleProduct.Basic
import RogersRamanujan.NumberTheory.QTheory.StrongNonarchimedean
public import RogersRamanujan.RingTheory.PowerSeries.DiscreteTopology
import RogersRamanujan.RingTheory.PowerSeries.Evaluation
import RogersRamanujan.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.MvPowerSeries.LinearTopology

/-! # Jacobi's identity

In this file we prove Jacobi's identity involving triangular numbers:
`(q; q)_∞^3 = ∑ k : ℤ, (-1)^k (2k+1) q^(k(k+1)/2)`.
This is `tsum_qPochhammerInf_self_pow_three`.

-/

@[expose] public section

open QTheory PowerSeries DiscreteTopology Topology

open LaurentPolynomial hiding C

theorem balanced_jacobi_triple_product_hasSum_laurentPolynomial (R : Type*) [CommRing R] :
    HasSum (fun n : ℕ ↦ (-1) ^ n * C (T (-n)) * X ^ (n + 1).choose 2 * qInt (C (T 1)) (2 * n + 1))
      ((C (T 1) * X; X)_∞ * (C (T (-1)) * X; X)_∞ * (X; X)_∞ : R[T;T⁻¹]⟦X⟧) := by
  -- `1 - T` is regular
  have h₁ := (Polynomial.monic_X_sub_C (1 : R)).isRegular.neg
  replace h₁ := (IsLocalization.toLocalizationMap (.powers Polynomial.X) R[T;T⁻¹]).map_isRegular h₁
  refine .of_C_mul_of_regular h₁ ?_
  -- Group JTP for `(T, T⁻¹ X, X)`
  have h₂ : (C (T 1) * (C (T (-1)) * X) : R[T;T⁻¹]⟦X⟧) = X := by
    simp [← mul_assoc, ← map_mul, -T_mul, ← T_add]
  replace h₂ := jacobi_triple_product_hasSum' (by simp) h₂
  replace h₂ := h₂.finsetSum_of_finite_fiber'
    (g := fun i ↦ if 1 ≤ i then (i - 1).natAbs else i.natAbs)
    (fun n ↦ .cons (-n) {((n + 1 : ℕ) : ℤ)} (by grind)) (by grind)
  -- Then compare both sides
  convert h₂ using 1
  · rfl
  · funext n
    suffices ((1 - C (T 1)) * qInt (C (T 1)) (2 * n + 1) *
          (-1) ^ n * C (T (-n)) * X ^ (n + 1).choose 2 : R[T;T⁻¹]⟦X⟧) =
        (-1) ^ n * C (T (-n)) * X ^ (n.choose 2 + n) +
          (-1) ^ (n + 1) * C (T (n + 1)) * X ^ (n + 1).choose 2 by
      simp [-Finset.cons_eq_insert, -Nat.cast_add, -Int.natCast_add, ← neg_mul, mul_pow,
        neg_pow (C _), ← map_pow, T_pow]
      grind
    rw [one_sub_mul_qInt, ← map_pow, T_pow, ← Nat.choose_succ_two,
      show (n + 1 : ℤ) = -n + (2 * n + 1) by grind, T_add, map_mul]
    grind
  · have hq : IsTopologicallyNilpotent (X : R[T;T⁻¹]⟦X⟧) := by simp
    simp [qPochhammerInf_eq_one_sub_mul_qPochhammerInf (a := C (T 1)) (hq := hq)]
    ring

theorem hasSum_qPochhammerInf_self_pow_three_powerSeries (R : Type*) [CommRing R] :
    HasSum (fun n : ℕ ↦ ((-1) ^ n * C (2 * n + 1 : R) * X ^ (n + 1).choose 2 : R⟦X⟧))
      ((X; X)_∞ ^ 3 : R⟦X⟧) := by
  convert (balanced_jacobi_triple_product_hasSum_laurentPolynomial R).map
    (map (eval₂ (.id R) 1)) (by fun_prop)
  · simp [map_ofNat]
    grind
  · simp [continuous_map, pow_three']

theorem hasSum_qPochhammerInf_self_pow_three {R : Type*} [CommRing R] [UniformSpace R]
    [IsUniformAddGroup R] [NonarchimedeanRing R] [CompleteSpace R] [T2Space R]
    {q : R} (hq : IsTopologicallyNilpotent q := by simp) :
    HasSum (fun n : ℕ ↦ (-1) ^ n * (2 * n + 1) * q ^ (n + 1).choose 2) ((q; q)_∞ ^ 3) := by
  convert (hasSum_qPochhammerInf_self_pow_three_powerSeries _).map (intEval q) (by fun_prop) using 1
  all_goals simp [funext_iff, hq, map_ofNat]

/-- **Jacobi's identity**: `(q; q)_∞^3 = ∑ k : ℕ, (-1)^k (2k+1) q^(k(k+1)/2)`.

For the version with `HasSum`, see `hasSum_qPochhammerInf_self_pow_three`. -/
theorem tsum_qPochhammerInf_self_pow_three {R : Type*} [CommRing R] [UniformSpace R]
    [IsUniformAddGroup R] [NonarchimedeanRing R] [CompleteSpace R] [T2Space R]
    {q : R} (hq : IsTopologicallyNilpotent q := by simp) :
    ∑' k : ℕ, (-1) ^ k * (2 * k + 1) * q ^ (k + 1).choose 2 = (q; q)_∞ ^ 3 :=
  (hasSum_qPochhammerInf_self_pow_three hq).tsum_eq

alias jacobi_identity := tsum_qPochhammerInf_self_pow_three
