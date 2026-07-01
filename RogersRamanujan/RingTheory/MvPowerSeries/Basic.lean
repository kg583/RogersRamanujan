module

public import RogersRamanujan.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic

/-! # Multivariate power series (basic)
-/

@[expose] public section

namespace MvPowerSeries

theorem apply_eq_coeff {R σ : Type*} [Semiring R] (p : MvPowerSeries σ R) (v : σ →₀ ℕ) :
  p v = p.coeff v := rfl

theorem monomial_single_add {R σ : Type*} [Semiring R] (i : σ) (n : ℕ) (v : σ →₀ ℕ) (r : R) :
    monomial (.single i n + v) r = X i ^ n * monomial v r := by
  nth_rw 1 [← one_mul r, ← monomial_mul_monomial, X_pow_eq]

theorem monomial_add_single {R σ : Type*} [Semiring R] (v : σ →₀ ℕ) (i : σ) (n : ℕ) (r : R) :
    monomial (v + .single i n) r = monomial v r * X i ^ n := by
  nth_rw 1 [← mul_one r, ← monomial_mul_monomial, X_pow_eq]

theorem pow_X_eq_monomial {R σ : Type*} [CommSemiring R] (v : σ →₀ ℕ) :
    v.pow (X (R := R)) = monomial v 1 := by
  induction v using Finsupp.induction with
  | zero => simp
  | single_add i n v hiv hn ih =>
    rw [Finsupp.pow_add, Finsupp.pow_single, monomial_single_add, ih]

theorem monomial_eq_mul_pow_X {R σ : Type*} [CommSemiring R] (v : σ →₀ ℕ) (r : R) :
    monomial v r = C r * v.pow (X (R := R)) := by
  rw [pow_X_eq_monomial, ← smul_eq_C_mul, ← map_smul, smul_eq_mul, mul_one]

theorem coeff_pow_eq_zero_of_constantCoeff_eq_zero
    {R σ : Type*} [Semiring R] {f : MvPowerSeries σ R} (hf : f.constantCoeff = 0)
    {n : ℕ} {d : σ →₀ ℕ} (hd : d.degree < n) : (f ^ n).coeff d = 0 := by
  classical induction n generalizing d with
  | zero => simp at hd
  | succ n ih =>
    rw [pow_succ, coeff_mul]
    refine Finset.sum_eq_zero fun p hp ↦ ?_
    have key := congr($(Finset.mem_antidiagonal.mp hp).degree)
    rw [map_add] at key
    by_cases! h1 : p.1.degree < n
    · simp [ih h1]
    have h2 : p.2.degree = 0 := by grind
    rw [p.2.degree_eq_zero_iff.mp h2, coeff_zero_eq_constantCoeff, hf, mul_zero]

end MvPowerSeries
