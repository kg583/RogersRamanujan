module

import RogersRamanujan.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Trunc

/-! # Generalizing power series lemmas to semirings

E.g. in https://github.com/leanprover-community/mathlib4/pull/23188 the coercion `R[X] → R⟦X⟧` was
generalized to `Semiring`, but some lemmas still require `CommSemiring`.

-/

@[expose] public section

open Nat hiding pow_succ pow_zero
open Finset Finset.Nat
open Polynomial

namespace PowerSeries

/-! # From Mathlib.RingTheory.PowerSeries.Trunc -/

section Trunc
/-
Lemmas in this section involve the coercion `R[X] → R⟦X⟧`, so they may only be stated in the case
`R` is commutative. This is because the coercion is an `R`-algebra map.
-/

variable {R : Type*} [Semiring R]

theorem trunc_trunc_of_le' {n m} (f : R⟦X⟧) (hnm : n ≤ m := by rfl) :
    trunc n (trunc m f) = trunc n f := by
  ext d
  rw [coeff_trunc, coeff_trunc, coeff_coe]
  split_ifs with h
  · rw [coeff_trunc, if_pos <| lt_of_lt_of_le h hnm]
  · rfl

@[simp] theorem trunc_trunc' {n} (f : R⟦X⟧) : trunc n ↑(trunc n f) = trunc n f :=
  trunc_trunc_of_le' f

@[simp] theorem trunc_trunc_mul' {n} (f g : R⟦X⟧) :
    trunc n ((trunc n f) * g : R⟦X⟧) = trunc n (f * g) := by
  ext m
  rw [coeff_trunc, coeff_trunc]
  split_ifs with h
  · rw [coeff_mul, coeff_mul, sum_congr rfl]
    intro _ hab
    have ha := lt_of_le_of_lt (antidiagonal.fst_le hab) h
    rw [coeff_coe, coeff_trunc, if_pos ha]
  · rfl

@[simp] theorem trunc_mul_trunc' {n} (f g : R⟦X⟧) :
    trunc n (f * (trunc n g) : R⟦X⟧) = trunc n (f * g) := by
  ext m
  rw [coeff_trunc, coeff_trunc]
  split_ifs with h
  · rw [coeff_mul, coeff_mul, sum_congr rfl]
    intro _ hab
    have ha := lt_of_le_of_lt (antidiagonal.snd_le hab) h
    rw [coeff_coe, coeff_trunc, if_pos ha]
  · rfl

theorem trunc_trunc_mul_trunc' {n} (f g : R⟦X⟧) :
    trunc n (trunc n f * trunc n g : R⟦X⟧) = trunc n (f * g) := by
  rw [trunc_trunc_mul', trunc_mul_trunc']

@[simp] theorem trunc_trunc_pow' (f : R⟦X⟧) (n a : ℕ) :
    trunc n ((trunc n f : R⟦X⟧) ^ a) = trunc n (f ^ a) := by
  induction a with
  | zero =>
    rw [pow_zero, pow_zero]
  | succ a ih =>
    rw [_root_.pow_succ', _root_.pow_succ', trunc_trunc_mul',
      ← trunc_trunc_mul_trunc', ih, trunc_trunc_mul_trunc']

theorem trunc_coe_eq_self' {n} {f : R[X]} (hn : natDegree f < n) : trunc n (f : R⟦X⟧) = f := by
  rw [← Polynomial.coe_inj]
  ext m
  rw [coeff_coe, coeff_trunc]
  split
  case isTrue h => rfl
  case isFalse h =>
    rw [not_lt] at h
    rw [coeff_coe]; symm
    exact coeff_eq_zero_of_natDegree_lt <| lt_of_lt_of_le hn h

/-- The function `coeff n : R⟦X⟧ → R` is continuous. I.e. `coeff n f` depends only on a sufficiently
long truncation of the power series `f`. -/
theorem coeff_coe_trunc_of_lt' {n m} {f : R⟦X⟧} (h : n < m) :
    coeff n (trunc m f) = coeff n f := by
  rwa [coeff_coe, coeff_trunc, if_pos]

/-- The `n`-th coefficient of `f*g` may be calculated
from the truncations of `f` and `g`. -/
theorem coeff_mul_eq_coeff_trunc_mul_trunc₂' {n a b} (f g : R⟦X⟧) (ha : n < a) (hb : n < b) :
    coeff n (f * g) = coeff n ((trunc a f : R⟦X⟧) * (trunc b g : R⟦X⟧)) := by
  symm
  rw [← coeff_coe_trunc_of_lt' n.lt_succ_self, ← trunc_trunc_mul_trunc', trunc_trunc_of_le' f ha,
    trunc_trunc_of_le' g hb, trunc_trunc_mul_trunc', coeff_coe_trunc_of_lt' n.lt_succ_self]

theorem coeff_mul_eq_coeff_trunc_mul_trunc' {d n} (f g) (h : d < n) :
    coeff d (f * g) = coeff d ((trunc n f : R⟦X⟧) * (trunc n g : R⟦X⟧)) :=
  coeff_mul_eq_coeff_trunc_mul_trunc₂' f g h h

end Trunc

/-! # Custom lemmas -/

variable {R : Type*} [Semiring R]

theorem coe_trunc_eq_sum {n} (f : R⟦X⟧) :
    (f.trunc n : R⟦X⟧) = ∑ i ∈ range n, C (f.coeff i) * X ^ i := by
  simp [trunc_apply, Ico_zero_eq_range, coe_sum, monomial_eq_C_mul_X_pow]

end PowerSeries
