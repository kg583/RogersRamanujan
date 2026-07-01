module

import RogersRamanujan.Data.Nat.Choose.Basic
public import Mathlib.Combinatorics.Enumerative.Pentagonal
public import Mathlib.Data.Nat.Choose.Basic

/-! # Pentagonal numbers and binomial coefficients

Expressing the (generalised) pentagonal numbers `pentagonal n` and `pentagonal (-n)` in terms of
the binomial coefficient `n.choose 2`.
-/

@[expose] public section

@[simp] theorem three_mul_choose_two_add_self_eq_pentagonal (n : ℕ) :
    3 * n.choose 2 + n = pentagonal n := by
  refine Nat.cast_injective (R := ℤ) <| mul_left_cancel₀ (by grind : (2 : ℤ) ≠ 0) ?_
  rw [two_mul_natCast_pentagonal]
  simp [mul_add, mul_left_comm (2 : ℤ), Nat.two_mul_cast_choose_two_right]
  grind

@[simp] theorem three_mul_choose_two_add_two_mul_self_eq_pentagonal_neg (n : ℕ) :
    3 * n.choose 2 + 2 * n = pentagonal (-n) := by
  refine Nat.cast_injective (R := ℤ) <| mul_left_cancel₀ (by grind : (2 : ℤ) ≠ 0) ?_
  rw [two_mul_natCast_pentagonal]
  simp [mul_add, mul_left_comm (2 : ℤ), Nat.two_mul_cast_choose_two_right]
  grind
