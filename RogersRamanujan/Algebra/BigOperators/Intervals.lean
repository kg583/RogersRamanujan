module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Abel

/-! # Big operators over intervals
-/

@[expose] public section

open Finset

namespace Finset

theorem sum_Ico_id_mul_two (m n : ℕ) :
    (∑ i ∈ Ico m n, i) * 2 = (n - m) * (m + n - 1) := by
  nth_rw 1 [sum_Ico_eq_sum_range, mul_two, ← sum_range_reflect, ← sum_add_distrib,
    sum_const_nat (m := m + n - 1) (by grind), card_range]

theorem sum_Ico_id (m n : ℕ) :
    ∑ i ∈ Ico m n, i = (n - m) * (m + n - 1) / 2 := by
  rw [← sum_Ico_id_mul_two, Nat.mul_div_cancel _ (by grind)]

theorem sum_range_natSub (n : ℕ) :
    ∑ i ∈ range n, (n - i) = n * (n + 1) / 2 := by
  rw [range_eq_Ico, sum_Ico_reflect (f := fun i ↦ i) _ (by simp),
    Nat.add_sub_cancel_left, Nat.sub_zero, sum_Ico_id]
  grind

end Finset

/-- Fold a sum from `0` to `2 * n - 1` in half. -/
theorem sum_range_two_mul_eq_fold
    {α : Type*} [AddCommMonoid α] (f : ℕ → α) (n : ℕ) :
    ∑ i ∈ range (2 * n), f i = ∑ i ∈ range n, (f (n - 1 - i) + f (n + i)) := by
  rw [two_mul, sum_range_add, ← sum_range_reflect, sum_add_distrib]

/-- Fold a sum from `0` to `2 * n` in half. -/
theorem sum_range_two_mul_add_one_eq_fold
    {α : Type*} [AddCommMonoid α] (f : ℕ → α) (n : ℕ) :
    ∑ i ∈ range (2 * n + 1), f i = f n + ∑ i ∈ Icc 1 n, (f (n - i) + f (n + i)) := by
  conv_lhs => rw [show 2 * n + 1 = n + 1 + n by grind, sum_range_add, sum_range_succ]
  conv_rhs => rw [sum_add_distrib, ← Ico_add_one_right_eq_Icc, sum_Ico_reflect _ _ (by grind),
    sum_Ico_eq_sum_range _ 1]
  simp; abel_nf

/-- Fold a sum from `0` to `2 * n + 1` in half. -/
theorem sum_range_two_mul_add_two_eq_fold
    {α : Type*} [AddCommMonoid α] (f : ℕ → α) (n : ℕ) :
    ∑ i ∈ range (2 * n + 2), f i = ∑ i ∈ range (n + 1), (f (n - i) + f (n + 1 + i)) := by
  rw [← mul_add_one, sum_range_two_mul_eq_fold, Nat.add_sub_cancel]

/-- Reindex a triangular double sum: swap the summation order and shift the inner variable.
Transforms `∑_{j≤N} ∑_{r≤j} f(r, j)` into `∑_{r≤N} ∑_{k≤N-r} f(r, r+k)`. -/
theorem sum_triangle_reindex {M : Type*} [AddCommMonoid M] (N : ℕ) (f : ℕ → ℕ → M) :
    ∑ j ∈ range (N + 1), ∑ r ∈ range (j + 1), f r j =
      ∑ r ∈ range (N + 1), ∑ k ∈ range (N - r + 1), f r (r + k) := by
  rw [sum_comm' (t' := range (N + 1)) (s' := fun r ↦ Ico r (N + 1))
    (fun j r ↦ by simp [mem_range, mem_Ico]; omega)]
  refine sum_congr rfl ?_
  intro r hr
  have hrN : r ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hr)
  simp_rw [sum_Ico_eq_sum_range, show N + 1 - r = N - r + 1 by omega]
