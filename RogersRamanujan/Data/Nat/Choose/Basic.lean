module

public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs

/-! # Binomial coefficients on `ℕ`
-/

@[expose] public section

open Filter

namespace Nat

theorem choose_succ_two {n : ℕ} : (n + 1).choose 2 = n.choose 2 + n := by
  simp [choose_succ_succ]; omega

theorem choose_succ_two' {n : ℕ} : (n + 1).choose 2 = n * (n + 1) / 2 := by
  simp [Nat.choose_two_right, Nat.mul_comm]

theorem choose_add_two (a b : ℕ) : (a + b).choose 2 = a.choose 2 + b.choose 2 + a * b := by
  simp [add_choose_eq, Finset.antidiagonal]
  grind

theorem choose_le_choose_right {n r₁ r₂ : ℕ} (h1 : r₁ ≤ r₂) (h2 : r₂ ≤ n / 2) :
    n.choose r₁ ≤ n.choose r₂ := by
  obtain ⟨r₂, rfl⟩ := Nat.exists_eq_add_of_le h1; clear h1
  induction r₂ with
  | zero => simp
  | succ r₂ ih =>
    rw [show r₁ + (r₂ + 1) = r₁ + r₂ + 1 by omega, succ_le_iff] at h2
    rw [show r₁ + (r₂ + 1) = r₁ + r₂ + 1 by omega]
    grw [ih h2.le, choose_le_succ_of_lt_half_left h2]

/-- A loose lower bound of `n.choose r` -/
theorem le_choose_of {n r i : ℕ} (hr : r ≠ 0) (hi : i + 2 * r + 1 ≤ n) : i ≤ n.choose r := by
  grw [← hi, ← choose_le_choose_right (r₁ := 1) (by grind) (by grind), choose_one_right]
  grind

theorem tendsto_choose_atTop_atTop {r : ℕ} (hr : r ≠ 0) :
    Tendsto (fun n : ℕ ↦ n.choose r) atTop atTop := by
  rw [tendsto_atTop_atTop]
  exact fun n ↦ ⟨n + 2 * r + 1, fun i hi ↦ le_choose_of hr hi⟩

theorem two_mul_choose_two_right (k : ℕ) : 2 * k.choose 2 = k * (k - 1) := by
  rw [choose_two_right, Nat.mul_div_cancel' k.two_dvd_mul_sub_one]

theorem two_mul_cast_choose_two_right (n : ℕ) :
    2 * (n.choose 2 : ℤ) = n * (n - 1) := by
  obtain _ | n := n
  · rfl
  rw [← Nat.cast_two, ← Nat.cast_mul, two_mul_choose_two_right]
  simp

theorem two_mul_choose_two_add_self (k : ℕ) : 2 * k.choose 2 + k = k * k := by
  rw [two_mul_choose_two_right, ← mul_add_one]
  grind

theorem choose_succ_two_add_choose_self_two (n : ℕ) :
    (n + 1).choose 2 + n.choose 2 = n * n := by
  grind [two_mul_choose_two_add_self]

theorem choose_succ_two_add_choose_add_two (m n : ℕ) :
    (m + 1).choose 2 + (m + n).choose 2 = m * (m + n) + n.choose 2 := by
  rw [choose_add_two m n, mul_add, ← choose_succ_two_add_choose_self_two]
  grind

theorem choose_two_add_choose_succ_add_two (m n : ℕ) :
    m.choose 2 + (m + n + 1).choose 2 = m * (m + n) + (n + 1).choose 2 := by
  rw [choose_succ_two, choose_succ_two, choose_add_two, mul_add, ← two_mul_choose_two_add_self]
  ring_nf

theorem choose_two_add_choose_succ_two_of_le {n r : ℕ} (hr : r ≤ n) :
    r.choose 2 + (n + 1).choose 2 = r * n + (n - r + 1).choose 2 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hr
  rw [add_comm n r, choose_two_add_choose_succ_add_two, Nat.add_sub_cancel_left]

theorem choose_succ_two_add_choose_two_of_ge {n r : ℕ} (hr : r ≤ n) :
    (n + 1).choose 2 + r.choose 2 = n * r + (n - r + 1).choose 2 := by
  rw [add_comm, choose_two_add_choose_succ_two_of_le hr, mul_comm]

theorem choose_succ_two_add_choose_two_of_le {n r : ℕ} (hr : r ≤ n) :
    (r + 1).choose 2 + n.choose 2 = r * n + (n - r).choose 2 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hr
  rw [add_comm n r, choose_succ_two_add_choose_add_two, Nat.add_sub_cancel_left]

theorem choose_two_add_choose_succ_two_of_ge {n r : ℕ} (hr : r ≤ n) :
    n.choose 2 + (r + 1).choose 2 = n * r + (n - r).choose 2 := by
  rw [add_comm, choose_succ_two_add_choose_two_of_le hr, mul_comm]

end Nat
