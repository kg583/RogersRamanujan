module

import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Algebra.Group.Units.Defs

/-! # Both-sided inverse (`bInv`)

This file defines the both-sided inverse of an element of a monoid,
with junk value `1` when it does not exist.
-/

@[expose] public section

/-- The both-sided inverse of an element of a monoid, with junk value `1` when it does not exist. -/
noncomputable def bInv {α : Type*} [Monoid α] (x : α) : α :=
  open scoped Classical in if h : IsUnit x then ↑h.unit⁻¹ else 1

section monoid
variable {α : Type*} [Monoid α] {u x y z : α}

variable (α) in
@[simp]
theorem bInv_one : bInv (1 : α) = 1 := by simp [bInv]

theorem bInv_eq_one_of_not_isUnit (hx : ¬IsUnit x) : bInv x = 1 := dif_neg hx

namespace IsUnit

theorem bInv_eq_inv_unit (hx : IsUnit x) : bInv x = ↑hx.unit⁻¹ := dif_pos hx

-- temporary measure for API building
attribute [local simp] bInv_eq_inv_unit bInv_eq_one_of_not_isUnit

@[simp, grind →]
theorem bInv_mul_cancel (hx : IsUnit x) : bInv x * x = 1 := by simp [hx]

variable (y) in
@[simp]
theorem bInv_mul_cancel_assoc (hx : IsUnit x) : bInv x * (x * y) = y := by simp [← mul_assoc, hx]

@[simp, grind →]
theorem mul_bInv_cancel (hx : IsUnit x) : x * bInv x = 1 := by simp [hx]

variable (y) in
@[simp]
theorem mul_bInv_cancel_assoc (hx : IsUnit x) : x * (bInv x * y) = y := by simp [← mul_assoc, hx]

@[grind .]
theorem bInv_eq_of_mul_eq_one (hx : IsUnit x) (hxy : x * y = 1) : bInv x = y :=
  left_inv_eq_right_inv hx.bInv_mul_cancel hxy

variable (y) in
theorem bInv_eq_iff_mul_eq_one (hx : IsUnit x) : bInv x = y ↔ x * y = 1 := by grind

@[grind .]
theorem eq_bInv_of_mul_eq_one (hy : IsUnit y) (hxy : x * y = 1) : x = bInv y :=
  left_inv_eq_right_inv hxy hy.mul_bInv_cancel

variable (x) in
theorem eq_bInv_iff_mul_eq_one (hy : IsUnit y) : x = bInv y ↔ x * y = 1 := by grind

@[simp]
theorem bInv_mul_rev (hx : IsUnit x) (hy : IsUnit y) :
    bInv (x * y) = bInv y * bInv x := by simp [hx, hy, hx.mul hy, unit_mul]

variable (x) in
@[simp]
protected theorem bInv : IsUnit (bInv x) := by by_cases hx : IsUnit x <;> simp [hx]

@[simp]
theorem bInv_bInv (hx : IsUnit x) : bInv (bInv x) = x := by simp [hx]

theorem bInv_mul_eq_iff_eq_mul (hu : IsUnit u) (x y : α) : bInv u * x = y ↔ x = u * y := by
  simp [hu, Units.inv_mul_eq_iff_eq_mul]

theorem bInv_mul_eq_of_eq_mul (hu : IsUnit u) (h : x = u * y) : bInv u * x = y :=
  hu.bInv_mul_eq_iff_eq_mul x y |>.mpr h

theorem eq_bInv_mul_iff_mul_eq (hu : IsUnit u) (x y : α) : x = bInv u * y ↔ u * x = y := by
  simp [hu, Units.eq_inv_mul_iff_mul_eq]

theorem eq_bInv_mul_of_mul_eq (hu : IsUnit u) (h : u * x = y) : x = bInv u * y :=
  hu.eq_bInv_mul_iff_mul_eq x y |>.mpr h

theorem mul_bInv_eq_iff_eq_mul (hu : IsUnit u) (x y : α) : x * bInv u = y ↔ x = y * u := by
  simp [hu, Units.mul_inv_eq_iff_eq_mul]

theorem mul_bInv_eq_of_eq_mul (hu : IsUnit u) (h : x = y * u) : x * bInv u = y :=
  hu.mul_bInv_eq_iff_eq_mul x y |>.mpr h

theorem eq_mul_bInv_iff_mul_eq (hu : IsUnit u) (x y : α) : x = y * bInv u ↔ x * u = y := by
  simp [hu, Units.eq_mul_inv_iff_mul_eq]

theorem eq_mul_bInv_of_mul_eq (hu : IsUnit u) (h : x * u = y) : x = y * bInv u :=
  hu.eq_mul_bInv_iff_mul_eq x y |>.mpr h

end IsUnit

-- temporary measure for API building
attribute [local simp] IsUnit.bInv_eq_inv_unit bInv_eq_one_of_not_isUnit

variable (x)

@[simp] theorem commutes_bInv : Commute x (bInv x) := by
  by_cases hx : IsUnit x <;> simp [commute_iff_eq, hx]

@[simp] theorem commutes_bInv' : Commute (bInv x) x := (commutes_bInv x).symm

variable {x}

namespace IsUnit

theorem pow_mul_bInv_pow_same (n : ℕ) (hx : IsUnit x) :
    x ^ n * bInv x ^ n = 1 := by
  rw [← (commutes_bInv x).mul_pow, hx.mul_bInv_cancel, one_pow]

theorem bInv_pow_mul_pow_same (n : ℕ) (hx : IsUnit x) :
    bInv x ^ n * x ^ n = 1 := by
  rw [← (commutes_bInv x).symm.mul_pow, hx.bInv_mul_cancel, one_pow]

theorem pow_mul_bInv_pow_of_ge {m n : ℕ} (hx : IsUnit x) (hnm : n ≤ m) :
    x ^ m * bInv x ^ n = x ^ (m - n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hnm
  rw [pow_add, mul_assoc, hx.pow_mul_bInv_pow_same n]
  simp

theorem bInv_pow_mul_pow_of_ge {m n : ℕ} (hx : IsUnit x) (hnm : n ≤ m) :
    bInv x ^ m * x ^ n = bInv x ^ (m - n) := by
  simpa [hx] using pow_mul_bInv_pow_of_ge (.bInv x) hnm

theorem pow_mul_bInv_pow_of_le {m n : ℕ} (hx : IsUnit x) (hnm : m ≤ n) :
    x ^ m * bInv x ^ n = bInv x ^ (n - m) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [pow_add, ← mul_assoc, hx.pow_mul_bInv_pow_same m]
  simp

theorem bInv_pow_mul_pow_of_le {m n : ℕ} (hx : IsUnit x) (hnm : m ≤ n) :
    bInv x ^ m * x ^ n = x ^ (n - m) := by
  simpa [hx] using pow_mul_bInv_pow_of_le (.bInv x) hnm

end IsUnit

namespace Units

@[simp] theorem bInv_coe (x : αˣ) : bInv (x : α) = x⁻¹ := by simp

end Units

theorem isUnit_and_bInv_eq_of_mul_eq_one (hxy : x * y = 1) (hyx : y * x = 1) :
    IsUnit x ∧ bInv x = y :=
  have hx : IsUnit x := isUnit_iff_exists.mpr ⟨_, hxy, hyx⟩
  ⟨hx, hx.bInv_eq_of_mul_eq_one hxy⟩

end monoid

section comm_monoid
variable {α : Type*} [CommMonoid α] {x y : α}

theorem IsUnit.bInv_mul (hx : IsUnit x) (hy : IsUnit y) : bInv (x * y) = bInv x * bInv y := by
  rw [hx.bInv_mul_rev hy, mul_comm]

theorem bInv_eq_of_mul_eq_one (h : x * y = 1) : bInv x = y :=
  (IsUnit.of_mul_eq_one _ h).bInv_eq_of_mul_eq_one h

theorem eq_bInv_of_mul_eq_one (h : x * y = 1) : x = bInv y :=
  (IsUnit.of_mul_eq_one_right _ h).eq_bInv_of_mul_eq_one h

end comm_monoid
