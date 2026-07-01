module

public import RogersRamanujan.Algebra.Group.Units.Basic
import Mathlib.Algebra.Group.Commute.Units

/-! # Commuting elements and units
-/

@[expose] public section

section monoid
variable {α : Type*} [Monoid α]

theorem bInv_pow (x : α) (n : ℕ) : bInv (x ^ n) = bInv x ^ n := by
  by_cases hx : IsUnit x
  · simp [hx, hx.pow, IsUnit.unit_pow, IsUnit.bInv_eq_inv_unit]
  obtain _ | n := n
  · simp
  have key := (isUnit_pow_succ_iff (n := n)).not.mpr hx
  rw [bInv_eq_one_of_not_isUnit hx, bInv_eq_one_of_not_isUnit key, one_pow]

end monoid
