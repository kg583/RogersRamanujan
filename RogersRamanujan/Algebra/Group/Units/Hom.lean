module

public import RogersRamanujan.Algebra.Group.Units.Basic
public import Mathlib.Algebra.Group.Units.Hom

/-! # Group homomorphisms and units
-/

@[expose] public section

theorem IsUnit.map_bInv {M N : Type*} [Monoid M] [Monoid N] {x : M} (hx : IsUnit x)
    {F : Type*} [FunLike F M N] [MonoidHomClass F M N] (f : F) :
    f (bInv x) = bInv (f x) :=
  (hx.map f).eq_bInv_of_mul_eq_one (by simp [← map_mul, hx])

/-- Special case for `IsLocalHom` -/
theorem map_bInv' {M N : Type*} [Monoid M] [Monoid N]
    {F : Type*} [FunLike F M N] [MonoidHomClass F M N] (f : F) [IsLocalHom f] (x : M) :
    f (bInv x) = bInv (f x) := by
  by_cases hx : IsUnit x
  · exact hx.map_bInv f
  · simp [bInv_eq_one_of_not_isUnit, hx]
