module

public import RogersRamanujan.Algebra.Group.Units.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-! # Big operators over a `Finset` (basic)
-/

@[expose] public section

open Finset

theorem bInv_prod
    {M ι : Type*} [CommMonoid M] {s : Finset ι} {f : ι → M} (hf : ∀ i ∈ s, IsUnit (f i)) :
    bInv (∏ i ∈ s, f i) = ∏ i ∈ s, bInv (f i) := bInv_eq_of_mul_eq_one <| by
  simp_rw +contextual [← prod_mul_distrib, (hf _ _).mul_bInv_cancel, prod_const_one]
