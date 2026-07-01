module

import RogersRamanujan.Algebra.Ring.NegOnePow
public import Mathlib.RingTheory.Binomial

/-! # Binomial rings
-/

@[expose] public section

open Ring Finset

theorem Ring.choose_neg_two
    {R : Type*} [NonAssocRing R] [Pow R ℕ] [BinomialRing R] [NatPowAssoc R] (r : R) :
    choose (-r) 2 = choose (r + 1) 2 := by
  simp [choose_neg, add_sub_assoc, ← one_add_one_eq_two]

theorem Ring.choose_succ_two
    {R : Type*} [NonAssocRing R] [Pow R ℕ] [BinomialRing R] [NatPowAssoc R] (r : R) :
    choose (r + 1) 2 = choose r 2 + r := by simp [choose_succ_succ, add_comm]

theorem Ring.add_choose_eq'
    {R : Type*} [CommRing R] [BinomialRing R] (r s : R) (k : ℕ) :
    choose (r + s) k = ∑ ij ∈ antidiagonal k, choose r ij.1 * choose s ij.2 :=
  add_choose_eq k <| .all r s
