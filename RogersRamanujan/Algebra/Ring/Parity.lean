module

public import Mathlib.Algebra.Ring.Parity

/-! # Parity in rings
-/

@[expose] public section

@[simp] lemma Even.mod_two {n : ℕ} (hn : Even n) : n % 2 = 0 :=
  Nat.even_iff.mp hn

@[simp] lemma Odd.mod_two {n : ℕ} (hn : Odd n) : n % 2 = 1 :=
  Nat.odd_iff.mp hn

theorem neg_one_pow_sub {M : Type*} [Monoid M] [HasDistribNeg M] {a b : ℕ} (h : b ≤ a) :
    (-1 : M) ^ (a - b) = (-1) ^ a * (-1) ^ b := by
  rw [← pow_add, show a + b = a - b + 2 * b by grind, pow_add]
  simp
