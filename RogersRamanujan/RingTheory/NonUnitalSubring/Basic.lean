module

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.RingTheory.NonUnitalSubring.Defs
import Mathlib.Tactic.Ring.RingNF

/-! # Non-unital subrings of a commutative ring

Membership lemmas for a non-unital subring `M` of a commutative ring `R`, expressed via the
`NonUnitalSubringClass` so that they apply to bundled `NonUnitalSubring`s as well as to
`OpenSubrng`s.

A non-unital subring is closed under multiplication, so these lemmas need no `M * M ≤ M`
hypothesis: that is exactly what the `NonUnitalSubring` packaging provides.
-/

@[expose] public section

namespace NonUnitalSubring

section CommRing
variable {R S : Type*} [CommRing R] [SetLike S R] [NonUnitalSubringClass S R] {M : S}

open Finset

theorem mul_mem_of_sub_one_mem {a b : R} (ha : a - 1 ∈ M) (hb : b ∈ M) : a * b ∈ M := by
  rw [show a * b = (a - 1) * b + b by ring]
  exact add_mem (mul_mem ha hb) hb

theorem prod_sub_one_mem {ι : Type*} {f : ι → R} {s : Finset ι}
    (hsf : ∀ i ∈ s, f i - 1 ∈ M) : (∏ i ∈ s, f i) - 1 ∈ M := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have key (a b : R) : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by ring
    rw [prod_insert hi, key]
    exact add_mem (add_mem (mul_mem (by grind) (ih <| by grind)) (by grind)) (ih <| by grind)

theorem mul_mem_of_mem_of_sub_one_mem {a b : R} (ha : a ∈ M) (hb : b - 1 ∈ M) : a * b ∈ M := by
  rw [mul_comm]
  exact mul_mem_of_sub_one_mem hb ha

theorem one_sub_mul_mem {a b : R} (ha : 1 - a ∈ M) (hb : 1 - b ∈ M) : 1 - a * b ∈ M := by
  convert sub_mem (add_mem ha hb) (mul_mem ha hb) using 1
  ring

theorem pow_succ_mem {x : R} (hx : x ∈ M) (n : ℕ) : x ^ (n + 1) ∈ M := by
  induction n with
  | zero => simpa
  | succ n ih => simpa [pow_succ] using mul_mem ih hx

theorem pow_mem {x : R} (hx : x ∈ M) {n : ℕ} (hn : n ≠ 0) : x ^ n ∈ M := by
  obtain _ | n := n
  · simp at hn
  exact pow_succ_mem hx n

theorem prod_one_add_sub_one_mem {ι : Type*} {a : ι → R} {s : Finset ι}
    (ha : ∀ i ∈ s, a i ∈ M) : (∏ i ∈ s, (1 + a i)) - 1 ∈ M :=
  prod_sub_one_mem fun i hi => by simpa using ha i hi

end CommRing

end NonUnitalSubring
