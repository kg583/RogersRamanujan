module

import RogersRamanujan.Analysis.Normed.Ring.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Topology.Algebra.TopologicallyNilpotent

/-! # `p`-adic numbers
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace Padic
variable (p : ℕ) [Fact p.Prime]

/-- Computable instance. -/
instance (priority := high) commRing : CommRing ℚ_[p] := CauSeq.Completion.Cauchy.commRing

/-- Computable instance. -/
instance (priority := high) : CommSemiring ℚ_[p] := (commRing p).toCommSemiring

/-- Computable instance. -/
instance (priority := high) : Semiring ℚ_[p] := (commRing p).toSemiring

theorem isTopologicallyNilpotent_p_pow_iff
    (p : ℕ) [Fact p.Prime] (n : ℤ) :
    IsTopologicallyNilpotent (p ^ n : ℚ_[p]) ↔ 0 < n := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  grw [isTopologicallyNilpotent_iff_norm_lt_one, Padic.norm_p_zpow,
    zpow_lt_one_iff_right₀ hp, neg_neg_iff_pos]

@[simp] theorem isTopologicallyNilpotent_p (p : ℕ) [Fact p.Prime] :
    IsTopologicallyNilpotent (p : ℚ_[p]) := by
  simpa using isTopologicallyNilpotent_p_pow_iff p 1

end Padic
