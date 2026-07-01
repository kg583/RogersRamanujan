module

public import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Operations

/-! # Operations involving polynomial degree
-/

@[expose] public section

namespace Polynomial

theorem degree_X_pow_add {R : Type*} [Semiring R] [Nontrivial R] {p : R[X]} {n : ℕ}
    (H : p.degree < n) : (X ^ n + p).degree = ↑n := by
  rw [degree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow]

end Polynomial
