module

import RogersRamanujan.Algebra.Group.Units.Hom
import RogersRamanujan.Data.Nat.Choose.Basic
import RogersRamanujan.NumberTheory.QTheory.Basic
public import RogersRamanujan.NumberTheory.QTheory.BinomialTheorem
import RogersRamanujan.NumberTheory.QTheory.JacobiTripleProduct.PowerSeriesIdentity
import RogersRamanujan.NumberTheory.QTheory.Nonarchimedean
import RogersRamanujan.NumberTheory.QTheory.StrongNonarchimedean
import RogersRamanujan.RingTheory.PowerSeries.Evaluation
import Mathlib.RingTheory.MvPowerSeries.LinearTopology
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-! # Jacobi Triple Product

The organization of this folder is as follows:
- `RogersRamanujan/NumberTheory/QTheory/JacobiTripleProduct/NilpotentUnit.lean`:
  Contains a weaker version of the theorem that assumes `a` and `q` are invertible and
  topologically nilpotent.
- `RogersRamanujan\NumberTheory\QTheory\JacobiTripleProduct\PowerSeriesIdentity.lean`:
  Then extracts a family of power series identities that is together equivalent to the
  full version: for each `n : ℕ`, we have:
  `∑' k, ((X; X)_k)⁻¹ * ((X; X)_(k+n))⁻¹ * X^(k(k+n)) = ((X; X)_∞)⁻¹`
  where `X` is the formal variable in the ring of formal power series.
- This file then contains the version in full generality: given `q` topologically nilpotent,
  and `a` and `b` such that `a * b = q`, we have:
  `(q; q)_∞ * (-a; q)_∞ * (-b; q)_∞ = ∑' n : ℤ, abPow a b n * q ^ (|n| choose 2)`
  where `abPow a b (n : ℕ) = a ^ n` and `abPow a b (-(n : ℕ)) = b ^ n` selects either powers of
  `a` or `b` depending on the sign of `n`.

-/

@[expose] public section

open PowerSeries
open scoped QTheory DiscreteTopology

theorem qPochhammerInfInner_add_mul_qPochhammerInfInner {R : Type*} [CommRing R] {a b q : R}
    (hab : a * b = q) (k n : ℕ) :
    qPochhammerInfInner a q (k + n) * qPochhammerInfInner b q k =
    bInv (q; q)_k * bInv (q; q)_(k + n) * a ^ n * q ^ (k * (k + n) + n.choose 2) := by
  rw [← Nat.choose_succ_two_add_choose_add_two]
  simp [qPochhammerInfInner, pow_add, Nat.choose_succ_two,
    show q ^ k = a ^ k * b ^ k by rw [← hab, mul_pow]]
  ring

/-- `abPow a b n` is `a ^ n` for `n ≥ 0` and `b ^ (-n)` for `n < 0`. -/
def abPow {R : Type*} [Pow R ℕ] (a b : R) (n : ℤ) : R := match n with
  | (n : ℕ) => a ^ n
  | Int.negSucc n => b ^ (n + 1)

@[simp] theorem abPow_nat {R : Type*} [Pow R ℕ] (a b : R) (n : ℕ) : abPow a b n = a ^ n := rfl

@[simp] theorem abPow_neg_nat {R : Type*} [Monoid R] (a b : R) (n : ℕ) :
    abPow a b (-n) = b ^ n := by
  obtain _ | n := n
  · simp [abPow]
  rw [Nat.cast_succ, ← Int.negSucc_eq]
  rfl

/-- Reindexing equivalence `ℕ × ℕ ≃ ℤ × ℕ` used to split the JTP double sum by the diagonal. -/
def jtpReindex' : ℕ × ℕ ≃ ℤ × ℕ where
  toFun p := (p.1 - p.2, min p.1 p.2)
  invFun p := if 0 ≤ p.1 then ((p.2 + p.1).toNat, p.2) else (p.2, (p.2 - p.1).toNat)
  left_inv := by grind
  right_inv := by grind

theorem symm_jtpReindex'_nat (n k : ℕ) : jtpReindex'.symm (n, k) = (k + n, k) := rfl

theorem symm_jtpReindex'_neg_nat (n k : ℕ) : jtpReindex'.symm (-n, k) = (k, k + n) := by
  simp [jtpReindex']; grind

section main
variable {R : Type*} [CommRing R]
  [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
  [StrongNonarchimedeanRing R] [T2Space R]
  {a b q : R}

theorem jacobi_triple_product_fiber_nat
    (hq : IsTopologicallyNilpotent q) (hab : a * b = q) (n : ℕ) :
    HasSum (fun k ↦ qPochhammerInfInner a q (jtpReindex'.symm (n, k)).1 *
        qPochhammerInfInner b q (jtpReindex'.symm (n, k)).2)
      (bInv (q; q)_∞ * a ^ n * q ^ n.choose 2) := by
  simp_rw [symm_jtpReindex'_nat, qPochhammerInfInner_add_mul_qPochhammerInfInner hab]
  let f := intEval q
  have hxn : IsTopologicallyNilpotent (X (R := ℤ)) := by simp
  have hfx : f X = q := by simp [f, hq]
  have := (hasSum_bInv_qPochhammer_mul_bInv_qPochhammer_mul_pow ℤ n).map f (by simp [f])
  convert (this.mul_right (a ^ n * q ^ n.choose 2)) using 1
  · rfl
  · funext k
    simp [map_qPochhammer, (isUnit_qPochhammer hxn hxn k).map_bInv f,
      (isUnit_qPochhammer hxn hxn (k + n)).map_bInv f, hfx, pow_add]
    ring
  · rw [(isUnit_qPochhammerInf hxn hxn).map_bInv f, map_qPochhammerInf f (by simp [f]) X hxn, hfx]
    ring

theorem jacobi_triple_product_fiber_neg_nat
    (hq : IsTopologicallyNilpotent q) (hab : a * b = q) (n : ℕ) :
    HasSum (fun k ↦ qPochhammerInfInner a q (jtpReindex'.symm (-n, k)).1 *
        qPochhammerInfInner b q (jtpReindex'.symm (-n, k)).2)
      (bInv (q; q)_∞ * b ^ n * q ^ n.choose 2) := by
  convert jacobi_triple_product_fiber_nat hq (mul_comm a b ▸ hab) n using 2
  simp [symm_jtpReindex'_nat, symm_jtpReindex'_neg_nat, mul_comm]

theorem jacobi_triple_product_fiber
    (hq : IsTopologicallyNilpotent q) (hab : a * b = q) (n : ℤ) :
    HasSum (fun k ↦ qPochhammerInfInner a q (jtpReindex'.symm (n, k)).1 *
        qPochhammerInfInner b q (jtpReindex'.symm (n, k)).2)
      (bInv (q; q)_∞ * abPow a b n * q ^ n.natAbs.choose 2) := by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa using jacobi_triple_product_fiber_nat hq hab n
  · simpa using jacobi_triple_product_fiber_neg_nat hq hab n

theorem jacobi_triple_product_hasSum
    (hq : IsTopologicallyNilpotent q) (hab : a * b = q) :
    HasSum (fun n ↦ abPow a b n * q ^ n.natAbs.choose 2) ((q; q)_∞ * (-a; q)_∞ * (-b; q)_∞) := by
  have h := (hasSum_qPochhammerInf_neg a hq).mul_of_nonarchimedean (hasSum_qPochhammerInf_neg b hq)
  replace h := jtpReindex'.symm.hasSum_iff.mpr h
  replace h := h.prod_fiberwise (jacobi_triple_product_fiber hq hab) |>.mul_left (q; q)_∞
  simp_rw [mul_assoc, (isUnit_qPochhammerInf hq hq).mul_bInv_cancel_assoc, ← mul_assoc] at h
  exact h

theorem jacobi_triple_product
    (hq : IsTopologicallyNilpotent q) (hab : a * b = q) :
    (q; q)_∞ * (-a; q)_∞ * (-b; q)_∞ = ∑' n : ℤ, abPow a b n * q ^ n.natAbs.choose 2 :=
  jacobi_triple_product_hasSum hq hab |>.tsum_eq |>.symm

theorem jacobi_triple_product_hasSum'
    (hq : IsTopologicallyNilpotent q) (hab : a * b = q) :
    HasSum (fun n ↦ abPow (-a) (-b) n * q ^ n.natAbs.choose 2)
      ((q; q)_∞ * (a; q)_∞ * (b; q)_∞) := by
  simpa using jacobi_triple_product_hasSum (a := -a) (b := -b) hq (by simpa)

theorem jacobi_triple_product'
    (hq : IsTopologicallyNilpotent q) (hab : a * b = q) :
    (q; q)_∞ * (a; q)_∞ * (b; q)_∞ = ∑' n : ℤ, abPow (-a) (-b) n * q ^ n.natAbs.choose 2 :=
  jacobi_triple_product_hasSum' hq hab |>.tsum_eq |>.symm

end main
