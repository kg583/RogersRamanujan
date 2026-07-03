module

import RogersRamanujan.Algebra.Group.Commute.Units
public import RogersRamanujan.Algebra.Group.Units.Basic
import RogersRamanujan.Algebra.Polynomial.Degree.Operations
import RogersRamanujan.Data.Nat.Choose.Basic
public import RogersRamanujan.NumberTheory.QTheory.Defs
import RogersRamanujan.RingTheory.NonUnitalSubring.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.RingTheory.NonUnitalSubring.Defs

/-! # Basic definitions in q-theory

We define the following basic objects in q-theory:

* q-integer: `qInt q n = 1 + q + q^2 + ... + q^(n-1)`, notated $[n]_q$ in mathematics.
* q-factorial: `qFactorial q n = [1]_q [2]_q ... [n]_q`, notated $[n]_q!$ in mathematics.
* q-binomial coefficients: `qChoose q n r = [n]_q! / ([r]_q! [n-r]_q!)`,
  notated $\binom{n}{r}_q$ in mathematics.
* q-Pochhammer symbol: `qPochhammer a q n = (1-a)(1-aq)...(1-aq^(n-1))`,
  notated $(a;q)_n$ in mathematics.
* infinite q-Pochhammer symbol: `qPochhammerInf a q = (1-a)(1-aq)(1-aq^2)...`,
  notated $(a;q)_\infty$ in mathematics.

-/

@[expose] public section

open Finset Filter Topology SummationFilter
open scoped QTheory

section CommSemiring
variable {R : Type*} [CommSemiring R] {q : R}
variable {S : Type*} [CommSemiring S]
variable {F : Type*} [FunLike F R S] [RingHomClass F R S] (f : F)

open Polynomial

@[simp]
theorem qInt_zero : qInt q 0 = 0 := rfl

theorem qInt_succ {n : ℕ} : qInt q (n + 1) = 1 + q * qInt q n := by
  simp_rw [qInt, sum_range_succ', pow_succ, pow_zero, ← sum_mul, mul_comm, add_comm]

theorem qInt_succ' {n : ℕ} : qInt q (n + 1) = qInt q n + q ^ n := by
  simp [qInt, sum_range_succ]

@[simp]
theorem qInt_one : qInt q 1 = 1 := by simp [qInt]

@[simp]
theorem qInt_two : qInt q 2 = 1 + q := by simp [qInt_succ]

@[simp]
theorem qInt_three : qInt q 3 = 1 + q + q ^ 2 := by simp [qInt_succ]; ring

@[simp] theorem qInt_one_left {n : ℕ} : qInt (1 : R) n = n := by
  simp [qInt]

theorem qInt_add {a b : ℕ} : qInt q (a + b) = qInt q a + q ^ a * qInt q b := by
  simp [qInt, sum_range_add, pow_add, ← mul_sum]

theorem qInt_add' {a b : ℕ} : qInt q (a + b) = q ^ b * qInt q a + qInt q b := by
  rw [add_comm, qInt_add, add_comm]

/-- Universal property of `qInt` -/
@[simp]
theorem map_qInt {n : ℕ} : f (qInt q n) = qInt (f q) n := by simp [qInt]

private theorem monic_qInt_and_degree_qInt [Nontrivial R] {n : ℕ} :
    (qInt X (n + 1) : R[X]).Monic ∧ (qInt X (n + 1) : R[X]).degree = n :=
  n.recOn (by simp) fun n ih ↦ by
  have key : (qInt (X : R[X]) (n + 1)).degree < (n + 1 :) := by rw [ih.2, Nat.cast_lt]; grind
  rw [qInt_succ', add_comm]
  exact ⟨monic_X_pow_add key, degree_X_pow_add key⟩

theorem monic_qInt_succ {n : ℕ} : (qInt X (n + 1) : R[X]).Monic := by
  nontriviality R
  exact monic_qInt_and_degree_qInt.1

theorem monic_qInt : ∀ n : ℕ, 0 < n → (qInt X n : R[X]).Monic
  | _ + 1, _ => monic_qInt_succ

@[simp]
theorem degree_qInt [Nontrivial R] {n : ℕ} :
    (qInt X (n + 1) : R[X]).degree = n := monic_qInt_and_degree_qInt.2

theorem one_sub_mul_qInt {R : Type*} [CommRing R] {q : R} {n : ℕ} :
    (1 - q) * qInt q n = 1 - q ^ n := mul_neg_geom_sum q n

@[simp]
theorem qFactorial_zero : qFactorial q 0 = 1 := rfl

theorem qFactorial_succ (n : ℕ) : qFactorial q (n + 1) = qInt q (n + 1) * qFactorial q n := by
  simp_rw [qFactorial, prod_range_succ, mul_comm]

@[simp]
theorem qFactorial_one : qFactorial q 1 = 1 := by simp [qFactorial_succ]

@[simp]
theorem qFactorial_two : qFactorial q 2 = 1 + q := by simp [qFactorial_succ]

@[simp]
theorem qFactorial_three : qFactorial q 3 = 1 + 2 * q + 2 * q ^ 2 + q ^ 3 := by
  simp [qFactorial_succ]; ring

/-- Universal property of `qFactorial` -/
@[simp]
theorem map_qFactorial {n : ℕ} : f (qFactorial q n) = qFactorial (f q) n := by simp [qFactorial]

theorem monic_qFactorial {n} : (qFactorial X n : R[X]).Monic :=
  monic_prod_of_monic _ _ fun _ _ ↦ monic_qInt_succ

theorem qFactorial_ne_zero [Nontrivial R] {n : ℕ} : (qFactorial X n : R[X]) ≠ 0 :=
  monic_qFactorial.ne_zero

theorem degree_qFactorial [Nontrivial R] {n : ℕ} :
    (qFactorial X n : R[X]).degree = (n * (n - 1) / 2 :) := by
  rw [qFactorial, degree_prod_of_monic _ _ fun _ _ ↦ monic_qInt_succ]
  simp_rw [degree_qInt, ← Nat.cast_sum _ fun x ↦ x, sum_range_id]

@[simp]
theorem qChoose_zero : ∀ {n}, qChoose q n 0 = 1
  | 0 => rfl
  | _ + 1 => rfl

@[simp]
theorem qChoose_eq_zero_of_lt : ∀ {n k}, n < k → qChoose q n k = 0
  | 0, _ + 1, _ => by simp [qChoose]
  | _ + 1, 0, h => by grind
  | n + 1, k + 1, h => by
    rw [qChoose, qChoose_eq_zero_of_lt (by omega), qChoose_eq_zero_of_lt (by omega)]
    simp

theorem qChoose_succ_succ {n k} : qChoose q (n + 1) (k + 1) =
    qChoose q n k + q ^ (k + 1) * qChoose q n (k + 1) := rfl

@[simp high]
theorem qChoose_zero_succ {n : ℕ} : qChoose q 0 (n + 1) = 0 := by simp [qChoose]

theorem qChoose_zero_fst (n : ℕ) : qChoose q 0 n = if n = 0 then 1 else 0 :=
  n.casesOn (by simp) (by simp)

@[simp]
theorem qChoose_self : ∀ {n}, qChoose q n n = 1
  | 0 => rfl
  | n + 1 => by rw [qChoose, qChoose_self, qChoose_eq_zero_of_lt (by omega)]; simp

@[simp]
theorem qChoose_one_right : ∀ {n}, qChoose q n 1 = qInt q n
  | 0 => by simp [qChoose]
  | n + 1 => by rw [qChoose, qChoose_one_right]; simp [qInt_succ]

theorem qChoose_mul_qFactorial_mul_qFactorial : ∀ {n k}, k ≤ n →
    qChoose q n k * qFactorial q k * qFactorial q (n - k) = qFactorial q n
  | 0, 0, _ => by simp
  | 0, _ + 1, h => by grind
  | _ + 1, 0, _ => by simp
  | n + 1, k + 1, h => by
    have hkn : k ≤ n := by omega
    obtain rfl | hkn' := hkn.eq_or_lt
    · simp [qChoose_self]
    rw [Nat.add_sub_add_right, qChoose]
    have hk1n : k + 1 ≤ n := by omega
    rw [add_mul, add_mul]
    nth_rw 2 [show n - k = n - (k + 1) + 1 by omega]
    nth_rw 1 [qFactorial_succ]
    nth_rw 2 [qFactorial_succ]
    nth_rw 1 [show n - (k + 1) + 1 = n - k by omega]
    trans qChoose q n k * qFactorial q k * qFactorial q (n - k) * qInt q (k + 1) +
      qChoose q n (k + 1) * qFactorial q (k + 1) * qFactorial q (n - (k + 1)) *
        (q ^ (k + 1) * qInt q (n - k))
    · ring
    rw [qChoose_mul_qFactorial_mul_qFactorial hkn, qChoose_mul_qFactorial_mul_qFactorial hk1n,
      ← mul_add, ← qInt_add, show k + 1 + (n - k) = n + 1 by omega, mul_comm, qFactorial_succ]

/-- Universal property of `qChoose` -/
@[simp]
theorem map_qChoose : ∀ {n k}, f (qChoose q n k) = qChoose (f q) n k
  | _, 0 => by simp
  | 0, _ + 1 => by simp
  | n + 1, k + 1 => by simp_rw [qChoose, map_add, map_mul, map_qChoose]; simp

theorem qChoose_symm {n k : ℕ} (hkn : k ≤ n) : qChoose q n (n - k) = qChoose q n k := by
  rw [← aeval_X (R := ℕ) (x := q), ← map_qChoose, ← map_qChoose]
  congr 1
  refine mul_right_cancel₀ (qFactorial_ne_zero (n := k)) ?_
  refine mul_right_cancel₀ (qFactorial_ne_zero (n := n - k)) ?_
  rw [qChoose_mul_qFactorial_mul_qFactorial hkn, mul_right_comm]
  nth_rw 3 [show k = n - (n - k) by omega]
  rw [qChoose_mul_qFactorial_mul_qFactorial (by omega)]

theorem qChoose_succ_succ' {n k} : qChoose q (n + 1) (k + 1) =
    q ^ (n - k) * qChoose q n k + qChoose q n (k + 1) := by
  obtain hnk | rfl | hkn := lt_trichotomy n k
  · simp [*, show n < k + 1 by omega]
  · simp
  rw [← qChoose_symm (by omega), show n + 1 - (k + 1) = n - (k + 1) + 1 by omega,
    qChoose_succ_succ, qChoose_symm (by omega), show n - (k + 1) + 1 = n - k by omega,
    qChoose_symm (by omega)]
  ring

theorem monic_qChoose {n k : ℕ} (hkn : k ≤ n) : (qChoose X n k : R[X]).Monic :=
  .of_mul_monic_right (monic_qFactorial (n := k)) <|
    .of_mul_monic_right (monic_qFactorial (n := n - k)) <|
      qChoose_mul_qFactorial_mul_qFactorial (q := (X : R[X])) hkn ▸ monic_qFactorial

theorem qChoose_X_ne_zero [Nontrivial R] {n k : ℕ} (hkn : k ≤ n) : (qChoose X n k : R[X]) ≠ 0 :=
  (monic_qChoose hkn).ne_zero

theorem qChoose_X_eq_zero_iff [Nontrivial R] {n k : ℕ} :
    (qChoose X n k : R[X]) = 0 ↔ n < k := by
  obtain hkn | hnk := le_or_gt k n
  · exact iff_of_false (qChoose_X_ne_zero hkn) (not_lt.mpr hkn)
  · exact iff_of_true (qChoose_eq_zero_of_lt hnk) hnk

theorem qChoose_X_ne_zero_iff [Nontrivial R] {n k : ℕ} :
    qChoose (X : R[X]) n k ≠ 0 ↔ k ≤ n := by
  rw [ne_eq, qChoose_X_eq_zero_iff, not_lt]

private theorem natDegree_qChoose_natX : ∀ {n k}, (qChoose X n k : ℕ[X]).natDegree = k * (n - k)
  | _, 0 => by simp
  | 0, _ + 1 => by simp
  | n + 1, k + 1 => by
    obtain hnk | hkn := lt_or_ge n k
    · rw [qChoose_eq_zero_of_lt (by omega), natDegree_zero,
        show n + 1 - (k + 1) = 0 by omega, mul_zero]
    obtain rfl | hkn := hkn.eq_or_lt
    · simp [qChoose_self]
    have key : (X ^ (k + 1) * qChoose X n (k + 1) : ℕ[X]).natDegree = (k + 1) * (n - k) := by
      rw [natDegree_mul (by simp) (qChoose_X_ne_zero (by omega)),
        natDegree_qChoose_natX, natDegree_X_pow, ← mul_one_add,
        show 1 + (n - (k + 1)) = n - k by omega]
    rw [qChoose, natDegree_add_eq_right_of_natDegree_lt, key, Nat.add_sub_add_right]
    rw [natDegree_qChoose_natX, key]
    have : 0 < n - k := by omega
    nlinarith

theorem natDegree_qChoose [Nontrivial R] {n k} :
    (qChoose X n k : R[X]).natDegree = k * (n - k) := by
  obtain hnk | hkn := lt_or_ge n k
  · simp [qChoose_eq_zero_of_lt hnk]
    omega
  rw [← aeval_X (R := ℕ) X, aeval_X_left_eq_map, ← coe_mapRingHom, ← map_qChoose, coe_mapRingHom,
    natDegree_map_eq_of_isUnit_leadingCoeff, natDegree_qChoose_natX]
  rw [monic_qChoose hkn]
  exact isUnit_one

end CommSemiring

section qPochhammer

variable {R : Type*} [CommRing R] {a q : R} {m n k : ℕ}
variable {S : Type*} [CommRing S] {F : Type*} [FunLike F R S] [RingHomClass F R S] (f : F)

@[simp]
theorem qPochhammer_zero : (a; q)_0 = 1 := by simp [qPochhammer]

theorem qPochhammer_succ' : (a; q)_(n + 1) = (a; q)_n * (1 - a * q ^ n) :=
  prod_range_succ _ _

theorem qPochhammer_add :
    (a; q)_(n + k) = (a; q)_k * (a * q ^ k; q)_n := by
  rw [add_comm, qPochhammer, prod_range_add]
  grind [qPochhammer]

theorem qPochhammer_add' (n k : ℕ) :
    (a; q)_(n + k) = (a; q)_n * (a * q ^ n; q)_k := by
  rw [add_comm, qPochhammer_add]

/-- Splitting `(q; q)_n` on the left: `(q; q)_n = (q; q)_k * (q^{k+1}; q)_{n-k}` for `k ≤ n`. -/
lemma qPochhammer_qq_add_left (q : R) {n k : ℕ} (hk : k ≤ n) :
    (q; q)_n = (q; q)_k * (q ^ (k + 1); q)_(n - k) := by
  conv_lhs => rw [show n = k + (n - k) by omega]
  rw [qPochhammer_add', show q * q ^ k = q ^ (k + 1) by ring]

/-- Splitting `(q; q)_n` on the right: `(q; q)_n = (q; q)_{n-k} * (q^{n+1-k}; q)_k` for `k ≤ n`. -/
lemma qPochhammer_qq_add_right (q : R) {n k : ℕ} (hk : k ≤ n) :
    (q; q)_n = (q; q)_(n - k) * (q ^ (n + 1 - k); q)_k := by
  conv_lhs => rw [show n = (n - k) + k by omega]
  rw [qPochhammer_add', show q * q ^ (n - k) = q ^ (n + 1 - k) by
    rw [show n + 1 - k = (n - k) + 1 by omega]; ring]

theorem qPochhammer_split_of_le (h : k ≤ n) :
    (a; q)_n = (a; q)_k * (a * q ^ k; q)_(n - k) := by
  conv_lhs => rw [← Nat.add_sub_cancel' h]
  exact qPochhammer_add' k (n - k)

theorem qPochhammer_split_of_le' (h : k ≤ n) :
    (a; q)_n = (a; q)_(n - k) * (a * q ^ (n - k); q)_k := by
  conv_lhs => rw [← Nat.sub_add_cancel h]
  exact qPochhammer_add' (n - k) k

theorem qPochhammer_split_of_add_eq {j k n : ℕ} (hjk : j + k = n) :
    (a; q)_n = (a; q)_j * (a * q ^ j; q)_k := hjk ▸ qPochhammer_add' j k

theorem qPochhammer_mul_eq_prod_range (m k : ℕ) :
    (a; q)_(m * k) = ∏ j ∈ Finset.range m, (a * q ^ j; q ^ m)_k := by
  induction k with
  | zero => simp [qPochhammer]
  | succ k ih =>
    rw [show m * (k + 1) = m * k + m by ring, qPochhammer_add' (m * k) m, ih]
    simp_rw [qPochhammer_succ' (n := k), Finset.prod_mul_distrib]
    congr 1
    simp only [qPochhammer]
    refine Finset.prod_congr rfl fun j _ => ?_
    congr 1; ring

@[simp]
theorem qPochhammer_one : (a; q)_1 = 1 - a := by simp [qPochhammer_succ']

theorem qPochhammer_succ : (a; q)_(n + 1) = (1 - a) * (a * q; q)_n := by
  simp [qPochhammer_add]

@[simp]
theorem qPochhammer_two : (a; q)_2 = (1 - a) * (1 - a * q) := by simp [qPochhammer_succ']

@[simp]
theorem qPochhammer_three : (a; q)_3 = (1 - a) * (1 - a * q) * (1 - a * q ^ 2) := by
  simp [qPochhammer_succ']

@[simp]
theorem qPochhammer_one_eq_zero {n : ℕ} (hn : n ≠ 0) : (1; q)_n = 0 :=
  prod_eq_zero (by simpa [← pos_iff_ne_zero] using hn) (by simp)

theorem qPochhammer_pow_bInv_eq_zero {m k : ℕ} (hk : m < k) : (bInv q ^ m; q)_k = 0 := by
  by_cases hqu : IsUnit q
  · exact prod_eq_zero (mem_range.mpr hk) (by simp [← mul_pow, hqu])
  · rw [bInv_eq_one_of_not_isUnit hqu, one_pow, qPochhammer_one_eq_zero (by grind)]

theorem one_sub_pow_mul_qFactorial : (1 - q) ^ n * qFactorial q n = (q; q)_n := by
  nth_rw 1 [← card_range n]
  simp_rw [qFactorial, ← prod_const, ← prod_mul_distrib, one_sub_mul_qInt, pow_succ', qPochhammer]

theorem qChoose_mul_qPochhammer_mul_qPochhammer (hkn : k ≤ n) :
    qChoose q n k * (q; q)_k * (q; q)_(n - k) = (q; q)_n := by
  rw [← one_sub_pow_mul_qFactorial, ← one_sub_pow_mul_qFactorial,
    mul_assoc, mul_mul_mul_comm, ← pow_add, ← mul_assoc, mul_right_comm, ← mul_assoc,
    qChoose_mul_qFactorial_mul_qFactorial hkn, show k + (n - k) = n by omega, mul_comm,
    one_sub_pow_mul_qFactorial]

@[simp]
theorem qPochhammer_zero_fst : (0; q)_n = 1 := by simp [qPochhammer]

theorem qPochhammer_one_left : (1; q)_n = if n = 0 then 1 else 0 := by
  split_ifs <;> simp [*]

/-- universal property of `qPochhammer` -/
theorem map_qPochhammer : f (a; q)_n = (f a; f q)_n := by simp [qPochhammer]

/-- The pre-cancellation form of `qPochhammer_qChoose_coeff`: both sides multiplied through by the
common factor `(q; q)_k * (q; q)_(n-k)`, which holds before cancelling and avoids the need for the
factor to be a non-zero-divisor. -/
lemma qPochhammer_qChoose_coeff_mul_factor (q : R) {n k : ℕ} (hk : k ≤ n) :
    (q; q)_n * qChoose q n k * ((q; q)_k * (q; q)_(n - k)) =
    (q ^ (n + 1 - k); q)_k * (q ^ (k + 1); q)_(n - k) * ((q; q)_k * (q; q)_(n - k)) := by
  calc (q; q)_n * qChoose q n k * ((q; q)_k * (q; q)_(n - k))
      = (qChoose q n k * (q; q)_k * (q; q)_(n - k)) * (q; q)_n := by ring
    _ = (q; q)_n * (q; q)_n := by rw [qChoose_mul_qPochhammer_mul_qPochhammer hk (q := q)]
    _ = ((q; q)_(n - k) * (q ^ (n + 1 - k); q)_k) *
          ((q; q)_k * (q ^ (k + 1); q)_(n - k)) := by
        rw [← qPochhammer_qq_add_right q hk, ← qPochhammer_qq_add_left q hk]
    _ = (q ^ (n + 1 - k); q)_k * (q ^ (k + 1); q)_(n - k) *
          ((q; q)_k * (q; q)_(n - k)) := by ring

/-- The q-binomial coefficient `qChoose n k` expressed via shifted q-Pochhammer symbols:
`(q; q)_n * qChoose n k = (q^{n+1-k}; q)_k * (q^{k+1}; q)_{n-k}` for `k ≤ n`. -/
theorem qPochhammer_qChoose_coeff (q : R) {n k : ℕ} (hk : k ≤ n) :
    (q; q)_n * qChoose q n k = (q ^ (n + 1 - k); q)_k * (q ^ (k + 1); q)_(n - k) := by
  have hne : qPochhammer (Polynomial.X : Polynomial ℤ) Polynomial.X k *
      qPochhammer Polynomial.X Polynomial.X (n - k) ≠ 0 := fun h => by
    simpa [map_mul, map_qPochhammer, qPochhammer_zero_fst] using
      congr_arg (Polynomial.evalRingHom (0 : ℤ)) h
  have hpoly := mul_right_cancel₀ hne
    (qPochhammer_qChoose_coeff_mul_factor (Polynomial.X : Polynomial ℤ) hk)
  simpa only [map_mul, map_qPochhammer, map_qChoose, map_pow, Polynomial.aeval_X]
    using congr_arg (Polynomial.aeval q) hpoly

/-- The q-analogue of `Nat.choose_mul`, the "subset of a subset" identity:
`qChoose n k * qChoose k s = qChoose n s * qChoose (n-s) (k-s)` for `s ≤ k`. -/
theorem qChoose_mul (q : R) {n k s : ℕ} (hsk : s ≤ k) :
    qChoose q n k * qChoose q k s = qChoose q n s * qChoose q (n - s) (k - s) := by
  obtain hnk | hkn := lt_or_ge n k
  · rw [qChoose_eq_zero_of_lt hnk, zero_mul]
    rcases lt_or_ge n s with hns | hsn
    · rw [qChoose_eq_zero_of_lt hns, zero_mul]
    · rw [qChoose_eq_zero_of_lt (show n - s < k - s by omega), mul_zero]
  suffices hpoly : qChoose (Polynomial.X (R := ℤ)) n k * qChoose Polynomial.X k s =
      qChoose Polynomial.X n s * qChoose Polynomial.X (n - s) (k - s) by
    simpa only [map_mul, map_qChoose, Polynomial.aeval_X]
      using congr_arg (Polynomial.aeval q) hpoly
  set p := (Polynomial.X (R := ℤ))
  refine mul_right_cancel₀ (mul_ne_zero (mul_ne_zero qFactorial_ne_zero qFactorial_ne_zero)
    qFactorial_ne_zero : qFactorial p (n - k) * qFactorial p (k - s) * qFactorial p s ≠ 0) ?_
  calc qChoose p n k * qChoose p k s *
        (qFactorial p (n - k) * qFactorial p (k - s) * qFactorial p s) =
      qChoose p n k *
          (qChoose p k s * qFactorial p s * qFactorial p (k - s)) * qFactorial p (n - k) := by ring
    _ = qFactorial p n := by
        rw [qChoose_mul_qFactorial_mul_qFactorial hsk,
          qChoose_mul_qFactorial_mul_qFactorial hkn]
    _ = qChoose p n s * qFactorial p s *
          (qChoose p (n - s) (k - s) * qFactorial p (k - s) * qFactorial p (n - k)) := by
        rw [show n - k = (n - s) - (k - s) by omega,
          qChoose_mul_qFactorial_mul_qFactorial (show k - s ≤ n - s by omega),
          qChoose_mul_qFactorial_mul_qFactorial (show s ≤ n by omega)]
    _ = qChoose p n s * qChoose p (n - s) (k - s) *
          (qFactorial p (n - k) * qFactorial p (k - s) * qFactorial p s) := by ring

/-- The **q-binomial theorem**:
$$(a;q)_n = \sum_{k=0}^{n} \binom{n}{k}_q (-a)^k q^{\binom{k}{2}}$$
This is the q-analogue of the binomial theorem $(1-a)^n = \sum_k \binom{n}{k}(-a)^k$. -/
theorem qPochhammer_eq_sum_qChoose :
    (a; q)_n = ∑ k ∈ range (n + 1), qChoose q n k * (-a) ^ k * q ^ k.choose 2 := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [qPochhammer_succ, ih]
    trans (1 - a) * ∑ k ∈ range (n + 1), qChoose q n k * (-a) ^ k * q ^ k * q ^ k.choose 2
    · simp_rw [← neg_mul, mul_pow, mul_assoc]
    rw [sub_eq_add_neg, one_add_mul]
    trans ∑ k ∈ range (n + 1), qChoose q n k * (-a) ^ k * q ^ k * q ^ k.choose 2 +
      ∑ k ∈ range (n + 1), qChoose q n k * (-a) ^ (k + 1) * q ^ ((k + 1).choose 2)
    · simp [Nat.choose_succ_two, pow_add, mul_comm, mul_left_comm, mul_assoc, mul_sum]
    trans ∑ k ∈ range n, qChoose q n (k + 1) * q ^ (k + 1) * (-a) ^ (k + 1) * q ^ (k + 1).choose 2 +
      1 + (∑ k ∈ range n, qChoose q n k * (-a) ^ (k + 1) * q ^ (k + 1).choose 2 +
        (-a) ^ (n + 1) * q ^ (n + 1).choose 2)
    · rw [sum_range_succ', sum_range_succ]
      simp [mul_assoc, mul_left_comm]
    trans ∑ k ∈ range n, qChoose q (n + 1) (k + 1) * (-a) ^ (k + 1) * q ^ (k + 1).choose 2 +
      (1 + (-a) ^ (n + 1) * q ^ (n + 1).choose 2)
    · rw [add_add_add_comm, ← sum_add_distrib]
      simp [← add_mul, qChoose_succ_succ, add_comm, mul_comm]
    rw [sum_range_succ, sum_range_succ']
    simp [add_assoc]

/-- **Cauchy's finite q-binomial identity**:
$$(uv;q)_n = \sum_{k=0}^n \binom{n}{k}_q (u;q)_k v^k (v;q)_{n-k}$$
Companion to `qPochhammer_eq_sum_qChoose`. -/
theorem qPochhammer_mul_eq_sum_qChoose (u v : R) (n : ℕ) :
    (u * v; q)_n = ∑ k ∈ range (n + 1), qChoose q n k * (u; q)_k * v ^ k * (v; q)_(n - k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [qPochhammer_succ', ih, sum_mul]
    -- Per-term split: `f_n(k) * (1 - uvq^n) = A(k) + C(k)` via `qPochhammer_succ'` twice.
    trans (∑ k ∈ range (n + 1), qChoose q n k * (u; q)_k * v ^ k * (v; q)_(n + 1 - k)) +
        ∑ k ∈ range (n + 1),
          qChoose q n k * (u; q)_(k + 1) * v ^ (k + 1) * q ^ (n - k) * (v; q)_(n - k)
    · rw [← sum_add_distrib]
      refine sum_congr rfl fun k hk => ?_
      have hk' : k ≤ n := by simpa using hk
      rw [show n + 1 - k = (n - k) + 1 by omega, qPochhammer_succ', qPochhammer_succ' (a := u),
        show q ^ n = q ^ k * q ^ (n - k) by rw [← pow_add]; congr 1; omega]
      ring
    -- Peel k=0 from ∑A and k=n from ∑C, match target after decomposition via q-Pascal.
    rw [sum_range_succ', sum_range_succ, show n + 1 + 1 = (n + 1) + 1 from rfl,
      sum_range_succ' (n := n + 1), sum_range_succ (n := n)]
    simp only [qChoose_zero, qChoose_self, qPochhammer_zero, pow_zero, one_mul, mul_one,
      Nat.sub_self, Nat.sub_zero, Nat.succ_sub_succ_eq_sub]
    rw [add_add_add_comm, ← sum_add_distrib,
      sum_congr rfl fun k _ => show
          qChoose q n (k + 1) * (u; q)_(k + 1) * v ^ (k + 1) * (v; q)_(n - k) +
          qChoose q n k * (u; q)_(k + 1) * v ^ (k + 1) * q ^ (n - k) * (v; q)_(n - k) =
          qChoose q (n + 1) (k + 1) * (u; q)_(k + 1) * v ^ (k + 1) * (v; q)_(n - k) by
        rw [qChoose_succ_succ']; ring]
    ring

theorem qPochhammer_dvd (h : m ≤ n) : (a; q)_m ∣ (a; q)_n := by
  rw [← Nat.sub_add_cancel h, qPochhammer_add]
  simp

theorem qChoose_eq_qPochhammer_div_qPochhammer_div_qPochhammer (hkn : k ≤ n)
    (huk : IsUnit (q; q)_k) (hunk : IsUnit (q; q)_(n - k)) :
    qChoose q n k = (q; q)_n * bInv (q; q)_k * bInv (q; q)_(n - k) := by
  refine hunk.mul_right_cancel <| huk.mul_right_cancel ?_
  rw [mul_right_comm, qChoose_mul_qPochhammer_mul_qPochhammer hkn]
  simp [mul_assoc, *]

theorem bInv_qPochhammer_mul_bInv_qPochhammer (humn : IsUnit (q; q)_(m + n)) :
    bInv (q; q)_m * bInv (q; q)_n = qChoose q (m + n) m * bInv (q; q)_(m + n) := by
  have hum := isUnit_of_dvd_unit (qPochhammer_dvd <| Nat.le_add_right m n) humn
  have hun := isUnit_of_dvd_unit (qPochhammer_dvd <| Nat.le_add_left n m) humn
  rw [qChoose_eq_qPochhammer_div_qPochhammer_div_qPochhammer (by simp) hum (by simpa),
    mul_comm (_ * _)]
  simp [mul_assoc, *]

theorem qChoose_eq_bInv_qPochhammer_mul_qPochhammer (hkn : k ≤ n)
    (hk : IsUnit (q; q)_k) (hnk : IsUnit (q; q)_(n - k)) :
    qChoose q n k = bInv (q; q)_k * (q ^ (n - k + 1); q)_k := by
  have h1 := qChoose_mul_qPochhammer_mul_qPochhammer (q := q) hkn
  have h2 := qPochhammer_add' (a := q) (q := q) (n := n - k) (k := k)
  rw [Nat.sub_add_cancel hkn, show q * q ^ (n - k) = q ^ (n - k + 1) by ring] at h2
  grind

theorem qPochhammer_sub_one_mem {R S : Type*} [CommRing R] [SetLike S R]
    [NonUnitalSubringClass S R] {a q : R} {n : ℕ} {U : S}
    (haqk : ∀ i < n, a * q ^ i ∈ U) : (a; q)_n - 1 ∈ U :=
  NonUnitalSubring.prod_sub_one_mem (by simpa)

theorem qPochhammer_eq_bInv
    (hau : IsUnit a) (hqu : IsUnit q) {n : ℕ} :
    (a; q)_n = (-1) ^ n * a ^ n * q ^ n.choose 2 * (bInv a * bInv q ^ (n - 1); q)_n := by
  simp_rw [pow_eq_prod_const _ n, Nat.choose_two_right, ← sum_range_id,
    ← sum_range_reflect (·), ← prod_pow_eq_pow_sum, qPochhammer, ← prod_mul_distrib]
  rw [← prod_range_reflect]
  obtain _ | n := n
  · rfl
  congr! 1 with i hi
  simp [mul_one_sub, mul_assoc, mul_left_comm, hau, ← pow_add, mem_range_succ_iff.mp hi,
    ← mul_pow, hqu, ← sub_eq_neg_add]

/-- **q-Pochhammer reversal identity**: for `a`, `q` invertible and `n ≤ N`,
`(aq^{-N}; q)_n = (-1)^n * q^{nC2} * q^{-n*N} * (a^{-1}q^{N+1-n}; q)_n`.
-/
theorem qPochhammer_bInv_pow (hqu : IsUnit q) {a : R} (hau : IsUnit a) {n N : ℕ} (hnN : n ≤ N) :
    (a * bInv q ^ N; q)_n =
      (-1) ^ n * a ^ n * q ^ n.choose 2 * bInv q ^ (n * N) * (bInv a * q ^ (N + 1 - n); q)_n := by
  rw [qPochhammer_eq_bInv (hau.mul ((IsUnit.bInv _).pow N)) hqu, mul_pow, ← pow_mul,
    hau.bInv_mul ((IsUnit.bInv _).pow N), bInv_pow, hqu.bInv_bInv]
  obtain _ | n := n
  · simp
  rw [Nat.add_sub_cancel, Nat.add_sub_add_right, mul_assoc (bInv a),
    hqu.pow_mul_bInv_pow_of_ge (by omega : n ≤ N)]
  ring

/-- `qPochhammer_bInv_pow` for `a = 1`, which does not require `n ≤ N`. -/
theorem qPochhammer_bInv_pow' (hqu : IsUnit q) {n N : ℕ} :
    (bInv q ^ N; q)_n = (-1) ^ n * q ^ n.choose 2 * bInv q ^ (n * N) * (q ^ (N + 1 - n); q)_n := by
  rw [qPochhammer_eq_bInv ((IsUnit.bInv _).pow N) hqu, ← pow_mul, bInv_pow, hqu.bInv_bInv]
  obtain _ | n := n
  · simp
  rw [Nat.add_sub_cancel, Nat.add_sub_add_right]
  by_cases! hn : n ≤ N
  · rw [hqu.pow_mul_bInv_pow_of_ge hn]
    ac_rfl
  · rw [hqu.pow_mul_bInv_pow_of_le hn.le, qPochhammer_pow_bInv_eq_zero (by omega),
      Nat.sub_eq_zero_of_le hn.le]
    simp

end qPochhammer
