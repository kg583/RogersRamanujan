module

public import RogersRamanujan.Algebra.Group.Units.Basic
import RogersRamanujan.NumberTheory.QTheory.Basic
public import RogersRamanujan.NumberTheory.QTheory.Defs
import RogersRamanujan.NumberTheory.QTheory.Topology
import RogersRamanujan.Topology.Algebra.TopologicallyNilpotent
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.Algebra.TopologicallyNilpotent
public import Mathlib.Topology.UniformSpace.Cauchy

/-! # Nonarchimedean q-theory
-/

@[expose] public section

open Filter Topology
open scoped QTheory

section topological_space
variable {R : Type*} [CommRing R] [TopologicalSpace R] [NonarchimedeanRing R]

theorem IsTopologicallyNilpotent.one_sub_qPochhammer {a q : R}
    (ha : IsTopologicallyNilpotent a) (hq : IsTopologicallyNilpotent q) (n : ℕ) :
    IsTopologicallyNilpotent (1 - (a; q)_n) := by
  induction n generalizing a with
  | zero => simpa using .zero
  | succ n ih =>
    rw [qPochhammer_succ]
    exact .one_sub_mul (by simpa) (ih <| ha.mul hq)

end topological_space

section complete_space
variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [NonarchimedeanRing R] [CompleteSpace R]

@[grind =>] theorem isUnit_qPochhammer [T2Space R] {a q : R}
    (ha : IsTopologicallyNilpotent a) (hq : IsTopologicallyNilpotent q) (k : ℕ) :
    IsUnit (a; q)_k :=
  (ha.one_sub_qPochhammer hq k).isUnit_of_one_sub

theorem bInv_qPochhammer_mul_bInv_qPochhammer' [T2Space R] {q : R}
    (hq : IsTopologicallyNilpotent q) (m n : ℕ) :
    bInv (q; q)_m * bInv (q; q)_n = qChoose q (m + n) m * bInv (q; q)_(m + n) :=
  bInv_qPochhammer_mul_bInv_qPochhammer <| isUnit_qPochhammer hq hq _

-- split to Basic
theorem qChoose_eq_bInv_mul_qPochhammer [T2Space R] {q : R}
    (hq : IsTopologicallyNilpotent q) {n k : ℕ} (hkn : k ≤ n) :
    qChoose q n k = bInv (q; q)_k * (q ^ (n - k + 1); q)_k := by
  have huk := isUnit_qPochhammer hq hq k
  have hunk := isUnit_qPochhammer hq hq (n - k)
  rw [qChoose_eq_qPochhammer_div_qPochhammer_div_qPochhammer hkn huk hunk, mul_assoc, mul_left_comm]
  nth_rw 1 [← Nat.sub_add_cancel hkn]
  rw [qPochhammer_add', mul_assoc, mul_comm _ (bInv _), hunk.mul_bInv_cancel_assoc, pow_succ']

-- split to Basic
theorem qChoose_add_eq_bInv_mul_qPochhammer [T2Space R] {q : R}
    (hq : IsTopologicallyNilpotent q) {n k : ℕ} :
    qChoose q (n + k) k = bInv (q; q)_k * (q ^ (n + 1); q)_k := by
  simpa using qChoose_eq_bInv_mul_qPochhammer hq (Nat.le_add_left k n)

/-- For each fixed `k`, `qChoose q n k → bInv (q; q)_k` as `n → ∞`. -/
theorem tendsto_qChoose [T2Space R] {q : R}
    (hq : IsTopologicallyNilpotent q) (k : ℕ) :
    Tendsto (fun n ↦ qChoose q n k) atTop (𝓝 (bInv (q; q)_k)) := by
  refine (tendsto_congr' <| eventually_atTop.mpr
    ⟨k, fun _ ↦ qChoose_eq_bInv_mul_qPochhammer hq⟩).mpr ?_
  have key := hq.comp <| (tendsto_add_atTop_nat 1).comp <| tendsto_sub_atTop_nat k
  simpa [qPochhammer_zero_fst] using
    (qPochhammer_continuous_fst.tendsto (0 : R)).comp key |>.const_mul (bInv (q; q)_k)

end complete_space

theorem cauchySeq_qInt
    {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R] [NonarchimedeanAddGroup R]
    {q : R} (hq : IsTopologicallyNilpotent q) :
    CauchySeq (qInt q) :=
  NonarchimedeanAddGroup.cauchySeq_of_tendsto_sub_nhds_zero <| by simpa [qInt_succ']
