module

import RogersRamanujan.NumberTheory.QTheory.Basic
public import RogersRamanujan.NumberTheory.QTheory.Defs
import RogersRamanujan.NumberTheory.QTheory.Nonarchimedean
import RogersRamanujan.NumberTheory.QTheory.StrongNonarchimedean
import RogersRamanujan.Order.Filter.Prod
import RogersRamanujan.RingTheory.NonUnitalSubring.Basic
import RogersRamanujan.Topology.Algebra.InfiniteSum.Nonarchimedean
public import RogersRamanujan.Topology.Algebra.Nonarchimedean.Strong
import RogersRamanujan.Topology.UniformSpace.UniformConvergence
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-! # General q-binomial theorem

We prove the q-binomial theorem in strongly nonarchimedean rings:
the q-Pochhammer symbol `(-a; q)_∞` equals `∑ a^k q^{k(k-1)/2} / (q; q)_k`,
and derive the q-exponential identity and general q-binomial theorem.

## Main results

* `qPochhammerInf_neg_eq_tsum`: `(-a; q)_∞ = ∑ a^k q^{k choose 2} / (q; q)_k`
* `qPochhammerInf_eq_tsum`: `(a; q)_∞ = ∑ (-a)^k q^{k choose 2} / (q; q)_k`
* `inv_qPochhammerInf_eq_tsum`: `1/(a; q)_∞ = ∑ a^n / (q; q)_n` (q-exponential)
* `qPochhammerInf_div_qPochhammerInf_eq_tsum`: general q-binomial theorem
-/

@[expose] public section

open Finset Filter Topology SummationFilter

open scoped QTheory

variable {R : Type*} [CommRing R]

/-- The inner summand of `(a; q)_∞` expressed as an infinite sum.

See `qPochhammerInf_neg_eq_tsum` and `qPochhammerInf_eq_tsum`. -/
noncomputable def qPochhammerInfInner (a q : R) (k : ℕ) : R :=
  bInv (q; q)_k * (a ^ k * q ^ k.choose 2)

variable [UniformSpace R] [IsUniformAddGroup R]
  [StrongNonarchimedeanRing R] [CompleteSpace R] [T2Space R] {a q z : R}

-- TODO: remove complete
theorem tendsto_qPochhammerInfInner_zero (a : R) {q : R} (hq : IsTopologicallyNilpotent q) :
    Tendsto (qPochhammerInfInner a q) atTop (𝓝 0) := by
  have h := (tendsto_bInv_qPochhammer_bInv_qPochhammerInf hq).mul
      (tendsto_pow_mul_pow_choose_two (a := a) hq)
  simp only [mul_zero] at h
  exact h.congr fun n ↦ by simp [qPochhammerInfInner]

theorem summable_qPochhammerInfInner (a : R) {q : R} (hq : IsTopologicallyNilpotent q) :
    Summable (qPochhammerInfInner a q) :=
  NonarchimedeanAddGroup.summable_of_tendsto_atTop_zero <| tendsto_qPochhammerInfInner_zero a hq

/-- Uniform convergence of the q-binomial approximants
`f(n,k) = qChoose q n k * a^k * q^{k choose 2}` to their limit
`l(k) = bInv (q; q)_k * a^k * q^{k choose 2}`.

The error `f(n,k) - l(k)` is controlled in four regions:
* *Small k* (`k < K`): pointwise convergence `f(n,k) → l(k)`.
* *Large gap* (`K ≤ k ≤ n` with `n-k ≥ K₁`): factorization
  `f-l = bInv (q; q)_k * (tail-1) * (a^k q^{k choose 2})` with each
  factor in a suitable subgroup `V`.
* *Near n* (`n-k < K₁`): use `qChoose_symm` to reduce to `f(n, n-m)` with `m` bounded,
  and `f(n, n-m) → 0` and `l(n-m) → 0`.
* *Beyond n* (`k > n`): `f(n,k) = 0` and `l(k) → 0`. -/
theorem tendstoUniformly_qChoose_mul_pow
    (hq : IsTopologicallyNilpotent q) :
    TendstoUniformly (fun n k ↦ qChoose q n k * a ^ k * q ^ k.choose 2)
      (qPochhammerInfInner a q) atTop := by
  unfold qPochhammerInfInner
  simp_rw [mul_assoc]
  set f : ℕ → ℕ → R := fun n k ↦ qChoose q n k * (a ^ k * q ^ k.choose 2)
  set l : ℕ → R := fun k ↦ bInv (q; q)_k * (a ^ k * q ^ k.choose 2)
  set u : ℕ → R := fun k ↦ a ^ k * q ^ k.choose 2
  have hu : Tendsto u atTop (𝓝 0) := tendsto_pow_mul_pow_choose_two hq
  have hfl (k) : Tendsto (f · k - l k) atTop (𝓝 0) :=
    tendsto_sub_nhds_zero_iff.mpr ((tendsto_qChoose hq k).mul_const _)
  have hl : Tendsto l atTop (𝓝 0) := by
    convert (tendsto_bInv_qPochhammer_bInv_qPochhammerInf hq).mul hu
    simp
  have hfnm (m) : Tendsto (fun n ↦ f n (n - m)) atTop (𝓝 0) := by
    have hcongr : (fun n ↦ qChoose q n (n - m)) =ᶠ[atTop] fun n ↦ qChoose q n m :=
      eventually_atTop.mpr ⟨m, fun n hn ↦ qChoose_symm hn⟩
    have key : Tendsto (fun n ↦ qChoose q n (n - m) * u (n - m)) atTop (𝓝 0) := by
      have := (tendsto_qChoose hq m).congr' hcongr.symm |>.mul (hu.comp <| tendsto_sub_atTop_nat m)
      simpa [mul_zero] using this
    exact key.congr fun n ↦ by simp [f, u]
  have hflnm : Tendsto (fun p : ℕ × ℕ ↦ f (p.1 + p.2) p.2 - l p.2) (atTop ×ˢ atTop) (𝓝 0) := by
    simp_rw [f, l, qChoose_add_eq_bInv_mul_qPochhammer hq, ← sub_mul, ← mul_sub_one]
    convert ((tendsto_bInv_qPochhammer_bInv_qPochhammerInf hq).snd'.mul
      (((tendsto_qPochhammer_nhds_atTop hq).comp
        ((hq.comp (tendsto_add_atTop_nat 1)).prodMap tendsto_id)).sub_const 1)).mul hu.snd' using 2
    all_goals simp [u]
  rw [hasBasis_nhds_zero_openSubrng.tendstoUniformly_iff']
  intro U _
  have hun := U.mem_nhds_zero
  obtain ⟨N₁, -, hN₁⟩ := atTop_basis.prod_self.mem_iff.mp (hflnm hun)
  obtain ⟨N₂, -, hN₂⟩ := atTop_basis.mem_iff.mp (hl hun)
  set N := max N₁ N₂
  filter_upwards [(biInter_finset_mem (range N)).mpr (fun i _ ↦ hfl i hun),
    (biInter_finset_mem (range N)).mpr (fun i _ ↦ hfnm i hun),
    Ici_mem_atTop N]
    with n hnk hnnk hnN k
  simp only [mem_range, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe] at *
  by_cases! h₁ : k < N
  · exact hnk _ h₁
  have hlk : l k ∈ U := hN₂ (by grind)
  by_cases! h₂ : n < k
  · simpa [f, qChoose_eq_zero_of_lt h₂]
  by_cases! h₃ : n - k < N
  · exact sub_mem (Nat.sub_sub_self h₂ ▸ hnnk _ h₃) hlk
  exact Nat.sub_add_cancel h₂ ▸ @hN₁ (_, _) (by grind)

/-- `q`-Expansion of the infinite `q`-Pochhammer symbol:

`(-a; q)_∞ = ∑ₖ (q; q)ₖ⁻¹ * aᵏ * q ^ (k choose 2)` -/
theorem qPochhammerInf_neg_eq_tsum
    (hq : IsTopologicallyNilpotent q := by simp) :
    (-a; q)_∞ = ∑' k, qPochhammerInfInner a q k := by
  set f : ℕ → ℕ → R := fun n k ↦ qChoose q n k * a ^ k * q ^ k.choose 2
  have key {n k} (h : n < k) : f n k = 0 := by simp [f, h]
  refine tendsto_nhds_unique (tendsto_qPochhammer_qPochhammerInf hq) ?_
  convert tendsto_tsum_tsum_nat f _ (tendstoUniformly_qChoose_mul_pow hq) fun n ↦ ?_ with n
  · rw [tsum_eq_sum (s := range (n + 1)) (by simp +contextual [key]),
      qPochhammer_eq_sum_qChoose, neg_neg]
  · exact tendsto_const_nhds.congr' <| eventually_atTop.mpr ⟨n + 1, by simp +contextual [key]⟩

theorem hasSum_qPochhammerInf_neg
    (a : R) (hq : IsTopologicallyNilpotent q := by simp) :
    HasSum (fun k ↦ qPochhammerInfInner a q k) (-a; q)_∞ :=
  qPochhammerInf_neg_eq_tsum hq ▸ (summable_qPochhammerInfInner a hq).hasSum

/-- `q`-Expansion of the infinite `q`-Pochhammer symbol:

`(a; q)_∞ = ∑ₖ (q; q)ₖ⁻¹ * (-a)ᵏ * q ^ (k choose 2)` -/
theorem qPochhammerInf_eq_tsum
    (hq : IsTopologicallyNilpotent q := by simp) :
    (a; q)_∞ = ∑' k, qPochhammerInfInner (-a) q k := by
  nth_rw 1 [← neg_neg a, qPochhammerInf_neg_eq_tsum hq]

theorem hasSum_qPochhammerInf
    (a : R) (hq : IsTopologicallyNilpotent q := by simp) :
    HasSum (fun k ↦ qPochhammerInfInner (-a) q k) (a; q)_∞ :=
  qPochhammerInf_eq_tsum hq ▸ (summable_qPochhammerInfInner (-a) hq).hasSum

/-! ## Applications: q-exponential and general q-binomial theorem -/

open Finset

set_option maxHeartbeats 800000 in
-- The `simpa` in this proof is slow under v4.31 due to whnf performance regression.
/-- Auxiliary lemma for `inv_qPochhammerInf_eq_tsum` and
`qPochhammerInf_div_qPochhammerInf_eq_tsum`. -/
theorem qPochhammerInf_mul_tsum_eq_tsum
    (hz : IsTopologicallyNilpotent z := by simp) (hq : IsTopologicallyNilpotent q := by simp) :
    ((a * z); q)_∞ * (∑' n, bInv (q; q)_n * z ^ n) = ∑' n, (a; q)_n * bInv (q; q)_n * z ^ n := by
  rw [qPochhammerInf_eq_tsum hq,
    Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_nonarchimedean
      (summable_qPochhammerInfInner (-(a * z)) hq)
      (NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero <| by
        simpa [Nat.cofinite_eq_atTop] using
          (tendsto_bInv_qPochhammer_bInv_qPochhammerInf hq).mul
            hz)]
  refine tsum_congr fun n ↦ ?_
  rw [qPochhammer_eq_sum_qChoose, sum_mul, sum_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine sum_congr rfl fun k hk ↦ ?_
  dsimp
  rw [mem_range_succ_iff] at hk
  rw [qPochhammerInfInner, mul_mul_mul_comm, bInv_qPochhammer_mul_bInv_qPochhammer' hq,
    ← neg_mul, mul_pow, mul_assoc _ (_ ^ _), mul_mul_mul_comm (_ ^ _), ← pow_add,
    Nat.add_sub_cancel' hk]
  ring

-- TODO: remove Strong
theorem qPochhammerInf_mul_tsum_eq_one
    (ha : IsTopologicallyNilpotent a := by simp) (hq : IsTopologicallyNilpotent q := by simp) :
    (a; q)_∞ * ∑' n, bInv (q; q)_n * a ^ n = 1 := by
  simpa [qPochhammer_one_left] using
    qPochhammerInf_mul_tsum_eq_tsum (a := 1) ha hq

-- TODO: remove Strong
@[grind →] theorem isUnit_qPochhammerInf
    (ha : IsTopologicallyNilpotent a := by simp) (hq : IsTopologicallyNilpotent q := by simp) :
    IsUnit (qPochhammerInf a q) :=
  .of_mul_eq_one _ <| qPochhammerInf_mul_tsum_eq_one ha hq

/-- This is the `a = 0` special case of the q-binomial theorem
`(a*z; q)_∞ / (z; q)_∞ = ∑ (a; q)_n / (q; q)_n * z^n`
(see `qPochhammerInf_div_qPochhammerInf_eq_tsum`). -/
theorem bInv_qPochhammerInf_eq_tsum
    (ha : IsTopologicallyNilpotent a := by simp) (hq : IsTopologicallyNilpotent q := by simp) :
    bInv ((a; q)_∞) = ∑' n, bInv (q; q)_n * a ^ n :=
  bInv_eq_of_mul_eq_one <| qPochhammerInf_mul_tsum_eq_one ha hq

theorem hasSum_bInv_qPochhammerInf (a q : R)
    (ha : IsTopologicallyNilpotent a := by simp) (hq : IsTopologicallyNilpotent q := by simp) :
    HasSum (fun n ↦ bInv (q; q)_n * a ^ n) (bInv (a; q)_∞) := by
  refine bInv_qPochhammerInf_eq_tsum ha hq ▸ Summable.hasSum ?_
  refine NonarchimedeanAddGroup.summable_of_tendsto_atTop_zero ?_
  convert (tendsto_bInv_qPochhammer_bInv_qPochhammerInf hq).mul ha
  simp

/-- The **general q-binomial theorem**:
`(a*z; q)_∞ / (z; q)_∞ = ∑ (a; q)_n / (q; q)_n * z^n`. -/
theorem qPochhammerInf_div_qPochhammerInf_eq_tsum
    (hz : IsTopologicallyNilpotent z := by simp) (hq : IsTopologicallyNilpotent q := by simp) :
    ((a * z); q)_∞ * bInv ((z; q)_∞) = ∑' n, (a; q)_n * bInv (q; q)_n * z ^ n := by
  rw [bInv_qPochhammerInf_eq_tsum hz hq, qPochhammerInf_mul_tsum_eq_tsum hz hq]

omit [UniformSpace R] [IsUniformAddGroup R] [StrongNonarchimedeanRing R] [CompleteSpace R]
  [T2Space R] in
/-- **Sum identity for the limiting Bailey lemma**: The sum
`∑_{k=0}^n z^k q^{k(k-1)} qChoose(n,k) (zq^k; q)_{n-k} = 1`.
This is the identity that replaces `qPfaffSaalschutz_denom_cleared` in the limiting case
(`ρ₁, ρ₂ → ∞`) of the Bailey lemma. -/
theorem qBinomial_qPochhammer_sum (n : ℕ) (z : R) :
    ∑ k ∈ range (n + 1),
      z ^ k * q ^ (k * (k - 1)) * qChoose q n k * (z * q ^ k; q)_(n - k) = 1 := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    -- Recurrence: `S(z, n+1) = (1 - z*q^n) * S(z, n) + z*q^n * S(z*q, n) = 1`
    -- Peel off `k=0`, apply alternate Pascal, distribute, and split into SumA + SumB
    rw [sum_range_succ']
    simp_rw [qChoose_succ_succ', Nat.add_sub_add_right, Nat.succ_sub_one]
    conv_lhs => arg 1; arg 2; ext x; rw [mul_add, add_mul]
    simp_rw [sum_add_distrib, show (0 : ℕ) * (0 - 1) = 0 from rfl, pow_zero, one_mul, Nat.sub_zero,
      qChoose_zero, mul_one, one_mul]
    -- Goal: `SumA + SumB + (z)_{n+1} = 1`
    -- Step 3: Show `SumA = z * q^n` (via `ih(z*q)`)
    have hSumA : ∑ x ∈ range (n + 1),
        z ^ (x + 1) * q ^ ((x + 1) * x) * (q ^ (n - x) * qChoose q n x) *
          (z * q ^ (x + 1); q)_(n - x) = z * q ^ n := by
      rw [← mul_one (z * q ^ n), ← ih (z * q), mul_sum]
      refine sum_congr rfl fun x hx ↦ ?_
      have hxn : x ≤ n := by simpa using hx
      have key : q ^ ((x + 1) * x) * q ^ (n - x) = q ^ (x * (x - 1)) * q ^ x * q ^ n := by
        rw [← pow_add, ← pow_add, ← pow_add]; congr 1; rcases x with _ | x <;> grind
      rw [show z * q ^ (x + 1) = z * q * q ^ x by ring]
      linear_combination (z ^ (x + 1) * qChoose q n x * (z * q * q ^ x; q)_(n - x)) * key
    -- Step 4: Show `SumB + (z)_{n+1} = 1 - z * q^n` (via `ih(z)`)
    -- Peel `x=n` from SumB: `C(n,n+1)=0`, so that term vanishes
    rw [hSumA, add_assoc, sum_range_succ,
      qChoose_eq_zero_of_lt (lt_add_one n), mul_zero, zero_mul, add_zero]
    -- Factor `(1 - z * q^n)` from each Pochhammer in `SumB`
    have hpoc : ∀ x ∈ range n, (z * q ^ (x + 1); q)_(n - x) =
        (z * q ^ (x + 1); q)_(n - (x + 1)) * (1 - z * q ^ n) := fun x hx ↦ by
      have hxn : x < n := mem_range.mp hx
      rw [show n - x = n - (x + 1) + 1 by omega, qPochhammer_succ',
        mul_assoc z, ← pow_add, show (x + 1) + (n - (x + 1)) = n by omega]
    rw [sum_congr rfl (fun x hx ↦ by rw [hpoc x hx, ← mul_assoc]), ← sum_mul, qPochhammer_succ',
      ← add_mul]
    -- Recognize `∑ + (z)_n = ih z = 1`
    suffices hih : ∑ i ∈ range n,
        z ^ (i + 1) * q ^ ((i + 1) * i) * qChoose q n (i + 1) *
          (z * q ^ (i + 1); q)_(n - (i + 1)) + (z; q)_n = 1 by
      rw [hih]; ring
    rw [add_comm, ← ih z, sum_range_succ']
    simp [qChoose_zero]
    ring

open scoped Pointwise in
/-- Infinite q-binomial identity: the tsum version of `qBinomial_qPochhammer_sum`. -/
theorem qBinomial_qPochhammer_tsum {z : R} (hq : IsTopologicallyNilpotent q) :
    ∑' k, z ^ k * q ^ (k * (k - 1)) * bInv (q; q)_k * (z * q ^ k; q)_∞ = 1 := by
  set l := fun k ↦ z ^ k * q ^ (k * (k - 1)) * bInv (q; q)_k * (z * q ^ k; q)_∞
  -- `l k → 0`
  have hl0 : Tendsto l atTop (nhds 0) := by
    have hzk : Tendsto (fun k ↦ z ^ k * q ^ (k * (k - 1))) atTop (nhds 0) := by
      have heq : ∀ k : ℕ, z ^ k * q ^ (k * (k - 1)) = (z * q ^ (k - 1)) ^ k := fun k ↦ by
        rw [mul_pow, ← pow_mul, Nat.mul_comm k (k - 1)]
      simp_rw [heq]
      refine tendsto_pow_of_tendsto_zero ?_ tendsto_id
      simpa [Function.comp_def] using
        ((continuous_const_mul z).tendsto 0).comp (hq.comp (tendsto_sub_atTop_nat 1))
    simpa [l, mul_assoc] using (hzk.mul (tendsto_bInv_qPochhammer_bInv_qPochhammerInf hq)).mul
      (tendsto_qPochhammerInf_shift_one (a := z) (q := q) hq)
  have hl_summ : Summable l := by
    rwa [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero, Nat.cofinite_eq_atTop]
  -- Unit lemmas
  have hqu : ∀ k, IsUnit (q; q)_k :=
    isUnit_qPochhammer_of_isUnit_qPochhammerInf hq (isUnit_qPochhammerInf hq hq)
  -- Rewritten finite identity: `(z*q^n; q)_∞ = ∑_{k≤n} l k * (q^{n-k+1}; q)_k`
  have hfin : ∀ n, (z * q ^ n; q)_∞ =
      ∑ k ∈ range (n + 1), l k * (q ^ (n - k + 1); q)_k := fun n ↦ by
    have hid := qBinomial_qPochhammer_sum (q := q) n z
    conv_lhs => rw [show (z * q ^ n; q)_∞ = (z * q ^ n; q)_∞ * 1 from (mul_one _).symm,
      ← hid, mul_sum]
    refine sum_congr rfl fun k hk ↦ ?_
    have hkn : k ≤ n := by have := mem_range.mp hk; omega
    have hqchoose := qChoose_eq_bInv_qPochhammer_mul_qPochhammer hkn (hqu k) (hqu (n - k))
    have hsplit : (z * q ^ k; q)_∞ = (z * q ^ k; q)_(n - k) * (z * q ^ n; q)_∞ := by
      rw [qPochhammerInf_eq_qPochhammer_mul_qPochhammerInf (n - k) hq, mul_assoc,
        ← pow_add, Nat.add_sub_cancel' hkn]
    simp [l, hqchoose, hsplit]; ring
  -- `∑_{k≤n} l k * ((q^{n-k+1}; q)_k - 1) → 0`
  -- TODO: simplify proof
  have herr : Tendsto (fun n ↦ ∑ k ∈ range (n + 1),
      l k * ((q ^ (n - k + 1); q)_k - 1)) atTop (nhds 0) := by
    rw [hasBasis_nhds_zero_openSubrng.tendsto_right_iff]
    intro M _
    rw [eventually_atTop]
    -- `K`: `q^j ∈ M` for `j ≥ K`, `l k ∈ M` for `k ≥ K`
    obtain ⟨K₁, hK₁⟩ := eventually_atTop.mp (hq.eventually M.mem_nhds_zero)
    obtain ⟨K₂, hK₂⟩ := eventually_atTop.mp (hl0.eventually M.mem_nhds_zero)
    -- Pointwise: for `k < K`, `l k * ((q^{n-k+1}; q)_k - 1) → 0`, eventually `∈ M`
    set K := max K₁ K₂
    have hptwise : ∀ k < K, ∀ᶠ n in atTop,
        l k * ((q ^ (n - k + 1); q)_k - 1) ∈ (M : Set R) := fun k _ ↦ by
      have : Tendsto (fun n ↦ (q ^ (n - k + 1); q)_k) atTop (nhds 1) := by
        rw [show (1 : R) = (0; q)_k by simp [qPochhammer]]
        exact (continuous_finsetProd _ fun i _ ↦
          continuous_const.sub (continuous_id.mul continuous_const)).continuousAt.tendsto.comp
          (hq.comp (tendsto_atTop_atTop.mpr fun N ↦ ⟨N + k, fun n hn ↦ by omega⟩))
      exact ((this.sub (tendsto_const_nhds (x := (1 : R)))).const_mul (l k)).eventually
        (M.isOpen.mem_nhds (by simp))
    -- Near-n: for `m < K`, `l (n-m) * ((q^{m+1}; q)_{n-m} - 1) → 0`, eventually `∈ M`
    have hnear : ∀ m < K, ∀ᶠ n in atTop,
        l (n - m) * ((q ^ (m + 1); q)_(n - m) - 1) ∈ (M : Set R) := fun m _ ↦ by
      have hshift : Tendsto (· - m) atTop (atTop : Filter ℕ) :=
        tendsto_atTop_atTop_of_monotone (fun _ _ h ↦ by omega) fun n ↦ ⟨n + m, by omega⟩
      exact ((hl0.comp hshift).mul
        ((tendsto_qPochhammer_qPochhammerInf (a := q ^ (m + 1)) hq).comp hshift |>.sub
          tendsto_const_nhds)).eventually (M.isOpen.mem_nhds (by simp))
    -- Combine
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
      ((Finset.eventually_all (I := range K)).mpr
        (fun k hk ↦ hptwise k (mem_range.mp hk)))
    obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp
      ((Finset.eventually_all (I := range K)).mpr
        (fun m hm ↦ hnear m (mem_range.mp hm)))
    refine ⟨max (max N₁ N₂) (2 * K), fun n hn ↦ ?_⟩
    refine sum_mem fun k hk ↦ ?_
    rw [mem_range] at hk
    have hkn : k ≤ n := by omega
    by_cases hk1 : k < K
    · -- Pointwise case
      exact (hN₁ n (by omega)) k (mem_range.mpr hk1)
    · push Not at hk1
      by_cases hnk : K₁ ≤ n - k
      · -- Middle case: `l k ∈ M` and `(q^{n-k+1}; q)_k - 1 ∈ M`
        have hl_mem : l k ∈ (M : Set R) := hK₂ k (by omega)
        have hpoch_mem : (q ^ (n - k + 1); q)_k - 1 ∈ (M : Set R) := by
          change ∏ i ∈ range k, (1 - q ^ (n - k + 1) * q ^ i) - 1 ∈ (M : Set R)
          exact NonUnitalSubring.prod_sub_one_mem fun i _ ↦ by
            rw [show 1 - q ^ (n - k + 1) * q ^ i - 1 = -(q ^ (n - k + 1 + i)) by
              rw [← pow_add]; ring]
            exact neg_mem (hK₁ _ (by omega))
        exact mul_mem hl_mem hpoch_mem
      · -- Near-n case: `n - k < K`, use hnear with `m = n - k`
        push Not at hnk
        have hm : n - k < K := by omega
        have h := (hN₂ n (by omega)) (n - k) (mem_range.mpr hm)
        rwa [Nat.sub_sub_self hkn] at h
  -- Conclude: `∑' l = 1`
  have hconv : Tendsto (fun n ↦ ∑ k ∈ range (n + 1), l k) atTop (nhds 1) := by
    have hshift := tendsto_qPochhammerInf_shift_one (a := z) (q := q) hq
    rw [show (1 : R) = 1 - 0 by ring]
    exact (hshift.sub herr).congr fun n ↦ by
      rw [hfin, ← sum_sub_distrib]; congr 1; ext k; ring
  have hconv' : Tendsto (fun n ↦ ∑ k ∈ range n, l k) atTop (nhds 1) := by
    rw [show (1 : R) = 1 - 0 by ring]
    exact (hconv.sub hl0).congr fun n ↦ by rw [sum_range_succ]; ring
  exact tendsto_nhds_unique (hl_summ.hasSum.tendsto_sum_nat) hconv'
