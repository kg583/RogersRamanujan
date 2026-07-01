module

import RogersRamanujan.Algebra.BigOperators.Intervals
import RogersRamanujan.Algebra.Group.Commute.Units -- shake: keep
import RogersRamanujan.NumberTheory.QTheory.Basic
import RogersRamanujan.NumberTheory.QTheory.BinomialTheorem
public import RogersRamanujan.NumberTheory.QTheory.Defs
import RogersRamanujan.NumberTheory.QTheory.HypergeometricSeries
import RogersRamanujan.NumberTheory.QTheory.StrongNonarchimedean
import RogersRamanujan.Topology.Algebra.InfiniteSum.Nonarchimedean
import RogersRamanujan.Topology.Algebra.Nonarchimedean.Bounded
public import RogersRamanujan.Topology.Algebra.Nonarchimedean.Strong
import RogersRamanujan.Topology.Algebra.TopologicallyNilpotent
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Util.Superscript -- shake: keep

/-!
# Bailey's lemma

We define Bailey pairs and prove Bailey's lemma for q-series (and limit version of it).

## Main definitions and results
* `bailey_lemma_basic`: Bailey lemma for general sequence.
* `IsBaileyPair a q α β`: Two sequences `α, β : ℕ → R` form a Bailey pair.
* `qBaileyLemma`: Bailey lemma for `q`-series.
* `qBaileyLemma_limit`: Limiting version of Bailey lemma, corresponds to `ρ₁, ρ₂ → ∞`.
* `qBaileyLemma_limit'`: Another limiting version of Bailey lemma, corresponds to `ρ₁, ρ₂, n → ∞`.

## References
* G. Andrews, *The Theory of Partitions*
* G. Andrews, *q-Series: Their Development and Applications in Analysis, Number theory,*
              *Combinatorics, Physics, and Computer Algebra*
-/

@[expose] public section

open Finset Filter Topology NonarchimedeanAddGroup
open scoped QTheoryUnsafe

namespace Bailey

/-- Basic Bailey's lemma for general sequence.
If `α, β, γ, δ, u, v` are sequences satisfying
`β_n = ∑_{r=0}^n α_r u_{n-r} v_{n+r}`, `γ_n = ∑_{r=n}^∞ δ_r u_{r-n} v_{r+n}`,
then `∑_{n=0}^∞ α_n γ_n = ∑_{n=0}^∞ β_n δ_n`.
Note that `T3Space` is needed for `Summable.tsum_comm'`.

See Theorem 3.1. of Andrews, "q-Series: Their Development and Application in Analysis,
Number Theory, Combinatorics, Physics, and Computer Algebra".
-/
theorem bailey_lemma_basic {R : Type*} [CommSemiring R] [TopologicalSpace R]
    [IsTopologicalSemiring R] [T3Space R] (u v α β γ δ : ℕ → R)
    (hγ : ∀ n, Summable fun r ↦ if n ≤ r then δ r * u (r - n) * v (r + n) else 0)
    (hswap : Summable (Function.uncurry fun n r : ℕ ↦
      if n ≤ r then α n * δ r * u (r - n) * v (r + n) else 0))
    (hαβ : ∀ n, β n = ∑ r ∈ range (n + 1), α r * u (n - r) * v (n + r))
    (hγδ : ∀ n, γ n = ∑' r, if n ≤ r then δ r * u (r - n) * v (r + n) else 0) :
    ∑' n, α n * γ n = ∑' n, β n * δ n := by
  let f : ℕ → ℕ → R := fun n r ↦ if n ≤ r then α n * δ r * u (r - n) * v (r + n) else 0
  -- Row/column summability for the sum-swap
  have hrow : ∀ n, Summable (f n) := fun n ↦ by
    simpa [f, mul_assoc, mul_left_comm, mul_comm] using (hγ n).mul_left (α n)
  have hcol : ∀ r, Summable (f · r) := fun r ↦ by
    simpa [f] using summable_of_ne_finset_zero (s := range (r + 1)) fun n hn ↦ by grind
  -- Step 1: Expand `γ_n` as a tsum, distribute `α_n` inside
  have h_expand : ∑' n, α n * γ n = ∑' n, ∑' r, f n r := tsum_congr fun n ↦ by
    rw [hγδ n, ← Summable.tsum_mul_left (α n) (hγ n)]
    exact tsum_congr fun r ↦ by by_cases hnr : n ≤ r <;> simp [f, hnr, mul_assoc]
  -- Step 2: Swap `∑'_n ∑'_r` → `∑'_r ∑'_n`
  have h_swap : (∑' n, ∑' r, f n r) = ∑' r, ∑' n, f n r := by
    simpa [f] using (Summable.tsum_comm' hswap hrow hcol).symm
  -- Step 3: Inner tsum has finite support; convert to sum
  have h_tofin : (∑' r, ∑' n, f n r) =
      ∑' r, ∑ n ∈ range (r + 1), δ r * α n * u (r - n) * v (r + n) :=
    tsum_congr fun r ↦ by
      refine (tsum_eq_sum (s := range (r + 1)) ?_).trans ?_
      · grind
      · exact sum_congr rfl fun n hn ↦ by
          simp [f, Nat.lt_succ_iff.mp (mem_range.mp hn), mul_assoc, mul_left_comm, mul_comm]
  -- Step 4: Factor out `δ` and recognize the inner sum as `β`
  have h_beta : (∑' r, ∑ n ∈ range (r + 1), δ r * α n * u (r - n) * v (r + n)) =
      ∑' r, β r * δ r :=
    tsum_congr fun r ↦ by simp [hαβ, mul_sum, mul_assoc, mul_left_comm, mul_comm]
  exact h_expand.trans (h_swap.trans (h_tofin.trans h_beta))

variable {R : Type*} [CommRing R]
variable (a q : R)

/-- **Bailey pair**: Two sequences `α` and `β` form a Bailey pair if they satisfy the relation
`β n = ∑ r ∈ range (n + 1), α r / ((q)_(n-r) * (aq)_(n+r))` for all `n`.
-/
noncomputable def IsBaileyPair (a q : R) (α β : ℕ → R) : Prop :=
  ∀ (n : ℕ),
    β n = ∑ r ∈ range (n + 1),
      α r * bInv (qPochhammer q q (n - r)) * bInv (qPochhammer (a * q) q (n + r))

/-- A triangular family `f n r` tends to `0` on `cofinite (ℕ × ℕ)` once every row tends to `0`
and `f n r ∈ U` eventually holds for `n` large and `r ≥ n`, for every neighborhood `U` of `0`. -/
theorem tendsto_cofinite_zero_triangular {X : Type*} [TopologicalSpace X] [Zero X]
    {f : ℕ → ℕ → X}
    (hrow : ∀ n, Tendsto (f n) atTop (𝓝 0))
    (hlarge : ∀ U ∈ 𝓝 (0 : X), ∀ᶠ n in atTop, ∀ r ≥ n, f n r ∈ U) :
    Tendsto (Function.uncurry fun n r : ℕ ↦ if n ≤ r then f n r else 0) cofinite (𝓝 0) := by
  intro U hU
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlarge U hU)
  choose Nr hNr using fun n ↦ eventually_atTop.mp ((hrow n).eventually hU)
  rw [Filter.mem_map, mem_cofinite]
  refine ((range N ×ˢ range (max N ((range N).sup Nr))).finite_toSet).subset fun ⟨n, r⟩ hbad ↦ ?_
  simp only [coe_product, coe_range, Set.mem_prod, Set.mem_Iio]
  by_contra! hab
  apply hbad
  change (if n ≤ r then f n r else 0) ∈ U
  split_ifs with hnr
  · rcases lt_or_ge n N with hn | hn
    · exact hNr n r <| (le_sup (f := Nr) (mem_range.mpr hn)).trans <|
        (le_max_right _ _).trans (hab hn)
    · exact hN n hn r hnr
  · exact mem_of_mem_nhds hU

/-- **Bailey lemma for q-series**: Let `α, β` be a Bailey pair, and `a`, `ρ₁`, `ρ₂` be elements
of `R` such that `ρ₁` and `ρ₂` are units, `q` is a unit, and all relevant `qPochhammer` values
are units. Define `α', β'` by
`α' n = α n * (ρ₁)_n * (ρ₂)_n * (aq/(ρ₁ρ₂))^n / ((aq/ρ₁)_n * (aq/ρ₂)_n)` and
`β' n = ∑ j, β j * (ρ₁)_j * (ρ₂)_j * (aq/(ρ₁ρ₂))_{n-j} * (aq/(ρ₁ρ₂))^j /`
`((aq/ρ₁)_n * (aq/ρ₂)_n * (q)_{n-j})`.
Then `α', β'` also form a Bailey pair.

The proof uses q-Pfaff-Saalschütz. In particular, it uses `qPfaffSaalschutz_denom_cleared`,
which does not require topology on `R`.

See Theorem 3.3. of Andrews, "q-Series: Their Development and Application in Analysis,
Number Theory, Combinatorics, Physics, and Computer Algebra".

TODO: replace unit conditions with e.g. `∀ k, IsUnit (1 - a * q ^ k)`.
-/
theorem qBaileyLemma (α β α' β' : ℕ → R) (h : IsBaileyPair a q α β)
    (ρ₁ ρ₂ : R) (hρ₁ : IsUnit ρ₁) (hρ₂ : IsUnit ρ₂) (hq : IsUnit q)
    (hqpoc : ∀ k, IsUnit (q)_k)
    (haqpoc : ∀ k, IsUnit (a * q)_k)
    (haqρ₁ : ∀ k, IsUnit (a * q * bInv ρ₁)_k)
    (haqρ₂ : ∀ k, IsUnit (a * q * bInv ρ₂)_k)
    (hα' : ∀ n, α' n = (ρ₁)_n * (ρ₂)_n * (a * q * bInv (ρ₁ * ρ₂)) ^ n *
      bInv (a * q * bInv ρ₁)_n * bInv (a * q * bInv ρ₂)_n * α n)
    (hβ' : ∀ n, β' n = ∑ j ∈ range (n + 1),
      (ρ₁)_j * (ρ₂)_j * (a * q * bInv (ρ₁ * ρ₂))_(n - j) * (a * q * bInv (ρ₁ * ρ₂)) ^ j *
        bInv (a * q * bInv ρ₁)_n * bInv (a * q * bInv ρ₂)_n * bInv ((q)_(n - j)) * β j) :
    IsBaileyPair a q α' β' := by
  intro N
  rw [IsBaileyPair] at h
  simp_rw [hβ' N, hα', h, mul_sum, sum_triangle_reindex]
  apply sum_congr rfl
  intro r hr
  have hrN : r ≤ N := by have := mem_range.mp hr; lia
  simp only [Nat.add_sub_cancel_left, mul_assoc (α r), mul_left_comm _ (α r), mul_comm _ (α r)]
  rw [← mul_sum]
  congr 1
  -- Inner sum identity: use `qPfaffSaalschutz`
  set M := N - r
  -- `qPfaffSaalschutz` parameters
  have hqr : IsUnit (q ^ r) := hq.pow r
  have hρ₁qr : IsUnit (ρ₁ * q ^ r) := hρ₁.mul hqr
  have hρ₂qr : IsUnit (ρ₂ * q ^ r) := hρ₂.mul hqr
  have hzk : ∀ k, IsUnit (a * q * q ^ (2 * r))_k := fun k ↦
    isUnit_of_mul_isUnit_right (by rw [← qPochhammer_add']; exact haqpoc (2 * r + k))
  have hqrinv := hq.pow_mul_bInv_pow_same (n := r)
  have hq2r : q ^ (2 * r) = q ^ r * q ^ r := by ring
  have hc_eq : a * q * q ^ (2 * r) * bInv (ρ₁ * q ^ r) * bInv (ρ₂ * q ^ r) =
      a * q * bInv (ρ₁ * ρ₂) := by
    grind [hρ₁.bInv_mul hqr, hρ₂.bInv_mul hqr, bInv_pow, hρ₁.bInv_mul hρ₂]
  have hbInv_shift (ρ : R) (hρ : IsUnit ρ) :
      a * q * q ^ (2 * r) * bInv (ρ * q ^ r) = a * q * bInv ρ * q ^ r := by
    grind [hρ.bInv_mul hqr, bInv_pow]
  -- Clearing factor `G` and applying `qPfaffSaalschutz`
  set G := (q)_M * (q)_M * (a * q * q ^ (2 * r))_M *
    (a * q * bInv ρ₁)_N * (a * q * bInv ρ₂)_N * (a * q)_(2 * r) with hG_def
  have hGu : IsUnit G := by grind
  apply hGu.mul_left_cancel
  rw [mul_sum]
  have hPS := qPfaffSaalschutz_denom_cleared (q := q) _ _ (a * q * q ^ (2 * r)) M hρ₁qr hρ₂qr
  simp only [hc_eq] at hPS
  rw [hbInv_shift ρ₁ hρ₁, hbInv_shift ρ₂ hρ₂] at hPS
  -- Per-summand identity: `G * summand = common * PS_summand`
  -- TODO: make this shorter
  have h_per : ∀ i ∈ range (M + 1),
      G * ((ρ₁)_(r + i) * (ρ₂)_(r + i) * (a * q * bInv (ρ₁ * ρ₂))_(N - (r + i)) *
            (a * q * bInv (ρ₁ * ρ₂)) ^ (r + i) * bInv (a * q * bInv ρ₁)_N *
              bInv (a * q * bInv ρ₂)_N * bInv (q)_(N - (r + i)) *
                (bInv (q)_i * bInv (a * q)_(r + i + r))) =
      (ρ₁)_(r) * (ρ₂)_(r) * (a * q * bInv (ρ₁ * ρ₂)) ^ r *
        ((ρ₁ * q ^ r)_i * (ρ₂ * q ^ r)_i * (q ^ (M + 1 - i))_i *
          (a * q * bInv (ρ₁ * ρ₂)) ^ i * (q ^ (i + 1))_(M - i) *
            (a * q * q ^ (2 * r) * q ^ i)_(M - i) * (a * q * bInv (ρ₁ * ρ₂))_(M - i)) := by
    intro i hi
    have hiM : i ≤ M := by have := mem_range.mp hi; lia
    have haq' : bInv (a * q)_(2 * r + i) = bInv (a * q)_(2 * r) * bInv (a * q * q ^ (2 * r))_i
        := by rw [qPochhammer_add' (2 * r) i]; exact (haqpoc (2 * r)).bInv_mul (hzk i)
    rw [(by lia : r + i + r = 2 * r + i), (by lia : N - (r + i) = M - i),
      qPochhammer_add' r i, qPochhammer_add' r i, pow_add, haq', hG_def]
    have := qPochhammer_split_of_le (a := q) (q := q) hiM
    have := qPochhammer_split_of_le' (a := q) (q := q) hiM
    have := qPochhammer_split_of_le (a := a * q * q ^ (2 * r)) (q := q) hiM
    have hpow : q * q ^ (M - i) = q ^ (M + 1 - i) := by rw [← pow_succ']; congr 1; lia
    grind [(hqpoc i).mul_bInv_cancel, (hqpoc (M - i)).mul_bInv_cancel, (hzk i).mul_bInv_cancel,
      (haqρ₁ N).mul_bInv_cancel, (haqρ₂ N).mul_bInv_cancel, (haqpoc (2 * r)).mul_bInv_cancel]
  rw [sum_congr rfl h_per]
  -- Step 2: Factor out common terms, apply PS, show equals G * target
  simp_rw [mul_assoc ((ρ₁)_(r)), mul_assoc ((ρ₂)_(r)), mul_assoc ((a * q * bInv (ρ₁ * ρ₂)) ^ r)]
  repeat rw [← mul_sum]
  have := qPochhammer_split_of_add_eq (a := a * q) (q := q) (show 2 * r + M = N + r by lia)
  have := qPochhammer_split_of_add_eq (a := a * q * bInv ρ₁) (q := q) (show r + M = N by lia)
  have := qPochhammer_split_of_add_eq (a := a * q * bInv ρ₂) (q := q) (show r + M = N by lia)
  grind [(haqρ₁ r).mul_bInv_cancel, (haqρ₂ r).mul_bInv_cancel, (hqpoc M).mul_bInv_cancel,
    ((haqpoc (2 * r)).mul (hzk M)).mul_bInv_cancel]

/-- Auxiliary lemma for `qBaileyLemma_limit`, obtained by applying `qBinomial_qPochhammer_sum`
with `z = aq^{2r+1}`. -/
theorem qBaileyLemma_limit_aux {n r : ℕ}
    (hq : ∀ i, IsUnit (q)_i) (haq : ∀ i, IsUnit (a * q)_i) :
    ∑ i ∈ range (n + 1), a ^ i * q ^ (i ^ 2 + 2 * r * i) *
      bInv (q)_i * bInv (q)_(n - i) * bInv (a * q)_(2 * r + i) =
        bInv (q)_n * bInv (a * q)_(n + 2 * r) := by
  set z := a * q * q ^ (2 * r) with hz_def
  have hGu : IsUnit ((q)_n * (a * q)_(n + 2 * r)) := (hq n).mul (haq (n + 2 * r))
  apply hGu.mul_left_cancel
  have hRHS : (q)_n * (a * q)_(n + 2 * r) * (bInv (q)_n * bInv (a * q)_(n + 2 * r)) = 1 := by
    grind [hq n, haq (n + 2 * r)]
  rw [hRHS, mul_sum]
  have h_per : ∀ i ∈ range (n + 1),
      (q)_n * (a * q)_(n + 2 * r) * (a ^ i * q ^ (i ^ 2 + 2 * r * i) *
        bInv (q)_i * bInv (q)_(n - i) * bInv (a * q)_(2 * r + i)) =
          z ^ i * q ^ (i * (i - 1)) * qChoose q n i * (z * q ^ i)_(n - i) := by
    intro i hi
    have hiN : i ≤ n := by have := mem_range.mp hi; omega
    have : (a * q)_(n + 2 * r) = (a * q)_(2 * r + i) * (z * q ^ i)_(n - i) := by
      have : a * q * q ^ (2 * r + i) = z * q ^ i := by rw [hz_def, pow_add]; ring
      rw [show n + 2 * r = (2 * r + i) + (n - i) by omega, qPochhammer_add', this]
    have := qChoose_eq_qPochhammer_div_qPochhammer_div_qPochhammer hiN (hq i) (hq (n - i))
    have : a ^ i * q ^ (i ^ 2 + 2 * r * i) = z ^ i * q ^ (i * (i - 1)) := by
      simp only [hz_def, mul_pow, ← pow_mul]
      rcases i with _ | i <;> simp; ring
    grind [haq (2 * r + i)]
  rw [sum_congr rfl h_per, qBinomial_qPochhammer_sum n z]

/-- **Limiting Bailey lemma** (`ρ₁, ρ₂ → ∞` case):
If `(α, β)` is a Bailey pair relative to `a`, then `(α', β')` defined by
`α_n' = a^n q^{n^2} α_n` and `β_n' = ∑_{j=0}^n a^j q^{j^2} β_j / (q)_{n-j}`
is also a Bailey pair relative to `a`. The proof uses `qBinomial_qPochhammer_sum`
in place of `qPfaffSaalschutz`. -/
theorem qBaileyLemma_limit (α β α' β' : ℕ → R) (h : IsBaileyPair a q α β)
    (hqpoc : ∀ k, IsUnit (q)_k) (haqpoc : ∀ k, IsUnit (a * q)_k)
    (hα' : ∀ n, α' n = a ^ n * q ^ (n ^ 2) * α n)
    (hβ' : ∀ n, β' n = ∑ j ∈ range (n + 1), a ^ j * q ^ (j ^ 2) * bInv (q)_(n - j) * β j) :
    IsBaileyPair a q α' β' := by
  intro N
  rw [IsBaileyPair] at h
  have hα_comm (r : ℕ) : a ^ r * q ^ (r ^ 2) * α r = α r * (a ^ r * q ^ (r ^ 2)) := by ring
  simp_rw [hβ' N, hα', hα_comm, h, mul_sum]
  rw [sum_triangle_reindex]
  apply sum_congr rfl
  intro r hr
  have hrN : r ≤ N := by have := mem_range.mp hr; lia
  simp only [Nat.add_sub_cancel_left, mul_assoc (α r), mul_left_comm _ (α r)]
  rw [← mul_sum]
  congr 1
  -- Inner sum identity: factor out `a^r * q^{r²}` and apply qBaileyLemma_limit_aux
  have h_per : ∀ i ∈ range (N - r + 1),
      a ^ (r + i) * q ^ ((r + i) ^ 2) * bInv (q)_(N - (r + i)) *
        (bInv (q)_i * bInv (a * q)_(r + i + r)) =
      a ^ r * q ^ (r ^ 2) * (a ^ i * q ^ (i ^ 2 + 2 * r * i) *
        bInv (q)_i * bInv (q)_(N - r - i) * bInv (a * q)_(2 * r + i)) := by
    intro i hi
    have : (r + i) ^ 2 = r ^ 2 + (i ^ 2 + 2 * r * i) := by ring
    grind
  have h_inner := qBaileyLemma_limit_aux (a := a) (q := q) (r := r) (n := N - r) hqpoc haqpoc
  simp_rw [sum_congr rfl h_per, ← mul_sum, h_inner, show N - r + 2 * r = N + r by lia]
  ring

/-- Reindex a `tsum` over `ℕ` restricted by `n ≤ r` to a shifted `tsum`. -/
theorem tsum_ite_le_eq_tsum_comp_add {G : Type*} [AddCommMonoid G] [TopologicalSpace G]
    {g : ℕ → G} {n : ℕ} :
    (∑' r, if n ≤ r then g r else 0) = ∑' k, g (k + n) := by
  have hinj : Function.Injective (· + n) := fun a b h ↦ Nat.add_right_cancel h
  have hsup : Function.support (fun r ↦ if n ≤ r then g r else 0) ⊆ Set.range (· + n) := by
    intro r hr
    rw [Function.mem_support] at hr
    exact ⟨r - n, Nat.sub_add_cancel (by_contra fun hc ↦ hr (if_neg hc))⟩
  rw [← Function.Injective.tsum_eq hinj hsup]
  exact tsum_congr fun k ↦ if_pos (Nat.le_add_left n k)

/-- Key identity from the infinite q-binomial theorem with `z = a·q^{2n+1}`:
`a^n q^{n²} / (aq)_∞ = ∑_{r≥n} a^r q^{r²} / ((q)_{r-n} (aq)_{r+n})`.
This is the `γ`–`δ` identity used in the limiting Bailey lemma. -/
theorem qBailey_gammaIdentity [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
    [T2Space R] [StrongNonarchimedeanRing R]
    (hq : IsTopologicallyNilpotent q) (haq : IsTopologicallyNilpotent (a * q)) (n : ℕ) :
    HasSum (fun r ↦ if n ≤ r then (a ^ r * q ^ (r ^ 2)) * bInv (q)_(r - n) *
      bInv (a * q)_(r + n) else 0) (a ^ n * q ^ (n ^ 2) * bInv (a * q)_∞) := by
  have haqu : IsUnit (a * q)_∞ := isUnit_qPochhammerInf haq hq
  have hshift := fun m ↦
    bInv_qPochhammer_eq_qPochhammerInf_shift_mul_bInv_qPochhammerInf (n := m) (q := q) hq haqu
  set z := a * q ^ (2 * n + 1) with hz_def
  have hz : IsTopologicallyNilpotent z := by
    rw [(by ring : z = (a * q) * q ^ (2 * n))]
    rcases n with _ | n <;> first | simpa using haq | exact haq.mul (hq.pow (by lia))
  have hkey := qBinomial_qPochhammer_tsum (z := z) (q := q) (hq := hq)
  have hsumm : Summable fun k ↦ z ^ k * q ^ (k * (k - 1)) * bInv (q)_k * (z * q ^ k)_∞ := by
    rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero, Nat.cofinite_eq_atTop]
    have h3 : Tendsto (fun k ↦ z ^ k * q ^ (k * (k - 1))) atTop (nhds 0) := by
      have := hq.comp (tendsto_atTop_atTop.mpr fun N ↦ ⟨N + 2, fun k hk ↦
        (show N ≤ k - 1 by omega).trans (Nat.le_mul_of_pos_left _ (show 0 < k by omega))⟩)
      simpa using Tendsto.mul (f := fun k ↦ z ^ k) hz this
    simpa using (h3.mul (tendsto_bInv_qPochhammer_bInv_qPochhammerInf hq)).mul
      (tendsto_qPochhammerInf_shift_one (a := z) (q := q) hq)
  -- Reindex `HasSum f (a^n q^{n²} bInv((aq)_∞))` via `k ↦ k + n` into the if-then-else form.
  have hinj : Function.Injective fun k : ℕ ↦ k + n := fun _ _ h ↦ Nat.add_right_cancel h
  rw [← hinj.hasSum_iff fun x hx ↦ if_neg fun h ↦ hx ⟨x - n, Nat.sub_add_cancel h⟩]
  have hscaled := (hkey ▸ hsumm.hasSum).mul_left (a ^ n * q ^ (n ^ 2) * bInv (a * q)_∞)
  rw [mul_one] at hscaled
  refine hscaled.congr_fun fun k ↦ ?_
  simp only [Function.comp_apply, if_pos (Nat.le_add_left n k), Nat.add_sub_cancel]
  rw [hz_def, hshift (k + n + n)]
  ring_nf
  congr 2
  rw [← pow_add]
  congr 1
  rcases k with _ | k <;> simp; ring_nf

/-- **Infinite limiting Bailey lemma (`HasSum` version)**: if `(α, β)` is a Bailey pair
relative to `a` and `a^r q^{r²} α_r → 0`, then the α-sum converges to some `L` and
the β-sum converges to `bInv((aq)_∞) * L`.

This is obtained by applying `bailey_lemma_basic` with `δ_n = a^n q^{n^2}` and
`γ_n = a^n q^{n^2} / (aq)_∞`, where the `γ`-identity is `qBailey_gammaIdentity`. -/
theorem qBaileyLemma_limit'_hasSum [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
    [T2Space R] [StrongNonarchimedeanRing R]
    (α β : ℕ → R) (h : IsBaileyPair a q α β)
    (hq : IsTopologicallyNilpotent q) (haq : IsTopologicallyNilpotent (a * q))
    (hα : Tendsto (fun r ↦ a ^ r * q ^ (r ^ 2) * α r) atTop (nhds 0)) :
    ∃ L, HasSum (fun r ↦ a ^ r * q ^ (r ^ 2) * α r) L ∧
      HasSum (fun j ↦ a ^ j * q ^ (j ^ 2) * β j) (bInv (a * q)_∞ * L) := by
  have haqu : IsUnit (a * q)_∞ := isUnit_qPochhammerInf haq hq
  have hαs : Summable fun r ↦ a ^ r * q ^ (r ^ 2) * α r := summable_of_tendsto_atTop_zero hα
  have hγ : ∀ n, Summable fun r ↦ if n ≤ r then (a ^ r * q ^ (r ^ 2)) * bInv (q)_(r - n) *
      bInv (a * q)_(r + n) else 0 := fun n ↦ (qBailey_gammaIdentity a q hq haq n).summable
  have hswap : Summable (fun (n, r) ↦
      if n ≤ r then α n * (a ^ r * q ^ (r ^ 2)) * bInv (q)_(r - n) *
        bInv (a * q)_(r + n) else 0) := by
    -- Factor summand as `(a^n q^{n²} α_n) * G(n, r)` where the first factor tends to `0`
    -- (by `hα`) and `G(n, r) = (aq)^{r-n} * q^{(r-n)(r+n-1)} * bInv((q)_{r-n}) * bInv((aq)_{r+n})`
    -- is bounded.
    apply summable_of_tendsto_cofinite_zero
    have hbq := (tendsto_bInv_qPochhammer_bInv_qPochhammerInf hq).boundedRange
    have hbaq := (tendsto_bInv_qPochhammer_bInv_qPochhammerInf' hq haqu).boundedRange
    have hRest : (fun (n, r) ↦ q ^ ((r - n) * (r + n - 1)) *
        bInv (q)_(r - n) * bInv (a * q)_(r + n)).BoundedRange :=
      (hq.boundedRange.comp.mul hbq.comp).mul hbaq.comp
    set G : ℕ × ℕ → R := fun (n, r) ↦ (a * q) ^ (r - n) *
        (q ^ ((r - n) * (r + n - 1)) * bInv (q)_(r - n) * bInv (a * q)_(r + n)) with hGdef
    have hG : G.BoundedRange := haq.boundedRange.comp.mul hRest
    set h : ℕ → R := fun n ↦ a ^ n * q ^ (n ^ 2) * α n with hhdef
    refine (tendsto_cofinite_zero_triangular (f := fun n r ↦ h n * G (n, r))
      (fun n ↦ ?_) fun U hU ↦ ?_).congr fun ⟨n, r⟩ ↦ ?_
    · -- Row limit: `h(n) * G(n, r) → 0` as `r → ∞`, since `(aq)^{r-n} → 0`.
      have h1 : Tendsto (fun r : ℕ ↦ (a * q) ^ (r - n)) atTop (𝓝 0) :=
        haq.comp (tendsto_atTop_atTop.mpr fun N ↦ ⟨N + n, fun r _ ↦ by omega⟩)
      simpa using (h1.mul_topologicallyBounded (hRest.comp (g := (n, ·)))).const_mul (h n)
    · -- Uniform tail: since `G` is bounded and `h → 0`, eventually `h(n) * G(n, r) ∈ U`.
      obtain ⟨V, hVn, _, hVU⟩ := hG.exists_subset_mul_mem hU
      filter_upwards [hα.eventually hVn] with n hhn r _
      rw [mul_comm]
      exact hVU _ ⟨(n, r), rfl⟩ _ hhn
    · -- Arithmetic: `α_n * a^r q^{r²} = h(n) * (aq)^{r-n} * q^{(r-n)(r+n-1)}`.
      simp only [Function.uncurry_apply_pair, hhdef, hGdef]
      split_ifs with hnr
      · have : a ^ r = a ^ n * a ^ (r - n) := by rw [← pow_add]; congr 1; omega
        have : q ^ r ^ 2 = q ^ n ^ 2 * q ^ (r - n) * q ^ ((r - n) * (r + n - 1)) := by
          repeat rw [← pow_add]
          congr 1
          rcases Nat.eq_zero_or_pos (r + n) with h | h
          · grind
          · zify [hnr, show 1 ≤ r + n from h]; ring
        grind [mul_pow]
      · rfl
  -- Derive `HasSum` for α side
  set L := ∑' r, a ^ r * q ^ (r ^ 2) * α r
  -- Derive `Summable` for β side from the double-sum swap
  have hβsumm : Summable (fun r ↦ a ^ r * q ^ (r ^ 2) * β r) := by
    set F : ℕ × ℕ → R := fun (n, r) ↦
      if n ≤ r then α n * (a ^ r * q ^ (r ^ 2)) * bInv (q)_(r - n) * bInv (a * q)_(r + n) else 0
    -- Swap product order: HasSum over (r, n) instead of (n, r)
    have hpair' : HasSum (fun p : ℕ × ℕ ↦ F p.swap) (∑' p : ℕ × ℕ, F p) := by
      simpa [Function.comp_def] using (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hswap.hasSum
    refine (hpair'.prod_fiberwise fun r ↦ ?_).summable
    -- Column sum: ∑_n F(n,r) = a^r q^{r^2} β_r
    have hfin : ∀ n ∉ range (r + 1), F (n, r) = 0 := fun n hn ↦ by grind
    have hsum : (∑ n ∈ range (r + 1), F (n, r)) = a ^ r * q ^ (r ^ 2) * β r := by
      rw [h r, mul_sum]
      exact sum_congr rfl fun n hn ↦ by
        simp [F, show n ≤ r by rw [mem_range] at hn; omega, mul_assoc, mul_left_comm, mul_comm]
    exact hsum ▸ hasSum_sum_of_ne_finset_zero hfin
  -- Apply `bailey_lemma_basic`
  have key := bailey_lemma_basic (fun n ↦ bInv (q)_n) (fun n ↦ bInv (a * q)_n)
    α β (fun n ↦ a ^ n * q ^ (n ^ 2) * bInv (a * q)_∞) (fun n ↦ a ^ n * q ^ (n ^ 2))
    hγ hswap h fun n ↦ (qBailey_gammaIdentity a q hq haq n).tsum_eq.symm
  have key' : bInv (a * q)_∞ * L = ∑' j, a ^ j * q ^ (j ^ 2) * β j := by
    rw [← hαs.tsum_mul_left]
    exact (tsum_congr fun n ↦ by ring).symm.trans (key.trans (tsum_congr fun n ↦ by ring))
  exact ⟨L, hαs.hasSum, key' ▸ hβsumm.hasSum⟩

/-- **Infinite limiting Bailey lemma**: if `(α, β)` is a Bailey pair relative to `a`, then
`∑ a^j q^{j^2} β_j = (aq)_∞⁻¹ ∑ a^r q^{r^2} α_r`.
-/
theorem qBaileyLemma_limit' [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
    [T2Space R] [StrongNonarchimedeanRing R]
    (α β : ℕ → R) (h : IsBaileyPair a q α β)
    (hq : IsTopologicallyNilpotent q) (haq : IsTopologicallyNilpotent (a * q))
    (hα : Tendsto (fun r ↦ a ^ r * q ^ (r ^ 2) * α r) atTop (nhds 0)) :
    ∑' j, a ^ j * q ^ (j ^ 2) * β j = bInv (a * q)_∞ * ∑' r, a ^ r * q ^ (r ^ 2) * α r := by
  obtain ⟨L, hL, hβL⟩ := qBaileyLemma_limit'_hasSum a q α β h hq haq hα
  simpa [hL.tsum_eq] using hβL.tsum_eq

end Bailey
