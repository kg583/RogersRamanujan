module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.MvPowerSeries.LinearTopology

public import RogersRamanujan.NumberTheory.Partitions.PR
public import RogersRamanujan.NumberTheory.QTheory.Defs
public import RogersRamanujan.NumberTheory.QTheory.Pentagonal
import RogersRamanujan.NumberTheory.QTheory.StrongNonarchimedean
import RogersRamanujan.NumberTheory.QTheory.BinomialTheorem
import RogersRamanujan.NumberTheory.QTheory.JacobiTriangular
public import RogersRamanujan.RingTheory.PowerSeries.DiscreteTopology
public import RogersRamanujan.RingTheory.PowerSeries.Evaluation

/-! # Dissection of power series and Ramanujan's partition congruences

This file develops the `l`-dissection of a power series (splitting it into pieces supported on a
single residue class mod `l`), and uses it to state Ramanujan's congruences
`p(5n + 4) ≡ 0 [MOD 5]`, `p(7n + 5) ≡ 0 [MOD 7]`, and `p(11n + 6) ≡ 0 [MOD 11]` for the
partition function.

## Main definitions

* `PowerSeries.dissect`: the piece of a power series supported on one residue class mod `l`
* `PowerSeries.dissectShift`: that piece, reindexed as a power series in its own right
* `Nat.Partition.powerSeriesCard`: the power series `∑ p(n) qⁿ`

## Main results

* `PowerSeries.sum_dissect`: a power series is the sum of its `l` dissection pieces
* `Nat.Partition.dissectShift_five_four_map_zmod_five`,
  `Nat.Partition.dissectShift_seven_five_map_zmod_seven`,
  `Nat.Partition.dissectShift_eleven_six_map_zmod_eleven`:
  Ramanujan's congruences mod `5`, `7`, `11`, stated as the vanishing of a dissected power series
* `Nat.Partition.five_dvd_card_five_mul_add_four`,
  `Nat.Partition.seven_dvd_card_seven_mul_add_five`,
  `Nat.Partition.eleven_dvd_card_eleven_mul_add_six`:
  the same congruences as elementary divisibility statements, derived from the above
-/

@[expose] public section

open QTheory PowerSeries DiscreteTopology

namespace PowerSeries

/-- The piece of `f` supported on the residue class `r` mod `l`: the power series obtained from
`f` by zeroing out every coefficient at an index `n` with `n % l ≠ r`. -/
noncomputable def dissect {R : Type*} [Semiring R] (f : R⟦X⟧) (l r : ℕ) : R⟦X⟧ :=
  mk fun n ↦ if n % l = r then f.coeff n else 0

@[simp]
theorem coeff_dissect {R : Type*} [Semiring R] (f : R⟦X⟧) (l r n : ℕ) :
    (f.dissect l r).coeff n = if n % l = r then f.coeff n else 0 :=
  coeff_mk _ _

theorem coeff_dissect_of_mod {R : Type*} [Semiring R] (f : R⟦X⟧) {l r n : ℕ} (h : n % l = r) :
    (f.dissect l r).coeff n = f.coeff n := by simp [h]

theorem coeff_dissect_of_not_mod {R : Type*} [Semiring R] (f : R⟦X⟧) {l r n : ℕ} (h : n % l ≠ r) :
    (f.dissect l r).coeff n = 0 := by simp [h]

/-- A power series is the sum of its `l` dissection pieces, one for each residue mod `l`. -/
theorem sum_dissect {R : Type*} [Semiring R] (f : R⟦X⟧) {l : ℕ} (hl : 0 < l) :
    ∑ r ∈ Finset.range l, f.dissect l r = f := by
  ext n
  rw [map_sum, Finset.sum_eq_single (n % l)]
  · exact coeff_dissect_of_mod f rfl
  · exact fun r _ hr ↦ coeff_dissect_of_not_mod f (Ne.symm hr)
  · exact fun h ↦ absurd (Finset.mem_range.mpr (Nat.mod_lt n hl)) h

/-- `f.dissect l r` reindexed along the residue class `n = l * m + r`: the power series in `m`
with coefficients `f.coeff (l * m + r)`. -/
noncomputable def dissectShift {R : Type*} [Semiring R] (f : R⟦X⟧) (l r : ℕ) : R⟦X⟧ :=
  mk fun m ↦ f.coeff (l * m + r)

@[simp]
theorem coeff_dissectShift {R : Type*} [Semiring R] (f : R⟦X⟧) (l r m : ℕ) :
    (f.dissectShift l r).coeff m = f.coeff (l * m + r) :=
  coeff_mk _ _

/-- Evaluating the `r`-mod-`l` dissection piece of `F` at a topologically nilpotent `q` is the
sum of `F`'s coefficients along the residue class `r`, each paired with the matching power of
`q`. -/
theorem hasSum_intEval_dissect {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [NonarchimedeanRing R] [CompleteSpace R] [T2Space R] (F : ℤ⟦X⟧) {l r : ℕ} (hr : r < l) {q : R}
    (hq : IsTopologicallyNilpotent q := by simp) :
    HasSum (fun m : ℕ ↦ (F.dissectShift l r).coeff m * q ^ (l * m + r))
      (intEval q (F.dissect l r)) := by
  have hinj : Function.Injective (fun m : ℕ ↦ l * m + r) := fun a b hab ↦ by
    simp only [add_left_inj] at hab
    exact Nat.eq_of_mul_eq_mul_left (by omega) hab
  have hzero : ∀ n : ℕ, n ∉ Set.range (fun m : ℕ ↦ l * m + r) →
      (F.dissect l r).coeff n * q ^ n = 0 := by
    intro n hn
    have hne : n % l ≠ r := fun h ↦
      hn ⟨n / l, show l * (n / l) + r = n from h ▸ Nat.div_add_mod n l⟩
    simp [coeff_dissect_of_not_mod F hne]
  simpa [Function.comp_def, Nat.mod_eq_of_lt hr]
    using (hinj.hasSum_iff hzero).mpr (hasSum_intEval hq (F.dissect l r))

@[simp]
theorem coeff_mul_eq_zero_of_forall {R : Type*} [CommSemiring R] (f g : R⟦X⟧) (m : ℕ)
    (h : ∀ i j, i + j = m → f.coeff i = 0 ∨ g.coeff j = 0) : (f * g).coeff m = 0 := by
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  rcases h p.1 p.2 hp with hh | hh <;> simp [hh]

end PowerSeries

private lemma isNilpotent_pow_X_p (p : ℕ) (hp : Nat.Prime p) :
    IsTopologicallyNilpotent (X ^ p : (ZMod p)⟦X⟧) := by
  simp only [isTopologicallyNilpotent_iff_isNilpotent_constantCoeff, map_pow, constantCoeff_X]
  rw [zero_pow]
  · simp only [IsNilpotent.zero]
  exact Nat.Prime.ne_zero hp

theorem qPochhammerInf_zmod_p_self_pow_p_zmod_p (p : ℕ) (hp : Nat.Prime p) :
    ((X; X)_∞ : (ZMod p)⟦X⟧) ^ p = (X ^ p; X ^ p)_∞ := by
  have hsub : ∀ Y : (ZMod p)⟦X⟧, (1 - Y) ^ p = 1 - Y ^ p := fun Y => by
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : CharP (ZMod p)⟦X⟧ p := charP_of_injective_ringHom PowerSeries.C_injective p
    rw [sub_pow_char, one_pow]
  have hEz0 := hasProd_qPochhammerInf_of_isTopologicallyNilpotent (a := (X : (ZMod p)⟦X⟧)) (q := X)
    isTopologicallyNilpotent_X isTopologicallyNilpotent_X
  have hEz : HasProd (fun n : ℕ => 1 - (X : (ZMod p)⟦X⟧) ^ (n + 1)) ((X; X)_∞) :=
    hEz0.congr_fun fun n => by ring
  have hEzp : HasProd (fun n : ℕ => 1 - (X : (ZMod p)⟦X⟧) ^ (p * n + p)) ((X; X)_∞ ^ p) := by
    refine (hEz.map (powMonoidHom p) (continuous_pow p)).congr_fun fun n => ?_
    simp only [Function.comp_apply, powMonoidHom_apply, hsub]
    ring
  have hEp0 := hasProd_qPochhammerInf_of_isTopologicallyNilpotent (a := (X ^ p : (ZMod p)⟦X⟧))
    (q := X ^ p) (isNilpotent_pow_X_p p hp) (isNilpotent_pow_X_p p hp)
  exact hEzp.unique (hEp0.congr_fun fun n => by ring)

theorem isUnit_qPochhammerInf_X_zmod (l : ℕ) :
    IsUnit ((X; X)_∞ : (ZMod l)⟦X⟧) := by
  have hcont : Continuous (map (Int.castRingHom (ZMod l)) : ℤ⟦X⟧ →+* (ZMod l)⟦X⟧) := by fun_prop
  have := (isUnit_qPochhammerInf (a := (X : ℤ⟦X⟧)) (q := X)).map (map (Int.castRingHom (ZMod l)))
  rwa [map_qPochhammerInf_of_isTopologicallyNilpotent (map (Int.castRingHom (ZMod l))) hcont
    isTopologicallyNilpotent_X isTopologicallyNilpotent_X, map_X] at this

namespace Nat.Partition

theorem map_powerSeriesCard_zmod (l : ℕ) :
    PowerSeries.map (Int.castRingHom (ZMod l)) powerSeriesCard
      = bInv ((X; X)_∞ : (ZMod l)⟦X⟧) := by
  have h1 : HasSum (fun n : ℕ => Partition.card n • (X : (ZMod l)⟦X⟧) ^ n)
      (bInv ((X; X)_∞ : (ZMod l)⟦X⟧)) := hasSum_card
  have h2 : HasSum (fun n : ℕ => C ((Partition.card n : ℤ) : ZMod l) * X ^ n)
      (PowerSeries.map (Int.castRingHom (ZMod l)) powerSeriesCard) := by
    have hc := hasSum_C_mul_X_pow (fun n => ((Partition.card n : ℤ) : ZMod l))
    convert hc using 1
    ext n
    simp [PowerSeries.coeff_map]
  refine h2.unique (h1.congr_fun fun n => ?_)
  rw [zsmul_eq_mul, ← map_intCast (C : ZMod l →+* (ZMod l)⟦X⟧)]

private theorem coeff_bInv_qPochhammerInf_zmod_p_pow_p (p : ℕ) (hp : Nat.Prime p) (m : ℕ)
    (hm : ¬ (p ∣ m)) : (bInv ((X ^ p; X ^ p)_∞ : (ZMod p)⟦X⟧)).coeff m = 0 := by
  have hfun : (fun n : ℕ => Partition.card n • (X ^ p : (ZMod p)⟦X⟧) ^ n)
      = fun n => C ((Partition.card n : ℤ) : ZMod p) * (X ^ p) ^ n := by
    funext n
    rw [zsmul_eq_mul, ← map_intCast (C : ZMod p →+* (ZMod p)⟦X⟧)]
  have hsum := hasSum_card (q := (X ^ p : (ZMod p)⟦X⟧)) (isNilpotent_pow_X_p p hp)
  rw [hfun] at hsum
  rw [← hsum.tsum_eq]
  rw [coeff_tsum_mul_pow_eq_succ (by
    simp only [map_pow, constantCoeff_X]
    rw [zero_pow]
    exact Nat.Prime.ne_zero hp)]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [coeff_C_mul, ← pow_mul, coeff_X_pow, if_neg (fun h => hm ⟨i, h⟩), mul_zero]

section Mod5

private lemma coeff_bInv_qPochhammerInf_zmod5_pow_ten (m : ℕ) (hm : ¬ (5 ∣ m)) :
    (bInv (((X; X)_∞ : (ZMod 5)⟦X⟧) ^ 10)).coeff m = 0 := by
  have hE5 := (qPochhammerInf_zmod_p_self_pow_p_zmod_p 5 Nat.prime_five).symm
  have hE5u : IsUnit ((X ^ 5; X ^ 5)_∞ : (ZMod 5)⟦X⟧) := by
    rw [hE5]; exact (isUnit_qPochhammerInf_X_zmod 5).pow 5
  have h10 : ((X; X)_∞ : (ZMod 5)⟦X⟧) ^ 10 = ((X ^ 5; X ^ 5)_∞) * ((X ^ 5; X ^ 5)_∞) := by
    rw [hE5]; ring
  rw [h10, hE5u.bInv_mul hE5u]
  refine coeff_mul_eq_zero_of_forall _ _ m fun i j hij => ?_
  by_cases hi : 5 ∣ i
  · exact Or.inr (coeff_bInv_qPochhammerInf_zmod_p_pow_p 5 Nat.prime_five j
    (fun hj => hm (hij ▸ Nat.dvd_add hi hj)))
  · exact Or.inl (coeff_bInv_qPochhammerInf_zmod_p_pow_p 5 Nat.prime_five i hi)

private lemma choose_two_succ_cast_zmod_five (n : ℕ) :
    ((n + 1).choose 2 : ZMod 5) = 3 * ((n : ZMod 5) + 1) * (n : ZMod 5) := by
  have hdvd : 2 ∣ (n + 1) * n := by
    rw [mul_comm]; exact (Nat.even_mul_succ_self n).two_dvd
  have h2 : 2 * (n + 1).choose 2 = (n + 1) * n := by
    rw [Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_div_cancel' hdvd]
  have h5 : (5 : ZMod 5) = 0 := by decide
  have hc := congrArg (Nat.cast : ℕ → ZMod 5) h2
  push_cast at hc
  linear_combination 3 * hc - ((n + 1).choose 2 : ZMod 5) * h5

private lemma coeff_qPochhammerInf_zmod_five_pow_three_eq_zero (m : ℕ)
    (h0 : (m : ZMod 5) ≠ 0) (h1 : (m : ZMod 5) ≠ 1) :
    (((X; X)_∞ : (ZMod 5)⟦X⟧) ^ 3).coeff m = 0 := by
  letI : TopologicalSpace (ZMod 5) := ⊥
  letI : DiscreteTopology (ZMod 5) := ⟨rfl⟩
  have hcoeff := (PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff (ZMod 5)).mp
    (hasSum_qPochhammerInf_self_pow_three_powerSeries (ZMod 5)) m
  have hz : HasSum (fun _ : ℕ => (0 : ZMod 5)) ((((X; X)_∞ : (ZMod 5)⟦X⟧) ^ 3).coeff m) := by
    refine hcoeff.congr_fun fun n => ?_
    rw [show ((-1 : (ZMod 5)⟦X⟧)) ^ n * C (2 * (n : ZMod 5) + 1)
        = C ((-1 : ZMod 5) ^ n * (2 * (n : ZMod 5) + 1)) by
          rw [map_mul, map_pow, map_neg, map_one], coeff_C_mul, coeff_X_pow]
    by_cases hk : m = (n + 1).choose 2
    · have hm5 : (m : ZMod 5) = 3 * ((n : ZMod 5) + 1) * (n : ZMod 5) := by
        rw [hk, choose_two_succ_cast_zmod_five]
      have hkey : 2 * (n : ZMod 5) + 1 = 0 :=
        (by decide : ∀ x : ZMod 5, 3 * (x + 1) * x ≠ 0 → 3 * (x + 1) * x ≠ 1 → 2 * x + 1 = 0)
          (n : ZMod 5) (hm5 ▸ h0) (hm5 ▸ h1)
      rw [if_pos hk, hkey]; ring
    · rw [if_neg hk, mul_zero]
  exact hz.unique hasSum_zero

private lemma zmod_five_eq_zero_or_one_of_ne {i : ℕ}
    (hi_ne : (((X; X)_∞ : (ZMod 5)⟦X⟧) ^ 3).coeff i ≠ 0) :
    (i : ZMod 5) = 0 ∨ (i : ZMod 5) = 1 := by
  rcases eq_or_ne (i : ZMod 5) 0 with h | h0
  · exact Or.inl h
  · rcases eq_or_ne (i : ZMod 5) 1 with h | h1
    · exact Or.inr h
    · exact absurd (coeff_qPochhammerInf_zmod_five_pow_three_eq_zero i h0 h1) hi_ne

private lemma coeff_qPochhammerInf_zmod5_pow_three_sq_eq_zero (m : ℕ)
    (hm : (m : ZMod 5) = 3 ∨ (m : ZMod 5) = 4) :
    (((X; X)_∞ : (ZMod 5)⟦X⟧) ^ 3 * ((X; X)_∞) ^ 3).coeff m = 0 := by
  refine coeff_mul_eq_zero_of_forall _ _ m fun i j hij => ?_
  rw [or_iff_not_imp_left]
  intro hi_ne
  have hsum : (i : ZMod 5) + (j : ZMod 5) = (m : ZMod 5) := by rw [← Nat.cast_add, hij]
  have hj := (by decide : ∀ a b c : ZMod 5, (c = 3 ∨ c = 4) → (a = 0 ∨ a = 1)
    → a + b = c → b ≠ 0 ∧ b ≠ 1)
    (i : ZMod 5) (j : ZMod 5) (m : ZMod 5) hm (zmod_five_eq_zero_or_one_of_ne hi_ne) hsum
  exact coeff_qPochhammerInf_zmod_five_pow_three_eq_zero j hj.1 hj.2

private lemma coeff_qPochhammerInf_zmod_five_pow_three_cube_eq_zero (m : ℕ)
    (hm : (m : ZMod 5) = 4) : ((((X; X)_∞ : (ZMod 5)⟦X⟧) ^ 3) ^ 3).coeff m = 0 := by
  rw [show (((X; X)_∞ : (ZMod 5)⟦X⟧) ^ 3) ^ 3
      = ((X; X)_∞) ^ 3 * (((X; X)_∞) ^ 3 * ((X; X)_∞) ^ 3) by ring]
  refine coeff_mul_eq_zero_of_forall _ _ m fun i j hij => ?_
  rw [or_iff_not_imp_left]
  intro hi_ne
  have hi := zmod_five_eq_zero_or_one_of_ne hi_ne
  have hsum : (i : ZMod 5) + (j : ZMod 5) = (m : ZMod 5) := by rw [← Nat.cast_add, hij]
  have hj := (by decide : ∀ a b c : ZMod 5, c = 4 → (a = 0 ∨ a = 1)
    → a + b = c → b = 3 ∨ b = 4) (i : ZMod 5) (j : ZMod 5) (m : ZMod 5) hm hi hsum
  exact coeff_qPochhammerInf_zmod5_pow_three_sq_eq_zero j hj

private lemma map_powerSeriesCard_zmod_five_eq :
    PowerSeries.map (Int.castRingHom (ZMod 5)) powerSeriesCard
      = (((X; X)_∞ : (ZMod 5)⟦X⟧) ^ 3) ^ 3 * bInv (((X; X)_∞ : (ZMod 5)⟦X⟧) ^ 10) := by
  have hEu := isUnit_qPochhammerInf_X_zmod 5
  have hFE : PowerSeries.map (Int.castRingHom (ZMod 5)) powerSeriesCard * ((X; X)_∞) = 1 := by
    rw [map_powerSeriesCard_zmod 5]; exact hEu.bInv_mul_cancel
  have hFE10 : PowerSeries.map (Int.castRingHom (ZMod 5)) powerSeriesCard * ((X; X)_∞ ^ 10)
      = ((X; X)_∞ ^ 3) ^ 3 := by
    rw [show PowerSeries.map (Int.castRingHom (ZMod 5)) powerSeriesCard * ((X; X)_∞ ^ 10)
        = (PowerSeries.map (Int.castRingHom (ZMod 5)) powerSeriesCard * (X; X)_∞) * (X; X)_∞ ^ 9 by
          ring, hFE, one_mul]
    ring
  exact (hEu.pow 10).eq_mul_bInv_of_mul_eq hFE10

private theorem coeff_map_powerSeriesCard_five_mul_add_four (n : ℕ) :
    (PowerSeries.map (Int.castRingHom (ZMod 5)) powerSeriesCard).coeff (5 * n + 4) = 0 := by
  rw [map_powerSeriesCard_zmod_five_eq]
  refine coeff_mul_eq_zero_of_forall _ _ (5 * n + 4) fun i j hij => ?_
  by_cases hj : 5 ∣ j
  · refine Or.inl (coeff_qPochhammerInf_zmod_five_pow_three_cube_eq_zero i ?_)
    have hj0 : (j : ZMod 5) = 0 := by rw [ZMod.natCast_eq_zero_iff]; exact hj
    have hsum : (i : ZMod 5) + (j : ZMod 5) = ((5 * n + 4 : ℕ) : ZMod 5) := by
      rw [← Nat.cast_add, hij]
    have h4 : ((5 * n + 4 : ℕ) : ZMod 5) = 4 := by
      push_cast
      rw [show (5 : ZMod 5) = 0 by decide, zero_mul, zero_add]
    rw [hj0, add_zero, h4] at hsum
    exact hsum
  · exact Or.inr (coeff_bInv_qPochhammerInf_zmod5_pow_ten j hj)

/-- **Ramanujan's congruence mod 5**: `p(5n + 4) ≡ 0 (mod 5)` for every `n`, phrased as the
vanishing, modulo `5`, of the power series `∑ p(5n + 4) qⁿ` obtained by dissecting
`powerSeriesCard` along the residue class `4` mod `5` and reindexing. -/
theorem dissectShift_five_four_map_zmod_five_powerSeries :
    PowerSeries.map (Int.castRingHom (ZMod 5)) (powerSeriesCard.dissectShift 5 4) = 0 := by
  ext n
  simpa [PowerSeries.coeff_map, coeff_dissectShift] using
    coeff_map_powerSeriesCard_five_mul_add_four n

/-- **Ramanujan's congruence mod 5**, as a divisibility statement: `5 ∣ p(5n + 4)` for every `n`. -/
theorem five_dvd_card_five_mul_add_four (n : ℕ) :
    5 ∣ Partition.card (5 * n + 4) := by
  have h := congrArg (PowerSeries.coeff n) dissectShift_five_four_map_zmod_five_powerSeries
  simp only [PowerSeries.coeff_map, coeff_dissectShift, coeff_powerSeriesCard, map_zero] at h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h

end Mod5

section Mod7

private lemma choose_two_succ_cast_zmod_seven (n : ℕ) :
    ((n + 1).choose 2 : ZMod 7) = 4 * ((n : ZMod 7) + 1) * (n : ZMod 7) := by
  have hdvd : 2 ∣ (n + 1) * n := by
    rw [mul_comm]; exact (Nat.even_mul_succ_self n).two_dvd
  have h2 : 2 * (n + 1).choose 2 = (n + 1) * n := by
    rw [Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_div_cancel' hdvd]
  have h7 : (7 : ZMod 7) = 0 := by decide
  have hc := congrArg (Nat.cast : ℕ → ZMod 7) h2
  push_cast at hc
  linear_combination 4 * hc - ((n + 1).choose 2 : ZMod 7) * h7

private lemma coeff_qPochhammerInf_zmod_seven_pow_three_eq_zero (m : ℕ)
    (h0 : (m : ZMod 7) ≠ 0) (h1 : (m : ZMod 7) ≠ 1) (h3 : (m : ZMod 7) ≠ 3) :
    (((X; X)_∞ : (ZMod 7)⟦X⟧) ^ 3).coeff m = 0 := by
  letI : TopologicalSpace (ZMod 7) := ⊥
  letI : DiscreteTopology (ZMod 7) := ⟨rfl⟩
  have hcoeff := (PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff (ZMod 7)).mp
    (hasSum_qPochhammerInf_self_pow_three_powerSeries (ZMod 7)) m
  have hz : HasSum (fun _ : ℕ => (0 : ZMod 7)) ((((X; X)_∞ : (ZMod 7)⟦X⟧) ^ 3).coeff m) := by
    refine hcoeff.congr_fun fun n => ?_
    rw [show ((-1 : (ZMod 7)⟦X⟧)) ^ n * C (2 * (n : ZMod 7) + 1)
        = C ((-1 : ZMod 7) ^ n * (2 * (n : ZMod 7) + 1)) by
          rw [map_mul, map_pow, map_neg, map_one], coeff_C_mul, coeff_X_pow]
    by_cases hk : m = (n + 1).choose 2
    · have hm7 : (m : ZMod 7) = 4 * ((n : ZMod 7) + 1) * (n : ZMod 7) := by
        rw [hk, choose_two_succ_cast_zmod_seven]
      have hkey : 2 * (n : ZMod 7) + 1 = 0 :=
        (by decide : ∀ x : ZMod 7, 4 * (x + 1) * x ≠ 0 → 4 * (x + 1) * x ≠ 1 →
          4 * (x + 1) * x ≠ 3 → 2 * x + 1 = 0)
          (n : ZMod 7) (hm7 ▸ h0) (hm7 ▸ h1) (hm7 ▸ h3)
      rw [if_pos hk, hkey]; ring
    · rw [if_neg hk, mul_zero]
  exact hz.unique hasSum_zero

private lemma zmod_seven_eq_zero_one_or_three_of_ne {i : ℕ}
    (hi_ne : (((X; X)_∞ : (ZMod 7)⟦X⟧) ^ 3).coeff i ≠ 0) :
    (i : ZMod 7) = 0 ∨ (i : ZMod 7) = 1 ∨ (i : ZMod 7) = 3 := by
  rcases eq_or_ne (i : ZMod 7) 0 with h | h0
  · exact Or.inl h
  · rcases eq_or_ne (i : ZMod 7) 1 with h | h1
    · exact Or.inr (Or.inl h)
    · rcases eq_or_ne (i : ZMod 7) 3 with h | h3
      · exact Or.inr (Or.inr h)
      · exact absurd (coeff_qPochhammerInf_zmod_seven_pow_three_eq_zero i h0 h1 h3) hi_ne

private lemma coeff_qPochhammerInf_zmod_seven_pow_three_sq_eq_zero
    (m : ℕ) (hm : (m : ZMod 7) = 5) : ((((X; X)_∞ : (ZMod 7)⟦X⟧) ^ 3) ^ 2).coeff m = 0 := by
  rw [show (((X; X)_∞ : (ZMod 7)⟦X⟧) ^ 3) ^ 2 = ((X; X)_∞) ^ 3 * ((X; X)_∞) ^ 3 by ring]
  refine coeff_mul_eq_zero_of_forall _ _ m fun i j hij => ?_
  rw [or_iff_not_imp_left]
  intro hi_ne
  have hsum : (i : ZMod 7) + (j : ZMod 7) = (m : ZMod 7) := by rw [← Nat.cast_add, hij]
  have hj := (by decide : ∀ a b c : ZMod 7, c = 5 → (a = 0 ∨ a = 1 ∨ a = 3) →
    a + b = c → b ≠ 0 ∧ b ≠ 1 ∧ b ≠ 3)
    (i : ZMod 7) (j : ZMod 7) (m : ZMod 7) hm (zmod_seven_eq_zero_one_or_three_of_ne hi_ne) hsum
  exact coeff_qPochhammerInf_zmod_seven_pow_three_eq_zero j hj.1 hj.2.1 hj.2.2

private lemma map_powerSeriesCard_zmod_seven_eq :
    PowerSeries.map (Int.castRingHom (ZMod 7)) powerSeriesCard
      = (((X; X)_∞ : (ZMod 7)⟦X⟧) ^ 3) ^ 2 * bInv (((X; X)_∞ : (ZMod 7)⟦X⟧) ^ 7) := by
  have hEu := isUnit_qPochhammerInf_X_zmod 7
  have hFE : PowerSeries.map (Int.castRingHom (ZMod 7)) powerSeriesCard * ((X; X)_∞) = 1 := by
    rw [map_powerSeriesCard_zmod 7]; exact hEu.bInv_mul_cancel
  have hFE7 : PowerSeries.map (Int.castRingHom (ZMod 7)) powerSeriesCard * ((X; X)_∞ ^ 7)
      = ((X; X)_∞ ^ 3) ^ 2 := by
    rw [show PowerSeries.map (Int.castRingHom (ZMod 7)) powerSeriesCard * ((X; X)_∞ ^ 7)
        = (PowerSeries.map (Int.castRingHom (ZMod 7)) powerSeriesCard * (X; X)_∞) * (X; X)_∞ ^ 6 by
          ring, hFE, one_mul]
    ring
  exact (hEu.pow 7).eq_mul_bInv_of_mul_eq hFE7

private theorem coeff_map_powerSeriesCard_seven_mul_add_five (n : ℕ) :
    (PowerSeries.map (Int.castRingHom (ZMod 7)) powerSeriesCard).coeff (7 * n + 5) = 0 := by
  rw [map_powerSeriesCard_zmod_seven_eq]
  refine coeff_mul_eq_zero_of_forall _ _ (7 * n + 5) fun i j hij => ?_
  by_cases hj : 7 ∣ j
  · refine Or.inl (coeff_qPochhammerInf_zmod_seven_pow_three_sq_eq_zero i ?_)
    have hj0 : (j : ZMod 7) = 0 := by rw [ZMod.natCast_eq_zero_iff]; exact hj
    have hsum : (i : ZMod 7) + (j : ZMod 7) = ((7 * n + 5 : ℕ) : ZMod 7) := by
      rw [← Nat.cast_add, hij]
    have h5 : ((7 * n + 5 : ℕ) : ZMod 7) = 5 := by
      push_cast
      rw [show (7 : ZMod 7) = 0 by decide, zero_mul, zero_add]
    rw [hj0, add_zero, h5] at hsum
    exact hsum
  · refine Or.inr ?_
    rw [qPochhammerInf_zmod_p_self_pow_p_zmod_p 7 Nat.prime_seven]
    exact coeff_bInv_qPochhammerInf_zmod_p_pow_p 7 Nat.prime_seven j hj

/-- **Ramanujan's congruence mod 7**: `p(7n + 5) ≡ 0 (mod 7)` for every `n`, phrased as the
vanishing, modulo `7`, of the power series `∑ p(7n + 5) qⁿ`. -/
theorem dissectShift_seven_five_map_zmod_seven_powerSeries :
    PowerSeries.map (Int.castRingHom (ZMod 7)) (powerSeriesCard.dissectShift 7 5) = 0 := by
  ext n
  simpa [PowerSeries.coeff_map, coeff_dissectShift] using
    coeff_map_powerSeriesCard_seven_mul_add_five n

/-- **Ramanujan's congruence mod 7**, as a divisibility statement: `7 ∣ p(7n + 5)` for every `n`. -/
theorem seven_dvd_card_seven_mul_add_five (n : ℕ) :
    7 ∣ Partition.card (7 * n + 5) := by
  have h := congrArg (PowerSeries.coeff n) dissectShift_seven_five_map_zmod_seven_powerSeries
  simp only [PowerSeries.coeff_map, coeff_dissectShift, coeff_powerSeriesCard, map_zero] at h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h

end Mod7

section Mod11

/-- **Ramanujan's congruence mod 11**: `p(11n + 6) ≡ 0 (mod 11)` for every `n`, phrased as the
vanishing, modulo `11`, of the power series `∑ p(11n + 6) qⁿ`. -/
theorem dissectShift_eleven_six_map_zmod_eleven_powerSeries :
    PowerSeries.map (Int.castRingHom (ZMod 11)) (powerSeriesCard.dissectShift 11 6) = 0 := by
  sorry

/-- **Ramanujan's congruence mod 11**, as a divisibility statement: `11 ∣ p(11n + 6)` for
every `n`. -/
theorem eleven_dvd_card_eleven_mul_add_six (n : ℕ) :
    11 ∣ Partition.card (11 * n + 6) := by
  have h := congrArg (PowerSeries.coeff n) dissectShift_eleven_six_map_zmod_eleven_powerSeries
  simp only [PowerSeries.coeff_map, coeff_dissectShift, coeff_powerSeriesCard, map_zero] at h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h

end Mod11

end Nat.Partition
