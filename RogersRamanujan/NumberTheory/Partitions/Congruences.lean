module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.ZMod.Basic

public import RogersRamanujan.NumberTheory.Partitions.PR
public import RogersRamanujan.NumberTheory.QTheory.Defs
public import RogersRamanujan.NumberTheory.QTheory.Pentagonal
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

end PowerSeries

namespace Nat.Partition

/-- **Ramanujan's congruence mod 5**: `p(5n + 4) ≡ 0 (mod 5)` for every `n`, phrased as the
vanishing, modulo `5`, of the power series `∑ p(5n + 4) qⁿ` obtained by dissecting
`powerSeriesCard` along the residue class `4` mod `5` and reindexing. -/
theorem dissectShift_five_four_map_zmod_five :
    PowerSeries.map (Int.castRingHom (ZMod 5)) (powerSeriesCard.dissectShift 5 4) = 0 := by
  sorry

/-- **Ramanujan's congruence mod 5**, as a divisibility statement: `5 ∣ p(5n + 4)` for every `n`. -/
theorem five_dvd_card_five_mul_add_four (n : ℕ) :
    5 ∣ Partition.card (5 * n + 4) := by
  have h := congrArg (PowerSeries.coeff n) dissectShift_five_four_map_zmod_five
  simp only [PowerSeries.coeff_map, coeff_dissectShift, coeff_powerSeriesCard, map_zero] at h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h

/-- **Ramanujan's congruence mod 7**: `p(7n + 5) ≡ 0 (mod 7)` for every `n`, phrased as the
vanishing, modulo `7`, of the power series `∑ p(7n + 5) qⁿ`. -/
theorem dissectShift_seven_five_map_zmod_seven :
    PowerSeries.map (Int.castRingHom (ZMod 7)) (powerSeriesCard.dissectShift 7 5) = 0 := by
  sorry

/-- **Ramanujan's congruence mod 7**, as a divisibility statement: `7 ∣ p(7n + 5)` for every `n`. -/
theorem seven_dvd_card_seven_mul_add_five (n : ℕ) :
    7 ∣ Partition.card (7 * n + 5) := by
  have h := congrArg (PowerSeries.coeff n) dissectShift_seven_five_map_zmod_seven
  simp only [PowerSeries.coeff_map, coeff_dissectShift, coeff_powerSeriesCard, map_zero] at h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h

/-- **Ramanujan's congruence mod 11**: `p(11n + 6) ≡ 0 (mod 11)` for every `n`, phrased as the
vanishing, modulo `11`, of the power series `∑ p(11n + 6) qⁿ`. -/
theorem dissectShift_eleven_six_map_zmod_eleven :
    PowerSeries.map (Int.castRingHom (ZMod 11)) (powerSeriesCard.dissectShift 11 6) = 0 := by
  sorry

/-- **Ramanujan's congruence mod 11**, as a divisibility statement: `11 ∣ p(11n + 6)` for
every `n`. -/
theorem eleven_dvd_card_eleven_mul_add_six (n : ℕ) :
    11 ∣ Partition.card (11 * n + 6) := by
  have h := congrArg (PowerSeries.coeff n) dissectShift_eleven_six_map_zmod_eleven
  simp only [PowerSeries.coeff_map, coeff_dissectShift, coeff_powerSeriesCard, map_zero] at h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h

end Nat.Partition
