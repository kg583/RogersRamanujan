module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.ZMod.Basic

public import RogersRamanujan.NumberTheory.Partitions.PR
public import RogersRamanujan.NumberTheory.QTheory.Defs
import RogersRamanujan.NumberTheory.QTheory.JacobiTriangular
public import RogersRamanujan.NumberTheory.QTheory.ModP
public import RogersRamanujan.RingTheory.PowerSeries.Dissect

/-! # Ramanujan's partition congruences

## Main results

* `coeff_bInv_qPochhammerInf_pow_p_zmod_p`: `((X; X)_∞)^-p` is supported only on `0` mod `p`
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

namespace Nat

lemma choose_two_succ (n : ℕ) : 2 * (n + 1).choose 2 = (n + 1) * n := by
  have hdvd : 2 ∣ (n + 1) * n := by rw [mul_comm]; exact (Nat.even_mul_succ_self n).two_dvd
  rw [Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_div_cancel' hdvd]

namespace Partition

section Mod5

private lemma choose_two_succ_cast_zmod_five (n : ℕ) :
    ((n + 1).choose 2 : ZMod 5) = 3 * ((n : ZMod 5) + 1) * (n : ZMod 5) := by
  have h5 : (5 : ZMod 5) = 0 := by decide
  have hc := congrArg (Nat.cast : ℕ → ZMod 5) (Nat.choose_two_succ n)
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
    rw [show ((-1 : (ZMod 5)⟦X⟧)) ^ n * PowerSeries.C (2 * (n : ZMod 5) + 1)
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

theorem coeff_map_powerSeriesCard_five_mul_add_four (n : ℕ) :
    (PowerSeries.map (Int.castRingHom (ZMod 5)) powerSeriesCard).coeff (5 * n + 4) = 0 := by
  rw [map_powerSeriesCard_zmod_five_eq]
  refine coeff_mul_eq_zero_of_forall _ _ (5 * n + 4) fun i j hij => ?_
  by_cases hj : 5 ∣ j
  · refine Or.inl (coeff_qPochhammerInf_zmod_five_pow_three_cube_eq_zero i ?_)
    calc (i : ZMod 5) = (i : ZMod 5) + (j : ZMod 5) := by
          rw [(ZMod.natCast_eq_zero_iff j 5).mpr hj, add_zero]
      _ = ((5 * n + 4 : ℕ) : ZMod 5) := by rw [← Nat.cast_add, hij]
      _ = 4 := by grind
  · exact Or.inr (coeff_bInv_qPochhammerInf_zmod_p_sq 5 Nat.prime_five j hj)

/-- **Ramanujan's congruence mod 5**: `p(5n + 4) ≡ 0 (mod 5)` for every `n`, phrased as the
vanishing, modulo `5`, of the power series `∑ p(5n + 4) qⁿ` obtained by dissecting
`powerSeriesCard` along the residue class `4` mod `5` and reindexing. -/
theorem dissectShift_five_four_map_zmod_five_powerSeries :
    PowerSeries.map (Int.castRingHom (ZMod 5)) (powerSeriesCard.dissectShift 5 4) = 0 := by
  ext n
  simp only [PowerSeries.coeff_map, coeff_dissectShift]
  exact coeff_map_powerSeriesCard_five_mul_add_four n

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
  have h7 : (7 : ZMod 7) = 0 := by decide
  have hc := congrArg (Nat.cast : ℕ → ZMod 7) (Nat.choose_two_succ n)
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
    rw [show ((-1 : (ZMod 7)⟦X⟧)) ^ n * PowerSeries.C (2 * (n : ZMod 7) + 1)
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

theorem coeff_map_powerSeriesCard_seven_mul_add_five (n : ℕ) :
    (PowerSeries.map (Int.castRingHom (ZMod 7)) powerSeriesCard).coeff (7 * n + 5) = 0 := by
  rw [map_powerSeriesCard_zmod_seven_eq]
  refine coeff_mul_eq_zero_of_forall _ _ (7 * n + 5) fun i j hij => ?_
  by_cases hj : 7 ∣ j
  · refine Or.inl (coeff_qPochhammerInf_zmod_seven_pow_three_sq_eq_zero i ?_)
    calc (i : ZMod 7) = (i : ZMod 7) + (j : ZMod 7) := by
          rw [(ZMod.natCast_eq_zero_iff j 7).mpr hj, add_zero]
      _ = ((7 * n + 5 : ℕ) : ZMod 7) := by rw [← Nat.cast_add, hij]
      _ = 5 := by grind
  · refine Or.inr ?_
    rw [qPochhammerInf_zmod_p_self_pow_p 7 Nat.prime_seven]
    exact coeff_bInv_qPochhammerInf_pow_p_zmod_p 7 Nat.prime_seven j hj

/-- **Ramanujan's congruence mod 7**: `p(7n + 5) ≡ 0 (mod 7)` for every `n`, phrased as the
vanishing, modulo `7`, of the power series `∑ p(7n + 5) qⁿ`. -/
theorem dissectShift_seven_five_map_zmod_seven_powerSeries :
    PowerSeries.map (Int.castRingHom (ZMod 7)) (powerSeriesCard.dissectShift 7 5) = 0 := by
  ext n
  simp only [PowerSeries.coeff_map, coeff_dissectShift]
  exact coeff_map_powerSeriesCard_seven_mul_add_five n

/-- **Ramanujan's congruence mod 7**, as a divisibility statement: `7 ∣ p(7n + 5)` for every `n`. -/
theorem seven_dvd_card_seven_mul_add_five (n : ℕ) :
    7 ∣ Partition.card (7 * n + 5) := by
  have h := congrArg (PowerSeries.coeff n) dissectShift_seven_five_map_zmod_seven_powerSeries
  simp only [PowerSeries.coeff_map, coeff_dissectShift, coeff_powerSeriesCard, map_zero] at h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h

end Mod7

section Mod11

private lemma choose_two_succ_cast_zmod_eleven (n : ℕ) :
    ((n + 1).choose 2 : ZMod 11) = 6 * ((n : ZMod 11) + 1) * (n : ZMod 11) := by
  have h11 : (11 : ZMod 11) = 0 := by decide
  have hc := congrArg (Nat.cast : ℕ → ZMod 11) (Nat.choose_two_succ n)
  push_cast at hc
  linear_combination 6 * hc - ((n + 1).choose 2 : ZMod 11) * h11

/-- The cube `(X;X)_∞^3` over `ZMod 11` is supported on the residues `{0, 1, 3, 6, 10}` mod `11`:
its coefficient vanishes at any index whose residue is not one of these. -/
private lemma coeff_qPochhammerInf_zmod_eleven_pow_three_eq_zero (m : ℕ)
    (h0 : (m : ZMod 11) ≠ 0) (h1 : (m : ZMod 11) ≠ 1) (h3 : (m : ZMod 11) ≠ 3)
    (h6 : (m : ZMod 11) ≠ 6) (h10 : (m : ZMod 11) ≠ 10) :
    (((X; X)_∞ : (ZMod 11)⟦X⟧) ^ 3).coeff m = 0 := by
  letI : TopologicalSpace (ZMod 11) := ⊥
  letI : DiscreteTopology (ZMod 11) := ⟨rfl⟩
  have hcoeff := (PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff (ZMod 11)).mp
    (hasSum_qPochhammerInf_self_pow_three_powerSeries (ZMod 11)) m
  have hz : HasSum (fun _ : ℕ => (0 : ZMod 11)) ((((X; X)_∞ : (ZMod 11)⟦X⟧) ^ 3).coeff m) := by
    refine hcoeff.congr_fun fun n => ?_
    rw [show ((-1 : (ZMod 11)⟦X⟧)) ^ n * PowerSeries.C (2 * (n : ZMod 11) + 1)
        = C ((-1 : ZMod 11) ^ n * (2 * (n : ZMod 11) + 1)) by
          rw [map_mul, map_pow, map_neg, map_one], coeff_C_mul, coeff_X_pow]
    by_cases hk : m = (n + 1).choose 2
    · have hm11 : (m : ZMod 11) = 6 * ((n : ZMod 11) + 1) * (n : ZMod 11) := by
        rw [hk, choose_two_succ_cast_zmod_eleven]
      have hkey : 2 * (n : ZMod 11) + 1 = 0 :=
        (by decide : ∀ x : ZMod 11, 6 * (x + 1) * x ≠ 0 → 6 * (x + 1) * x ≠ 1 →
          6 * (x + 1) * x ≠ 3 → 6 * (x + 1) * x ≠ 6 → 6 * (x + 1) * x ≠ 10 → 2 * x + 1 = 0)
          (n : ZMod 11) (hm11 ▸ h0) (hm11 ▸ h1) (hm11 ▸ h3) (hm11 ▸ h6) (hm11 ▸ h10)
      rw [if_pos hk, hkey]; ring
    · rw [if_neg hk, mul_zero]
  exact hz.unique hasSum_zero

private lemma zmod_eleven_mem_of_ne {i : ℕ}
    (hi_ne : (((X; X)_∞ : (ZMod 11)⟦X⟧) ^ 3).coeff i ≠ 0) :
    (i : ZMod 11) = 0 ∨ (i : ZMod 11) = 1 ∨ (i : ZMod 11) = 3 ∨ (i : ZMod 11) = 6
      ∨ (i : ZMod 11) = 10 := by
  rcases eq_or_ne (i : ZMod 11) 0 with h | h0
  · exact Or.inl h
  rcases eq_or_ne (i : ZMod 11) 1 with h | h1
  · exact Or.inr (Or.inl h)
  rcases eq_or_ne (i : ZMod 11) 3 with h | h3
  · exact Or.inr (Or.inr (Or.inl h))
  rcases eq_or_ne (i : ZMod 11) 6 with h | h6
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  rcases eq_or_ne (i : ZMod 11) 10 with h | h10
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  exact absurd (coeff_qPochhammerInf_zmod_eleven_pow_three_eq_zero i h0 h1 h3 h6 h10) hi_ne

private lemma pentagonal_cast_zmod_eleven (k : ℤ) :
    (pentagonal k : ZMod 11) = 7 * (k : ZMod 11) ^ 2 - 6 * (k : ZMod 11) := by
  have h11 : (11 : ZMod 11) = 0 := by decide
  have hc := congrArg (Int.cast : ℤ → ZMod 11) (two_mul_natCast_pentagonal k)
  push_cast at hc
  linear_combination 6 * hc + ((k : ZMod 11) ^ 2 - (pentagonal k : ZMod 11)) * h11

/-- The Euler product `(X;X)_∞` over `ZMod 11` is supported on the residues `{0, 1, 2, 4, 5, 7}`
mod `11`: its coefficient vanishes at any index whose residue is not one of these. -/
private lemma coeff_qPochhammerInf_zmod_eleven_eq_zero (m : ℕ)
    (h0 : (m : ZMod 11) ≠ 0) (h1 : (m : ZMod 11) ≠ 1) (h2 : (m : ZMod 11) ≠ 2)
    (h4 : (m : ZMod 11) ≠ 4) (h5 : (m : ZMod 11) ≠ 5) (h7 : (m : ZMod 11) ≠ 7) :
    ((X; X)_∞ : (ZMod 11)⟦X⟧).coeff m = 0 := by
  letI : TopologicalSpace (ZMod 11) := ⊥
  letI : DiscreteTopology (ZMod 11) := ⟨rfl⟩
  have hne : ∀ k : ℤ, m ≠ pentagonal k := by
    intro k hk
    have hmc : (m : ZMod 11) = 7 * (k : ZMod 11) ^ 2 - 6 * (k : ZMod 11) := by
      rw [hk]; exact pentagonal_cast_zmod_eleven k
    have hkey := (by decide : ∀ x : ZMod 11, 7 * x ^ 2 - 6 * x = 0 ∨ 7 * x ^ 2 - 6 * x = 1
      ∨ 7 * x ^ 2 - 6 * x = 2 ∨ 7 * x ^ 2 - 6 * x = 4 ∨ 7 * x ^ 2 - 6 * x = 5
      ∨ 7 * x ^ 2 - 6 * x = 7) (k : ZMod 11)
    rw [← hmc] at hkey
    rcases hkey with h | h | h | h | h | h
    · exact h0 h
    · exact h1 h
    · exact h2 h
    · exact h4 h
    · exact h5 h
    · exact h7 h
  have hcoeff := (PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff (ZMod 11)).mp
    (hasSum_qPochhammerInf_self (q := (X : (ZMod 11)⟦X⟧))) m
  have hz : HasSum (fun _ : ℤ => (0 : ZMod 11)) (((X; X)_∞ : (ZMod 11)⟦X⟧).coeff m) := by
    refine hcoeff.congr_fun fun k => ?_
    rw [Units.smul_def, map_zsmul, PowerSeries.coeff_X_pow, if_neg (hne k), smul_zero]
  exact hz.unique hasSum_zero

private noncomputable def Jd (i : ℕ) : (ZMod 11)⟦X⟧ :=
  (((X; X)_∞ : (ZMod 11)⟦X⟧) ^ 3).dissect 11 i

private theorem Supp_Jd (i : ℕ) : Supp 11 i (Jd i) := Supp.dissect_supp _

private lemma Supp_n (n : ℕ) (hn : 2 ≤ n) : Supp 11 0 (n : (ZMod 11)⟦X⟧) := by
  haveI := Nat.AtLeastTwo.mk hn
  rw [show (n : (ZMod 11)⟦X⟧) = PowerSeries.C (n : ZMod 11) from (map_ofNat _ n).symm]
  exact Supp.C n

private lemma Supp_n3 : Supp 11 0 3 := Supp_n 3 (by decide)
private lemma Supp_n4 : Supp 11 0 4 := Supp_n 4 (by decide)
private lemma Supp_n6 : Supp 11 0 6 := Supp_n 6 (by decide)
private lemma Supp_n12 : Supp 11 0 12 := Supp_n 12 (by decide)
private lemma Supp_n24 : Supp 11 0 24 := Supp_n 24 (by decide)

private noncomputable def R4c : ℕ → (ZMod 11)⟦X⟧
  | 0 => 4 * Jd 3 * Jd 10 ^ 3 + 12 * Jd 3 ^ 2 * Jd 6 * Jd 10 + 6 * Jd 1 ^ 2 * Jd 10 ^ 2 +
      12 * Jd 1 ^ 2 * Jd 3 * Jd 6 + 12 * Jd 0 * Jd 6 ^ 2 * Jd 10 + 12 * Jd 0 ^ 2 * Jd 1 * Jd 10 +
      Jd 0 ^ 4
  | 1 => Jd 3 ^ 4 + 12 * Jd 1 * Jd 6 ^ 2 * Jd 10 + 12 * Jd 0 * Jd 3 * Jd 10 ^ 2 +
      12 * Jd 0 * Jd 3 ^ 2 * Jd 6 + 12 * Jd 0 * Jd 1 ^ 2 * Jd 10 + 6 * Jd 0 ^ 2 * Jd 6 ^ 2 +
      4 * Jd 0 ^ 3 * Jd 1
  | 2 => Jd 6 ^ 4 + 12 * Jd 1 * Jd 3 * Jd 10 ^ 2 + 12 * Jd 1 * Jd 3 ^ 2 * Jd 6 +
      4 * Jd 1 ^ 3 * Jd 10 + 12 * Jd 0 * Jd 1 * Jd 6 ^ 2 + 12 * Jd 0 ^ 2 * Jd 3 * Jd 10 +
      6 * Jd 0 ^ 2 * Jd 1 ^ 2
  | 3 => 4 * Jd 6 * Jd 10 ^ 3 + 12 * Jd 3 * Jd 6 ^ 2 * Jd 10 + 6 * Jd 1 ^ 2 * Jd 6 ^ 2 +
      24 * Jd 0 * Jd 1 * Jd 3 * Jd 10 + 4 * Jd 0 * Jd 1 ^ 3 + 4 * Jd 0 ^ 3 * Jd 3
  | 4 => 6 * Jd 3 ^ 2 * Jd 10 ^ 2 + 4 * Jd 3 ^ 3 * Jd 6 + 12 * Jd 1 ^ 2 * Jd 3 * Jd 10 + Jd 1 ^ 4 +
      12 * Jd 0 * Jd 6 * Jd 10 ^ 2 + 12 * Jd 0 * Jd 3 * Jd 6 ^ 2 + 12 * Jd 0 ^ 2 * Jd 1 * Jd 3
  | 5 => 12 * Jd 1 * Jd 6 * Jd 10 ^ 2 + 12 * Jd 1 * Jd 3 * Jd 6 ^ 2 + 12 * Jd 0 * Jd 3 ^ 2 * Jd 10 +
      12 * Jd 0 * Jd 1 ^ 2 * Jd 3 + 12 * Jd 0 ^ 2 * Jd 6 * Jd 10
  | 6 => 4 * Jd 6 ^ 3 * Jd 10 + 12 * Jd 1 * Jd 3 ^ 2 * Jd 10 + 4 * Jd 1 ^ 3 * Jd 3 +
      24 * Jd 0 * Jd 1 * Jd 6 * Jd 10 + 6 * Jd 0 ^ 2 * Jd 3 ^ 2 + 4 * Jd 0 ^ 3 * Jd 6
  | 7 => Jd 10 ^ 4 + 12 * Jd 3 * Jd 6 * Jd 10 ^ 2 + 6 * Jd 3 ^ 2 * Jd 6 ^ 2 +
      12 * Jd 1 ^ 2 * Jd 6 * Jd 10 + 4 * Jd 0 * Jd 6 ^ 3 + 12 * Jd 0 * Jd 1 * Jd 3 ^ 2 +
      12 * Jd 0 ^ 2 * Jd 1 * Jd 6
  | 8 => 4 * Jd 3 ^ 3 * Jd 10 + 4 * Jd 1 * Jd 6 ^ 3 + 6 * Jd 1 ^ 2 * Jd 3 ^ 2 +
      4 * Jd 0 * Jd 10 ^ 3 + 24 * Jd 0 * Jd 3 * Jd 6 * Jd 10 + 12 * Jd 0 * Jd 1 ^ 2 * Jd 6
  | 9 => 4 * Jd 1 * Jd 10 ^ 3 + 24 * Jd 1 * Jd 3 * Jd 6 * Jd 10 + 4 * Jd 1 ^ 3 * Jd 6 +
      4 * Jd 0 * Jd 3 ^ 3 + 6 * Jd 0 ^ 2 * Jd 10 ^ 2 + 12 * Jd 0 ^ 2 * Jd 3 * Jd 6
  | 10 => 6 * Jd 6 ^ 2 * Jd 10 ^ 2 + 4 * Jd 3 * Jd 6 ^ 3 + 4 * Jd 1 * Jd 3 ^ 3 +
      12 * Jd 0 * Jd 1 * Jd 10 ^ 2 + 24 * Jd 0 * Jd 1 * Jd 3 * Jd 6 + 4 * Jd 0 ^ 3 * Jd 10
  | _ => 0

private noncomputable def K3c : ℕ → (ZMod 11)⟦X⟧
  | 0 => 3 * Jd 6 ^ 2 * Jd 10 + 6 * Jd 0 * Jd 1 * Jd 10 + Jd 0 ^ 3
  | 1 => 3 * Jd 3 * Jd 10 ^ 2 + 3 * Jd 3 ^ 2 * Jd 6 + 3 * Jd 1 ^ 2 * Jd 10 + 3 * Jd 0 * Jd 6 ^ 2 +
      3 * Jd 0 ^ 2 * Jd 1
  | 2 => 3 * Jd 1 * Jd 6 ^ 2 + 6 * Jd 0 * Jd 3 * Jd 10 + 3 * Jd 0 * Jd 1 ^ 2
  | 3 => 6 * Jd 1 * Jd 3 * Jd 10 + Jd 1 ^ 3 + 3 * Jd 0 ^ 2 * Jd 3
  | 4 => 3 * Jd 6 * Jd 10 ^ 2 + 3 * Jd 3 * Jd 6 ^ 2 + 6 * Jd 0 * Jd 1 * Jd 3
  | 5 => 3 * Jd 3 ^ 2 * Jd 10 + 3 * Jd 1 ^ 2 * Jd 3 + 6 * Jd 0 * Jd 6 * Jd 10
  | 6 => 6 * Jd 1 * Jd 6 * Jd 10 + 3 * Jd 0 * Jd 3 ^ 2 + 3 * Jd 0 ^ 2 * Jd 6
  | 7 => Jd 6 ^ 3 + 3 * Jd 1 * Jd 3 ^ 2 + 6 * Jd 0 * Jd 1 * Jd 6
  | 8 => Jd 10 ^ 3 + 6 * Jd 3 * Jd 6 * Jd 10 + 3 * Jd 1 ^ 2 * Jd 6
  | 9 => Jd 3 ^ 3 + 3 * Jd 0 * Jd 10 ^ 2 + 6 * Jd 0 * Jd 3 * Jd 6
  | 10 => 3 * Jd 1 * Jd 10 ^ 2 + 6 * Jd 1 * Jd 3 * Jd 6 + 3 * Jd 0 ^ 2 * Jd 10
  | _ => 0

private lemma Supp_R4c (d : ℕ) (hd : d < 11) : Supp 11 d (R4c d) := by
  have h0 := Supp_Jd 0
  have h1 := Supp_Jd 1
  have h3 := Supp_Jd 3
  have h6 := Supp_Jd 6
  have h10 := Supp_Jd 10
  interval_cases d
  · exact ((((((((Supp_n4.mul h3).mul (h10.pow 3)).add (((Supp_n12.mul (h3.pow 2)).mul h6).mul
      h10)).add ((Supp_n6.mul (h1.pow 2)).mul (h10.pow 2))).add (((Supp_n12.mul (h1.pow 2)).mul
      h3).mul h6)).add (((Supp_n12.mul h0).mul (h6.pow 2)).mul h10)).add (((Supp_n12.mul (h0.pow
      2)).mul h1).mul h10)).add (h0.pow 4))
  · exact (((((((h3.pow 4).add (((Supp_n12.mul h1).mul (h6.pow 2)).mul h10)).add (((Supp_n12.mul
      h0).mul h3).mul (h10.pow 2))).add (((Supp_n12.mul h0).mul (h3.pow 2)).mul h6)).add
      (((Supp_n12.mul h0).mul (h1.pow 2)).mul h10)).add ((Supp_n6.mul (h0.pow 2)).mul (h6.pow
      2))).add ((Supp_n4.mul (h0.pow 3)).mul h1))
  · exact (((((((h6.pow 4).add (((Supp_n12.mul h1).mul h3).mul (h10.pow 2))).add (((Supp_n12.mul
      h1).mul (h3.pow 2)).mul h6)).add ((Supp_n4.mul (h1.pow 3)).mul h10)).add (((Supp_n12.mul
      h0).mul h1).mul (h6.pow 2))).add (((Supp_n12.mul (h0.pow 2)).mul h3).mul h10)).add
      ((Supp_n6.mul (h0.pow 2)).mul (h1.pow 2)))
  · exact (((((((Supp_n4.mul h6).mul (h10.pow 3)).add (((Supp_n12.mul h3).mul (h6.pow 2)).mul
      h10)).add ((Supp_n6.mul (h1.pow 2)).mul (h6.pow 2))).add ((((Supp_n24.mul h0).mul h1).mul
      h3).mul h10)).add ((Supp_n4.mul h0).mul (h1.pow 3))).add ((Supp_n4.mul (h0.pow 3)).mul h3))
  · exact ((((((((Supp_n6.mul (h3.pow 2)).mul (h10.pow 2)).add ((Supp_n4.mul (h3.pow 3)).mul
      h6)).add (((Supp_n12.mul (h1.pow 2)).mul h3).mul h10)).add (h1.pow 4)).add (((Supp_n12.mul
      h0).mul h6).mul (h10.pow 2))).add (((Supp_n12.mul h0).mul h3).mul (h6.pow 2))).add
      (((Supp_n12.mul (h0.pow 2)).mul h1).mul h3))
  · exact (((((((Supp_n12.mul h1).mul h6).mul (h10.pow 2)).add (((Supp_n12.mul h1).mul h3).mul
      (h6.pow 2))).add (((Supp_n12.mul h0).mul (h3.pow 2)).mul h10)).add (((Supp_n12.mul h0).mul
      (h1.pow 2)).mul h3)).add (((Supp_n12.mul (h0.pow 2)).mul h6).mul h10))
  · exact (((((((Supp_n4.mul (h6.pow 3)).mul h10).add (((Supp_n12.mul h1).mul (h3.pow 2)).mul
      h10)).add ((Supp_n4.mul (h1.pow 3)).mul h3)).add ((((Supp_n24.mul h0).mul h1).mul h6).mul
      h10)).add ((Supp_n6.mul (h0.pow 2)).mul (h3.pow 2))).add ((Supp_n4.mul (h0.pow 3)).mul h6))
  · exact (((((((h10.pow 4).add (((Supp_n12.mul h3).mul h6).mul (h10.pow 2))).add ((Supp_n6.mul
      (h3.pow 2)).mul (h6.pow 2))).add (((Supp_n12.mul (h1.pow 2)).mul h6).mul h10)).add
      ((Supp_n4.mul h0).mul (h6.pow 3))).add (((Supp_n12.mul h0).mul h1).mul (h3.pow 2))).add
      (((Supp_n12.mul (h0.pow 2)).mul h1).mul h6))
  · exact (((((((Supp_n4.mul (h3.pow 3)).mul h10).add ((Supp_n4.mul h1).mul (h6.pow 3))).add
      ((Supp_n6.mul (h1.pow 2)).mul (h3.pow 2))).add ((Supp_n4.mul h0).mul (h10.pow 3))).add
      ((((Supp_n24.mul h0).mul h3).mul h6).mul h10)).add (((Supp_n12.mul h0).mul (h1.pow 2)).mul
      h6))
  · exact (((((((Supp_n4.mul h1).mul (h10.pow 3)).add ((((Supp_n24.mul h1).mul h3).mul h6).mul
      h10)).add ((Supp_n4.mul (h1.pow 3)).mul h6)).add ((Supp_n4.mul h0).mul (h3.pow 3))).add
      ((Supp_n6.mul (h0.pow 2)).mul (h10.pow 2))).add (((Supp_n12.mul (h0.pow 2)).mul h3).mul h6))
  · exact (((((((Supp_n6.mul (h6.pow 2)).mul (h10.pow 2)).add ((Supp_n4.mul h3).mul (h6.pow
      3))).add ((Supp_n4.mul h1).mul (h3.pow 3))).add (((Supp_n12.mul h0).mul h1).mul (h10.pow
      2))).add ((((Supp_n24.mul h0).mul h1).mul h3).mul h6)).add ((Supp_n4.mul (h0.pow 3)).mul
      h10))

private lemma Supp_K3c (d : ℕ) (hd : d < 11) : Supp 11 d (K3c d) := by
  have h0 := Supp_Jd 0
  have h1 := Supp_Jd 1
  have h3 := Supp_Jd 3
  have h6 := Supp_Jd 6
  have h10 := Supp_Jd 10
  interval_cases d
  · exact ((((Supp_n3.mul (h6.pow 2)).mul h10).add (((Supp_n6.mul h0).mul h1).mul h10)).add
      (h0.pow 3))
  · exact ((((((Supp_n3.mul h3).mul (h10.pow 2)).add ((Supp_n3.mul (h3.pow 2)).mul h6)).add
      ((Supp_n3.mul (h1.pow 2)).mul h10)).add ((Supp_n3.mul h0).mul (h6.pow 2))).add ((Supp_n3.mul
      (h0.pow 2)).mul h1))
  · exact ((((Supp_n3.mul h1).mul (h6.pow 2)).add (((Supp_n6.mul h0).mul h3).mul h10)).add
      ((Supp_n3.mul h0).mul (h1.pow 2)))
  · exact (((((Supp_n6.mul h1).mul h3).mul h10).add (h1.pow 3)).add ((Supp_n3.mul (h0.pow 2)).mul
      h3))
  · exact ((((Supp_n3.mul h6).mul (h10.pow 2)).add ((Supp_n3.mul h3).mul (h6.pow 2))).add
      (((Supp_n6.mul h0).mul h1).mul h3))
  · exact ((((Supp_n3.mul (h3.pow 2)).mul h10).add ((Supp_n3.mul (h1.pow 2)).mul h3)).add
      (((Supp_n6.mul h0).mul h6).mul h10))
  · exact (((((Supp_n6.mul h1).mul h6).mul h10).add ((Supp_n3.mul h0).mul (h3.pow 2))).add
      ((Supp_n3.mul (h0.pow 2)).mul h6))
  · exact (((h6.pow 3).add ((Supp_n3.mul h1).mul (h3.pow 2))).add (((Supp_n6.mul h0).mul h1).mul
      h6))
  · exact (((h10.pow 3).add (((Supp_n6.mul h3).mul h6).mul h10)).add ((Supp_n3.mul (h1.pow 2)).mul
      h6))
  · exact (((h3.pow 3).add ((Supp_n3.mul h0).mul (h10.pow 2))).add (((Supp_n6.mul h0).mul h3).mul
      h6))
  · exact ((((Supp_n3.mul h1).mul (h10.pow 2)).add (((Supp_n6.mul h1).mul h3).mul h6)).add
      ((Supp_n3.mul (h0.pow 2)).mul h10))

private lemma hS4_eq :
    (Jd 0 + Jd 1 + Jd 3 + Jd 6 + Jd 10) ^ 4 = ∑ d ∈ Finset.range 11, R4c d := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, R4c]; ring

private lemma hS3_eq :
    (Jd 0 + Jd 1 + Jd 3 + Jd 6 + Jd 10) ^ 3 = ∑ d ∈ Finset.range 11, K3c d := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, K3c]; ring

private lemma natCast_ne (l : ℕ+) {r k : ℕ} (hr : r < l) (hk : k < l) (h : r ≠ k) :
    (r : ZMod l) ≠ (k : ZMod l) := by
  rw [Ne, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hk]
  exact h

private lemma Jd_eq_zero {r : ℕ} (h : r < 11 ∧ r ≠ 0 ∧ r ≠ 1 ∧ r ≠ 3 ∧ r ≠ 6 ∧ r ≠ 10) :
    Jd r = 0 := by
  obtain ⟨hr, h0, h1, h3, h6, h10⟩ := h
  have z0 : (r : ZMod 11) ≠ 0 := natCast_ne 11 hr (by norm_num) h0
  have z1 : (r : ZMod 11) ≠ 1 := natCast_ne 11 hr (by norm_num) h1
  have z3 : (r : ZMod 11) ≠ 3 := natCast_ne 11 hr (by norm_num) h3
  have z6 : (r : ZMod 11) ≠ 6 := natCast_ne 11 hr (by norm_num) h6
  have z10 : (r : ZMod 11) ≠ 10 := natCast_ne 11 hr (by norm_num) h10
  rw [Jd]; ext n; rw [coeff_dissect, map_zero]
  split_ifs with h
  · have hnr : (n : ZMod 11) = (r : ZMod 11) := h
    refine coeff_qPochhammerInf_zmod_eleven_pow_three_eq_zero n ?_ ?_ ?_ ?_ ?_ <;>
      rw [hnr] <;> assumption
  · rfl

/-- `(X;X)_∞^3` over `ZMod 11` splits as the sum of its dissection pieces on the residues
`{0, 1, 3, 6, 10}`. -/
private lemma hEz3 : ((X; X)_∞ : (ZMod 11)⟦X⟧) ^ 3 = Jd 0 + Jd 1 + Jd 3 + Jd 6 + Jd 10 := by
  have e2 : Jd 2 = 0 := Jd_eq_zero (by decide)
  have e4 : Jd 4 = 0 := Jd_eq_zero (by decide)
  have e5 : Jd 5 = 0 := Jd_eq_zero (by decide)
  have e7 : Jd 7 = 0 := Jd_eq_zero (by decide)
  have e8 : Jd 8 = 0 := Jd_eq_zero (by decide)
  have e9 : Jd 9 = 0 := Jd_eq_zero (by decide)
  have h := sum_dissect (((X; X)_∞ : (ZMod 11)⟦X⟧) ^ 3) (l := 11)
  simp only [show ((11 : ℕ+) : ℕ) = 11 from rfl, Finset.sum_range_succ,
    Finset.sum_range_zero] at h
  rw [← h]
  change (0 : (ZMod 11)⟦X⟧) + Jd 0 + Jd 1 + Jd 2 + Jd 3 + Jd 4 + Jd 5 + Jd 6 + Jd 7 + Jd 8 + Jd 9
    + Jd 10 = _
  rw [e2, e4, e5, e7, e8, e9]; ring

/-- The Frobenius identity `(X;X)_∞^12 = (X^11;X^11)_∞ · (X;X)_∞` over `ZMod 11` forces the
dissection of `(X;X)_∞^12` on any residue outside `{0, 1, 2, 4, 5, 7}` to vanish. -/
private lemma dissect_Ez12_eq_zero {r : ℕ} (h0 : (r : ZMod 11) ≠ 0) (h1 : (r : ZMod 11) ≠ 1)
    (h2 : (r : ZMod 11) ≠ 2) (h4 : (r : ZMod 11) ≠ 4) (h5 : (r : ZMod 11) ≠ 5)
    (h7 : (r : ZMod 11) ≠ 7) : (((X; X)_∞ : (ZMod 11)⟦X⟧) ^ 12).dissect 11 r = 0 := by
  have hfrob : ((X; X)_∞ : (ZMod 11)⟦X⟧) ^ 12 = (X ^ 11; X ^ 11)_∞ * (X; X)_∞ := by
    rw [show (12 : ℕ) = 11 + 1 from rfl, pow_succ,
      qPochhammerInf_zmod_p_self_pow_p 11 Nat.prime_eleven]
  rw [hfrob]; ext n; rw [coeff_dissect, map_zero]
  split_ifs with h
  · have hnr : n % 11 = r % 11 :=
      (ZMod.natCast_eq_natCast_iff' n r 11).mp (h : (n : ZMod 11) = (r : ZMod 11))
    refine coeff_mul_eq_zero_of_forall _ _ n fun i j hij => ?_
    by_cases hi : 11 ∣ i
    · right
      have hjmod : j % 11 = r % 11 := by obtain ⟨c, rfl⟩ := hi; omega
      have hjr : (j : ZMod 11) = (r : ZMod 11) := by
        have := congrArg (Nat.cast : ℕ → ZMod 11) hjmod
        rwa [ZMod.natCast_mod, ZMod.natCast_mod] at this
      refine coeff_qPochhammerInf_zmod_eleven_eq_zero j ?_ ?_ ?_ ?_ ?_ ?_ <;>
        rw [hjr] <;> assumption
    · exact Or.inl (coeff_qPochhammerInf_pow_p_zmod_p 11 Nat.prime_eleven i hi)
  · rfl

private lemma R4c_eq_zero {r : ℕ}
    (h : r < 11 ∧ r ≠ 0 ∧ r ≠ 1 ∧ r ≠ 2 ∧ r ≠ 4 ∧ r ≠ 5 ∧ r ≠ 7) : R4c r = 0 := by
  obtain ⟨hr, h0, h1, h2, h4, h5, h7⟩ := h
  have z0 : (r : ZMod 11) ≠ 0 := natCast_ne 11 hr (by norm_num) h0
  have z1 : (r : ZMod 11) ≠ 1 := natCast_ne 11 hr (by norm_num) h1
  have z2 : (r : ZMod 11) ≠ 2 := natCast_ne 11 hr (by norm_num) h2
  have z4 : (r : ZMod 11) ≠ 4 := natCast_ne 11 hr (by norm_num) h4
  have z5 : (r : ZMod 11) ≠ 5 := natCast_ne 11 hr (by norm_num) h5
  have z7 : (r : ZMod 11) ≠ 7 := natCast_ne 11 hr (by norm_num) h7
  have hval : (r : ZMod (11 : ℕ+)).val = r := by
    rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt hr
  rw [← hval, ← Supp.dissect_eq_of_sum (r : ZMod (11 : ℕ+)) hS4_eq Supp_R4c,
    show (Jd 0 + Jd 1 + Jd 3 + Jd 6 + Jd 10) ^ 4 = (((X; X)_∞ : (ZMod 11)⟦X⟧) ^ 3) ^ 4 by
      rw [hEz3],
    show (((X; X)_∞ : (ZMod 11)⟦X⟧) ^ 3) ^ 4 = ((X; X)_∞ : (ZMod 11)⟦X⟧) ^ 12 by ring]
  exact dissect_Ez12_eq_zero z0 z1 z2 z4 z5 z7

private lemma dissect_Ez21_six_eq_zero :
    ((((X; X)_∞ : (ZMod 11)⟦X⟧) ^ 3) ^ 7).dissect 11 6 = 0 := by
  have hR3 : R4c 3 = 0 := R4c_eq_zero (by decide)
  have hR6 : R4c 6 = 0 := R4c_eq_zero (by decide)
  have hR8 : R4c 8 = 0 := R4c_eq_zero (by decide)
  have hR9 : R4c 9 = 0 := R4c_eq_zero (by decide)
  have hR10 : R4c 10 = 0 := R4c_eq_zero (by decide)
  have hR : ∀ a : ℕ, a < 11 → ((Jd 0 + Jd 1 + Jd 3 + Jd 6 + Jd 10) ^ 4).dissect 11 a = R4c a :=
    fun a ha => by
      have := Supp.dissect_eq_of_sum (a : ZMod (11 : ℕ+)) hS4_eq Supp_R4c
      rw [ZMod.val_natCast] at this
      rwa [show a % ((11 : ℕ+) : ℕ) = a from Nat.mod_eq_of_lt ha] at this
  have hK : ∀ b : ℕ, b < 11 → ((Jd 0 + Jd 1 + Jd 3 + Jd 6 + Jd 10) ^ 3).dissect 11 b = K3c b :=
    fun b hb => by
      have := Supp.dissect_eq_of_sum (b : ZMod (11 : ℕ+)) hS3_eq Supp_K3c
      rw [ZMod.val_natCast] at this
      rwa [show b % ((11 : ℕ+) : ℕ) = b from Nat.mod_eq_of_lt hb] at this
  have hsub : ∀ r' : ℕ, r' < 11 →
      6 - ((r' : ℕ) : ZMod (11 : ℕ+)) = (((17 - r') % 11 : ℕ) : ZMod (11 : ℕ+)) := by
    decide
  rw [hEz3, show (Jd 0 + Jd 1 + Jd 3 + Jd 6 + Jd 10) ^ 7 = (Jd 0 + Jd 1 + Jd 3 + Jd 6 + Jd 10) ^ 4
      * (Jd 0 + Jd 1 + Jd 3 + Jd 6 + Jd 10) ^ 3 by ring,
    show (((Jd 0 + Jd 1 + Jd 3 + Jd 6 + Jd 10) ^ 4) * ((Jd 0 + Jd 1 + Jd 3 + Jd 6 + Jd 10) ^ 3)
        ).dissect 11 6
      = ∑ r' ∈ Finset.range 11, (((Jd 0 + Jd 1 + Jd 3 + Jd 6 + Jd 10) ^ 4).dissect 11 (6 - r'))
        * ((Jd 0 + Jd 1 + Jd 3 + Jd 6 + Jd 10) ^ 3).dissect 11 r' from
      Supp.dissect_mul_dissect_sum _ _,
    Finset.sum_congr rfl fun r' hr' => by rw [hsub r' (Finset.mem_range.mp hr')]]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub, Nat.reduceMod]
  rw [hR 6 (by norm_num), hR 5 (by norm_num), hR 4 (by norm_num), hR 3 (by norm_num),
    hR 2 (by norm_num), hR 1 (by norm_num), hR 0 (by norm_num), hR 10 (by norm_num),
    hR 9 (by norm_num), hR 8 (by norm_num), hR 7 (by norm_num), hK 0 (by norm_num),
    hK 1 (by norm_num), hK 2 (by norm_num), hK 3 (by norm_num), hK 4 (by norm_num),
    hK 5 (by norm_num), hK 6 (by norm_num), hK 7 (by norm_num), hK 8 (by norm_num),
    hK 9 (by norm_num), hK 10 (by norm_num)]
  simp only [R4c, K3c] at hR3 hR6 hR8 hR9 hR10 ⊢
  have h11 : (11 : (ZMod 11)⟦X⟧) = 0 := by
    haveI : Fact (Nat.Prime 11) := ⟨Nat.prime_eleven⟩
    haveI : CharP (ZMod 11)⟦X⟧ 11 := charP_of_injective_ringHom PowerSeries.C_injective 11
    exact_mod_cast CharP.cast_eq_zero (ZMod 11)⟦X⟧ 11
  linear_combination
    (10 * Jd 1 * Jd 3 * Jd 10 + 10 * Jd 1 ^ 3 + 4 * Jd 0 ^ 2 * Jd 3) * hR3 +
    (4 * Jd 6 ^ 2 * Jd 10 + 10 * Jd 0 * Jd 1 * Jd 10 + 10 * Jd 0 ^ 3) * hR6 +
    (10 * Jd 3 ^ 3 + 4 * Jd 0 * Jd 10 ^ 2 + 10 * Jd 0 * Jd 3 * Jd 6) * hR8 +
    (10 * Jd 10 ^ 3 + 10 * Jd 3 * Jd 6 * Jd 10 + 4 * Jd 1 ^ 2 * Jd 6) * hR9 +
    (10 * Jd 6 ^ 3 + 4 * Jd 1 * Jd 3 ^ 2 + 10 * Jd 0 * Jd 1 * Jd 6) * hR10 +
    (-5 * Jd 6 ^ 5 * Jd 10 ^ 2
      - 3 * Jd 3 * Jd 6 ^ 6
      - 3 * Jd 3 ^ 6 * Jd 10
      - 3 * Jd 1 * Jd 10 ^ 6
      - 10 * Jd 1 * Jd 3 * Jd 6 * Jd 10 ^ 4
      + 18 * Jd 1 * Jd 3 ^ 2 * Jd 6 ^ 2 * Jd 10 ^ 2
      + 4 * Jd 1 * Jd 3 ^ 3 * Jd 6 ^ 3
      - 5 * Jd 1 ^ 2 * Jd 3 ^ 5
      + 4 * Jd 1 ^ 3 * Jd 6 * Jd 10 ^ 3
      + 8 * Jd 1 ^ 3 * Jd 3 * Jd 6 ^ 2 * Jd 10
      - 5 * Jd 1 ^ 5 * Jd 6 ^ 2
      + 4 * Jd 0 * Jd 3 ^ 3 * Jd 10 ^ 3
      - 10 * Jd 0 * Jd 3 ^ 4 * Jd 6 * Jd 10
      + 8 * Jd 0 * Jd 1 * Jd 6 ^ 3 * Jd 10 ^ 2
      - 10 * Jd 0 * Jd 1 * Jd 3 * Jd 6 ^ 4
      + 18 * Jd 0 * Jd 1 ^ 2 * Jd 3 ^ 2 * Jd 10 ^ 2
      + 8 * Jd 0 * Jd 1 ^ 2 * Jd 3 ^ 3 * Jd 6
      - 10 * Jd 0 * Jd 1 ^ 4 * Jd 3 * Jd 10
      - 3 * Jd 0 * Jd 1 ^ 6
      - 5 * Jd 0 ^ 2 * Jd 10 ^ 5
      + 8 * Jd 0 ^ 2 * Jd 3 * Jd 6 * Jd 10 ^ 3
      + 18 * Jd 0 ^ 2 * Jd 3 ^ 2 * Jd 6 ^ 2 * Jd 10
      + 18 * Jd 0 ^ 2 * Jd 1 ^ 2 * Jd 6 * Jd 10 ^ 2
      + 18 * Jd 0 ^ 2 * Jd 1 ^ 2 * Jd 3 * Jd 6 ^ 2
      + 4 * Jd 0 ^ 3 * Jd 6 ^ 3 * Jd 10
      + 8 * Jd 0 ^ 3 * Jd 1 * Jd 3 ^ 2 * Jd 10
      + 4 * Jd 0 ^ 3 * Jd 1 ^ 3 * Jd 3
      - 10 * Jd 0 ^ 4 * Jd 1 * Jd 6 * Jd 10
      - 5 * Jd 0 ^ 5 * Jd 3 ^ 2
      - 3 * Jd 0 ^ 6 * Jd 6) * h11

private lemma map_powerSeriesCard_zmod_eleven_eq :
    PowerSeries.map (Int.castRingHom (ZMod 11)) powerSeriesCard
      = (((X; X)_∞ : (ZMod 11)⟦X⟧) ^ 3) ^ 7 * bInv (((X; X)_∞ : (ZMod 11)⟦X⟧) ^ 22) := by
  have hEu := isUnit_qPochhammerInf_X_zmod 11
  set F := PowerSeries.map (Int.castRingHom (ZMod 11)) powerSeriesCard with hF
  have hFE : F * ((X; X)_∞) = 1 := by
    rw [hF, map_powerSeriesCard_zmod 11]; exact hEu.bInv_mul_cancel
  have hFE22 : F * ((X; X)_∞ ^ 22) = ((X; X)_∞ ^ 3) ^ 7 := by
    rw [show F * ((X; X)_∞ ^ 22) = (F * (X; X)_∞) * (X; X)_∞ ^ 21 by ring, hFE, one_mul]
    ring
  exact (hEu.pow 22).eq_mul_bInv_of_mul_eq hFE22

theorem coeff_map_powerSeriesCard_eleven_mul_add_six (n : ℕ) :
    (PowerSeries.map (Int.castRingHom (ZMod 11)) powerSeriesCard).coeff (11 * n + 6) = 0 := by
  rw [map_powerSeriesCard_zmod_eleven_eq]
  refine coeff_mul_eq_zero_of_forall _ _ (11 * n + 6) fun i j hij => ?_
  by_cases hj : 11 ∣ j
  · refine Or.inl ?_
    have hi6 : (i : ZMod (11 : ℕ+)) = 6 := by
      obtain ⟨c, rfl⟩ := hj
      have hc := congrArg (Nat.cast (R := ZMod (11 : ℕ+))) hij
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hc
      have h11 : (11 : ZMod (11 : ℕ+)) = 0 := by decide
      linear_combination hc + ((n : ZMod (11 : ℕ+)) - (c : ZMod (11 : ℕ+))) * h11
    have hc := congrArg (PowerSeries.coeff i) dissect_Ez21_six_eq_zero
    rwa [coeff_dissect, if_pos hi6, map_zero] at hc
  · exact Or.inr (coeff_bInv_qPochhammerInf_zmod_p_sq 11 Nat.prime_eleven j hj)

/-- **Ramanujan's congruence mod 11**: `p(11n + 6) ≡ 0 (mod 11)` for every `n`, phrased as the
vanishing, modulo `11`, of the power series `∑ p(11n + 6) qⁿ`. -/
theorem dissectShift_eleven_six_map_zmod_eleven_powerSeries :
    PowerSeries.map (Int.castRingHom (ZMod 11)) (powerSeriesCard.dissectShift 11 6) = 0 := by
  ext n
  simp only [PowerSeries.coeff_map, coeff_dissectShift]
  exact coeff_map_powerSeriesCard_eleven_mul_add_six n

/-- **Ramanujan's congruence mod 11**, as a divisibility statement: `11 ∣ p(11n + 6)` for
every `n`. -/
theorem eleven_dvd_card_eleven_mul_add_six (n : ℕ) :
    11 ∣ Partition.card (11 * n + 6) := by
  have h := congrArg (PowerSeries.coeff n) dissectShift_eleven_six_map_zmod_eleven_powerSeries
  simp only [PowerSeries.coeff_map, coeff_dissectShift, coeff_powerSeriesCard, map_zero] at h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h

end Mod11

end Partition

end Nat
