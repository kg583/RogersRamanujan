module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.MvPowerSeries.LinearTopology

public import RogersRamanujan.NumberTheory.QTheory.BinomialTheorem
public import RogersRamanujan.NumberTheory.QTheory.Defs
public import RogersRamanujan.NumberTheory.QTheory.Pentagonal
import RogersRamanujan.NumberTheory.QTheory.StrongNonarchimedean
public import RogersRamanujan.RingTheory.PowerSeries.DiscreteTopology
public import RogersRamanujan.RingTheory.PowerSeries.Dissect
public import RogersRamanujan.RingTheory.PowerSeries.Evaluation

/-! # q-Series mod p

## Main definitions

* `Nat.Partition.powerSeriesCard`: the power series `∑ p(n) qⁿ`

## Main results

* `qPochhammerInf_zmod_p_self_pow_p`: `((X; X)_∞)^p = (X^p; X^p)_∞` mod `p` a prime
* `coeff_bInv_qPochhammerInf_pow_p_zmod_p`: `((X; X)_∞)^-p` is supported only on `0` mod `p`
-/

@[expose] public section

open QTheory PowerSeries DiscreteTopology

theorem isUnit_qPochhammerInf_X_zmod (l : ℕ) :
    IsUnit ((X; X)_∞ : (ZMod l)⟦X⟧) := by
  have hcont : Continuous (map (Int.castRingHom (ZMod l)) : ℤ⟦X⟧ →+* (ZMod l)⟦X⟧) := by fun_prop
  have := (isUnit_qPochhammerInf (a := (X : ℤ⟦X⟧)) (q := X)).map (map (Int.castRingHom (ZMod l)))
  rwa [map_qPochhammerInf_of_isTopologicallyNilpotent (map (Int.castRingHom (ZMod l))) hcont
    isTopologicallyNilpotent_X isTopologicallyNilpotent_X, map_X] at this

theorem qPochhammerInf_zmod_p_self_pow_p (p : ℕ) (hp : Nat.Prime p) :
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

theorem coeff_qPochhammerInf_pow_p_zmod_p (p : ℕ) (hp : Nat.Prime p) (m : ℕ)
    (hm : ¬ (p ∣ m)) : ((X ^ p; X ^ p)_∞ : (ZMod p)⟦X⟧).coeff m = 0 := by
  letI : TopologicalSpace (ZMod p) := ⊥
  letI : DiscreteTopology (ZMod p) := ⟨rfl⟩
  have hcoeff := (PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff (ZMod p)).mp
    (hasSum_qPochhammerInf_self (q := (X ^ p : (ZMod p)⟦X⟧)) (isNilpotent_pow_X_p p hp)) m
  have hz : HasSum (fun _ : ℤ => (0 : ZMod p))
      (((X ^ p; X ^ p)_∞ : (ZMod p)⟦X⟧).coeff m) := by
    refine hcoeff.congr_fun fun k => ?_
    rw [Units.smul_def, map_zsmul, ← pow_mul, PowerSeries.coeff_X_pow,
      if_neg (fun h => hm ⟨pentagonal k, h⟩), smul_zero]
  exact hz.unique hasSum_zero

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
  rw [zsmul_eq_mul, ← map_intCast (PowerSeries.C : ZMod l →+* (ZMod l)⟦X⟧)]

theorem coeff_bInv_qPochhammerInf_pow_p_zmod_p (p : ℕ) (hp : Nat.Prime p) (m : ℕ)
    (hm : ¬ (p ∣ m)) : (bInv ((X ^ p; X ^ p)_∞ : (ZMod p)⟦X⟧)).coeff m = 0 := by
  have hfun : (fun n : ℕ => Partition.card n • (X ^ p : (ZMod p)⟦X⟧) ^ n)
      = fun n => C ((Partition.card n : ℤ) : ZMod p) * (X ^ p) ^ n := by
    funext n
    rw [zsmul_eq_mul, ← map_intCast (PowerSeries.C : ZMod p →+* (ZMod p)⟦X⟧)]
  have hsum := hasSum_card (q := (X ^ p : (ZMod p)⟦X⟧)) (isNilpotent_pow_X_p p hp)
  rw [hfun] at hsum
  rw [← hsum.tsum_eq]
  rw [coeff_tsum_mul_pow_eq_succ (by
    simp only [map_pow, constantCoeff_X]
    rw [zero_pow]
    exact Nat.Prime.ne_zero hp)]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [coeff_C_mul, ← pow_mul, coeff_X_pow, if_neg (fun h => hm ⟨i, h⟩), mul_zero]

theorem coeff_bInv_qPochhammerInf_zmod_p_sq (p : ℕ) (hp : Nat.Prime p)
    (m : ℕ) (hm : ¬ (p ∣ m)) : (bInv (((X; X)_∞ : (ZMod p)⟦X⟧) ^ (2 * p))).coeff m = 0 := by
  have hE := (qPochhammerInf_zmod_p_self_pow_p p hp).symm
  have hEu : IsUnit ((X ^ p; X ^ p)_∞ : (ZMod p)⟦X⟧) := by
    rw [hE]; exact (isUnit_qPochhammerInf_X_zmod p).pow p
  have hsq : ((X; X)_∞ : (ZMod p)⟦X⟧) ^ (2 * p) = ((X ^ p; X ^ p)_∞) * ((X ^ p; X ^ p)_∞) := by
    rw [hE]; ring
  rw [hsq, hEu.bInv_mul hEu]
  refine coeff_mul_eq_zero_of_forall _ _ m fun i j hij => ?_
  by_cases hi : p ∣ i
  · exact Or.inr (coeff_bInv_qPochhammerInf_pow_p_zmod_p p hp j
    (fun hj => hm (hij ▸ Nat.dvd_add hi hj)))
  · exact Or.inl (coeff_bInv_qPochhammerInf_pow_p_zmod_p p hp i hi)

end Nat.Partition
