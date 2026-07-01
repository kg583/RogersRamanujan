module

public import RogersRamanujan.RingTheory.MvPowerSeries.Evaluation
public import RogersRamanujan.RingTheory.PowerSeries.DiscreteTopology

/-! # Strong evaluation of power series

Strong evaluation `sEval f q` evaluates a power series at a topologically nilpotent
element `q` via `∑' n, f(coeff n) * q^n`, where `f` is a ring homomorphism with
topologically bounded range.
-/

@[expose] public section

open Finset Filter Topology

namespace PowerSeries

theorem hasEval₂_iff {R : Type*} [CommSemiring R] [TopologicalSpace R]
    {ι : Type*} (f : ι → R) (q : R) :
    MvPowerSeries.HasEval₂ f (fun _ : Unit ↦ q) ↔
    f.BoundedRange ∧ IsTopologicallyNilpotent q := by
  rw [MvPowerSeries.hasEval₂_iff, jointlyTopologicallyNilpotent_iff_of_unique, and_comm]

variable {R₀ : Type*} [Semiring R₀]
  {R : Type*} [CommRing R] [UniformSpace R] [NonarchimedeanRing R]
  [IsUniformAddGroup R] [CompleteSpace R] [T2Space R]

/-- Strong evaluation of a power series at a topologically nilpotent
element, via `∑' n, f(coeff n) * q^n`. Requires `f` to have
topologically bounded range and commute with `q`. Returns the junk value `f ∘ constantCoeff`
when the hypotheses fail. -/
noncomputable def sEval (f : R₀ →+* R) (q : R) : R₀⟦X⟧ →+* R :=
  MvPowerSeries.eval f fun _ ↦ q

theorem hasSum_sEval_of_commute (f : R₀ →+* R) {q : R} (hf : (⇑f).BoundedRange)
    (hq : IsTopologicallyNilpotent q) (p : R₀⟦X⟧) :
    HasSum (fun n ↦ f (p.coeff n) * q ^ n) (sEval f q p) :=
  have h := MvPowerSeries.hasSum_eval ((hasEval₂_iff f q).mpr ⟨hf, hq⟩) p
  ((Finsupp.uniqueEquiv ()).symm.hasSum_iff.mpr h).congr_fun fun n ↦ by simp [coeff]

theorem sEval_apply_of_commute (f : R₀ →+* R) {q : R} (hf : (⇑f).BoundedRange)
    (hq : IsTopologicallyNilpotent q) (p : R₀⟦X⟧) :
    sEval f q p = ∑' n, f (p.coeff n) * q ^ n :=
  (hasSum_sEval_of_commute f hf hq p).tsum_eq.symm

@[simp] theorem sEval_X_of_commute (f : R₀ →+* R) {q : R} (hf : (⇑f).BoundedRange)
    (hq : IsTopologicallyNilpotent q) : sEval f q X = q :=
  MvPowerSeries.eval_X ((hasEval₂_iff f q).mpr ⟨hf, hq⟩) _

@[simp] theorem sEval_C (f : R₀ →+* R) (q : R) (r : R₀) : sEval f q (C r) = f r :=
  MvPowerSeries.eval_C ..

/-- Evaluation from `ℤ⟦X⟧` sending `X` to any specified topologically nilpotent element `q`. -/
noncomputable def intEval (q : R) : ℤ⟦X⟧ →+* R :=
  sEval (Int.castRingHom R) q

theorem hasSum_intEval {q : R} (hq : IsTopologicallyNilpotent q) (p : ℤ⟦X⟧) :
    HasSum (fun n ↦ p.coeff n * q ^ n) (intEval q p) :=
  hasSum_sEval_of_commute (Int.castRingHom R) .range_intCast hq _

@[simp] theorem intEval_X {q : R} (hq : IsTopologicallyNilpotent q) : intEval q X = q :=
  sEval_X_of_commute (Int.castRingHom R) .range_intCast hq

theorem intEval_C (q : R) (r : ℤ) : intEval q (C r) = r := by simp

section
open scoped DiscreteTopology

theorem bounded_univ {R : Type*} [Semiring R] : (Set.univ : Set R⟦X⟧).TopologicallyBounded where
  exists_mul_subset hU :=
    let ⟨n, _, hn⟩ := DiscreteTopology.hasBasis_nhds_zero.mem_iff.mp hU
    ⟨_, DiscreteTopology.span_X_pow_mem_nhds_zero n, Set.mul_subset_iff.mpr fun _ _ _ hy ↦
      hn <| Ideal.mul_mem_left _ _ hy⟩

@[simp] theorem bounded {R : Type*} [Semiring R] (S : Set R⟦X⟧) : S.TopologicallyBounded :=
  bounded_univ.mono <| by simp

@[fun_prop, simp] theorem sEval_continuous (f : R₀ →+* R) (q : R) : Continuous (sEval f q) :=
  let : UniformSpace R₀ := ⊥
  MvPowerSeries.continuous_eval_of_discrete _ _

@[fun_prop, simp] theorem intEval_continuous (q : R) : Continuous (intEval q) :=
  sEval_continuous _ _

/-- Universal property of `ℤ⟦X⟧`. Every nice enough (i.e. continuous) map is `intEval`. -/
theorem eq_intEval (f : ℤ⟦X⟧ →+* R) (hf : Continuous f) : f = intEval (f X) := by
  have hfx : IsTopologicallyNilpotent (f X) := .map hf (by simp)
  refine DiscreteTopology.ext_ringHom hf (by fun_prop) (by ext; simp) (by simp [hfx])

variable {R S : Type*} [Semiring R] [CommRing S]

theorem map_eq_sEval_X {f : R →+* S} : map f = sEval (C.comp f) (X : S⟦X⟧) := RingHom.ext fun p ↦
  (map f p).hasSum_self.unique <| (p.hasSum_self.map (sEval (C.comp f) X) (by fun_prop)).congr_fun
    (by simp)

end

end PowerSeries
