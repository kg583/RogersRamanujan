module

public import RogersRamanujan.Algebra.BigOperators.Finsupp.Basic
import RogersRamanujan.Order.Filter.Cofinite
import RogersRamanujan.RingTheory.MvPowerSeries.Basic
import RogersRamanujan.RingTheory.MvPowerSeries.PiTopology
import RogersRamanujan.Topology.Algebra.InfiniteSum.Nonarchimedean
import RogersRamanujan.Topology.Algebra.Monoid
import RogersRamanujan.Topology.Algebra.Nonarchimedean.Basic
public import RogersRamanujan.Topology.Algebra.Nonarchimedean.Bounded
public import Mathlib.RingTheory.MvPowerSeries.PiTopology
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-! # Evaluation of multivariate power series

Unfortunately `MvPowerSeries.eval₂` does not seem very usable. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Finset Filter Topology NonarchimedeanAddGroup

/-- A family `f : σ → M` in a topological monoid-with-zero is *jointly topologically nilpotent*
if the `Finsupp`-indexed products `v ↦ ∏ i, f i ^ v i` tend to zero along the cofinite filter,
and for finite `σ` it is equivalent to each `f i` being topologically nilpotent. -/
@[mk_iff]
structure JointlyTopologicallyNilpotent {M σ : Type*} [Zero M] [CommMonoid M] [TopologicalSpace M]
    (f : σ → M) : Prop where
  tendsto_zero : Tendsto (fun L : σ →₀ ℕ ↦ L.pow f) cofinite (𝓝 0)

theorem JointlyTopologicallyNilpotent.map {M N σ : Type*}
    [CommMonoidWithZero M] [CommMonoidWithZero N] [TopologicalSpace M] [TopologicalSpace N]
    {F : Type*} [FunLike F M N] [MonoidWithZeroHomClass F M N]
    {v : σ → M} (h : JointlyTopologicallyNilpotent v) (f : F) (hf : Continuous f) :
    JointlyTopologicallyNilpotent (f ∘ v) where
  tendsto_zero := by
    convert (hf.continuousAt (x := 0)).tendsto.comp h.tendsto_zero
    · simp [map_finsuppPow]
    · simp

theorem jointlyTopologicallyNilpotent_iff_of_unique'
    {M σ : Type*} [CommMonoid M] [Zero M] [Unique σ] [TopologicalSpace M] (f : σ → M) :
    JointlyTopologicallyNilpotent f ↔ Tendsto (f default ^ ·) atTop (𝓝 0) := by
  rw [jointlyTopologicallyNilpotent_iff, ← (Finsupp.uniqueEquiv (default : σ)).symm.map_cofinite,
    tendsto_map'_iff, Nat.cofinite_eq_atTop]
  simp [Function.comp_def]

theorem jointlyTopologicallyNilpotent_iff_of_unique
    {M σ : Type*} [CommMonoidWithZero M] [Unique σ] [TopologicalSpace M] (f : σ → M) :
    JointlyTopologicallyNilpotent f ↔ IsTopologicallyNilpotent (f default) := by
  rw [jointlyTopologicallyNilpotent_iff_of_unique', IsTopologicallyNilpotent]

theorem JointlyTopologicallyNilpotent.isTopologicallyNilpotent
    {M σ : Type*} [CommMonoidWithZero M] [TopologicalSpace M] {f : σ → M}
    (h : JointlyTopologicallyNilpotent f) (i : σ) : IsTopologicallyNilpotent (f i) := by
  convert h.tendsto_zero.comp (f := (Finsupp.single i ·)) (x := cofinite)
    (Finsupp.single_injective _).tendsto_cofinite
  simp [IsTopologicallyNilpotent, Function.comp_def, Nat.cofinite_eq_atTop]

theorem jointlyTopologicallyNilpotent_iff_of_finite
    {S σ : Type*} [Finite σ] [CommMonoidWithZero S]
    [TopologicalSpace S] [ContinuousMul S] {q : σ → S} :
    JointlyTopologicallyNilpotent q ↔ ∀ i, IsTopologicallyNilpotent (q i) := by
  refine ⟨(·.isTopologicallyNilpotent), fun h ↦ ⟨?_⟩⟩
  let := Fintype.ofFinite σ
  simp_rw [Finsupp.pow_fintype]
  simp_rw [IsTopologicallyNilpotent, ← Nat.cofinite_eq_atTop] at h
  exact (tendsto_prod_cofinite_nhds_zero h).comp DFunLike.coe_injective.tendsto_cofinite

namespace MvPowerSeries

/-- A coefficient map `f : R → S` and family `q : σ → S` are evaluable at any multivariate power
series if `q` is jointly topologically nilpotent and `f` has bounded range. -/
@[mk_iff]
structure HasEval₂ {R S σ : Type*} [CommMonoid S] [Zero S] [TopologicalSpace S]
    (f : R → S) (q : σ → S) : Prop where
  jointlyTopologicallyNilpotent : JointlyTopologicallyNilpotent q
  boundedRange : f.BoundedRange

/-- Underlying function of `MvPowerSeries.eval`: the formal sum
`∑' v, f (p.coeff v) * ∏ i, q i ^ v i`. Only well-behaved when `HasEval₂ f q` holds. -/
noncomputable def evalFun
    {R S σ : Type*} [Semiring R] [CommSemiring S] [TopologicalSpace S]
    (f : R → S) (q : σ → S) (p : MvPowerSeries σ R) : S :=
  ∑' v, f (p.coeff v) * v.prod (q · ^ ·)

theorem hasSum_evalFun
    {R S σ : Type*} [Semiring R] [CommRing S]
    [UniformSpace S] [IsUniformAddGroup S] [NonarchimedeanRing S] [CompleteSpace S]
    {f : R → S} {q : σ → S} (h : HasEval₂ f q) (p : MvPowerSeries σ R) :
    HasSum (fun v ↦ f (p.coeff v) * v.pow q) (evalFun f q p) :=
  (summable_of_tendsto_cofinite_zero <| h.boundedRange.comp.mul_tendsto_zero
    h.jointlyTopologicallyNilpotent.tendsto_zero).hasSum

theorem evalFun_add
    {R S σ : Type*} [Semiring R] [CommRing S]
    [UniformSpace S] [IsUniformAddGroup S] [NonarchimedeanRing S] [CompleteSpace S] [T2Space S]
    {F : Type*} [FunLike F R S] [AddHomClass F R S]
    {f : F} {q : σ → S} (h : HasEval₂ f q) (p₁ p₂ : MvPowerSeries σ R) :
    evalFun f q (p₁ + p₂) = evalFun f q p₁ + evalFun f q p₂ :=
  have h₁ := hasSum_evalFun h p₁
  have h₂ := hasSum_evalFun h p₂
  have h₃ := hasSum_evalFun h (p₁ + p₂)
  h₃.unique <| (h₁.add h₂).congr_fun (by simp [add_mul])

@[simp] theorem HasEval₂.intCast_iff_of_finite
    {R σ : Type*} [Finite σ] [CommRing R] [TopologicalSpace R] [NonarchimedeanRing R] {q : σ → R} :
    HasEval₂ Int.cast q ↔ ∀ i, IsTopologicallyNilpotent (q i) := by
  simp [hasEval₂_iff, jointlyTopologicallyNilpotent_iff_of_finite]

theorem evalFun_mul
    {R S σ : Type*} [Semiring R] [CommRing S]
    [UniformSpace S] [IsUniformAddGroup S] [NonarchimedeanRing S] [CompleteSpace S] [T2Space S]
    {f : R →+* S} {q : σ → S} (h : HasEval₂ f q) (p₁ p₂ : MvPowerSeries σ R) :
    evalFun f q (p₁ * p₂) = evalFun f q p₁ * evalFun f q p₂ := by
  classical
  have h₁ := hasSum_evalFun h p₁
  have h₂ := hasSum_evalFun h p₂
  have h₃ := hasSum_evalFun h (p₁ * p₂)
  refine h₃.unique <| (h₁.mul_antidiagonal h₂).congr_fun <| fun v ↦ ?_
  simp_rw [coeff_mul, map_sum, map_mul, sum_mul, mul_mul_mul_comm _ (Finsupp.pow ..)]
  congr! 2 with p hp
  rw [← mem_antidiagonal.mp hp, Finsupp.pow_add]

/-- Evaluation of a multivariate power series at a commuting, jointly topologically nilpotent
family `q : σ → S` via a ring homomorphism `f : R →+* S` with bounded range, as a ring
homomorphism `MvPowerSeries σ R →+* S`. Defined to be `f ∘ constantCoeff` when `HasEval₂ f q`
fails, so the interesting lemmas assume `HasEval₂ f q`. -/
noncomputable def eval {R S σ : Type*} [Semiring R] [CommRing S]
    [UniformSpace S] [IsUniformAddGroup S] [NonarchimedeanRing S] [CompleteSpace S] [T2Space S]
    (f : R →+* S) (q : σ → S) : MvPowerSeries σ R →+* S :=
  open scoped Classical in
  if h : HasEval₂ f q then
  { toFun p := evalFun f q p
    map_zero' := by simp [evalFun]
    map_one' := by classical simp [evalFun, coeff_one]
    map_add' := evalFun_add h
    map_mul' := evalFun_mul h }
  else f.comp constantCoeff

theorem hasSum_eval {R S σ : Type*} [Semiring R] [CommRing S]
    [UniformSpace S] [IsUniformAddGroup S] [NonarchimedeanRing S] [CompleteSpace S] [T2Space S]
    {f : R →+* S} {q : σ → S} (h : HasEval₂ f q) (p : MvPowerSeries σ R) :
    HasSum (fun v ↦ f (p.coeff v) * v.pow q) (eval f q p) := by
  rw [eval, dif_pos h]
  exact hasSum_evalFun h p

theorem eval_apply {R S σ : Type*} [Semiring R] [CommRing S]
    [UniformSpace S] [IsUniformAddGroup S] [NonarchimedeanRing S] [CompleteSpace S] [T2Space S]
    {f : R →+* S} {q : σ → S} (h : HasEval₂ f q) (p : MvPowerSeries σ R) :
    eval f q p = ∑' v, f (p.coeff v) * v.pow q :=
  (hasSum_eval h p).tsum_eq.symm

@[simp]
theorem eval_X {R S σ : Type*} [Semiring R] [CommRing S]
    [UniformSpace S] [IsUniformAddGroup S] [NonarchimedeanRing S] [CompleteSpace S] [T2Space S]
    {f : R →+* S} {q : σ → S} (h : HasEval₂ f q) (i : σ) :
    eval f q (X i) = q i := by
  refine (hasSum_eval h (X i)).unique ?_
  convert hasSum_single (Finsupp.single i 1) _ (.unconditional _)
  · simp
  · classical simp +contextual [coeff_X]

@[simp]
theorem eval_C {R S σ : Type*} [Semiring R] [CommRing S]
    [UniformSpace S] [IsUniformAddGroup S] [NonarchimedeanRing S] [CompleteSpace S] [T2Space S]
    (f : R →+* S) (q : σ → S) (r : R) :
    eval f q (C r) = f r := by
  classical
  by_cases h : HasEval₂ f q
  · refine (hasSum_eval h (C r)).unique ?_
    simp only [coeff_C, apply_ite, map_zero, ite_mul, zero_mul]
    convert hasSum_ite_eq (0 : σ →₀ ℕ) _
    simp [*]
  rw [eval, dif_neg h]
  simp

@[simp]
theorem eval_monomial {R S σ : Type*} [Semiring R] [CommRing S]
    [UniformSpace S] [IsUniformAddGroup S] [NonarchimedeanRing S] [CompleteSpace S] [T2Space S]
    {f : R →+* S} {q : σ → S} (h : HasEval₂ f q) (v : σ →₀ ℕ) (r : R) :
    eval f q (monomial v r) = f r * v.pow q := by
  nth_rw 1 [← mul_one r, ← smul_eq_mul, map_smul, smul_eq_C_mul, map_mul, eval_C]
  congr 1
  induction v using Finsupp.induction with
  | zero => simp
  | single_add i n v hiv hn ih =>
    rw [Finsupp.pow_add, ← mul_one 1, ← monomial_mul_monomial, map_mul, ← X_pow_eq, ih,
      Finsupp.pow_single, map_pow, eval_X h]

open scoped WithPiTopology

@[fun_prop] theorem continuous_eval_of_discrete {R S σ : Type*} [Semiring R] [CommRing S]
    [UniformSpace S] [IsUniformAddGroup S] [NonarchimedeanRing S] [CompleteSpace S] [T2Space S]
    [TopologicalSpace R] [DiscreteTopology R] (f : R →+* S) (q : σ → S) :
    Continuous (eval f q) := by
  by_cases! h : ¬HasEval₂ f q
  · rw [eval, dif_neg h, RingHom.coe_comp, ← coeff_zero_eq_constantCoeff]
    fun_prop
  refine continuous_iff_continuousAt.mpr fun p ↦
    (hasBasis_nhds_zero_openAddSubgroup.nhds_of_zero _).tendsto_right_iff.mpr fun U _ ↦ ?_
  obtain ⟨V, _, hVU, hfV⟩ := (hasBasis_nhds_zero_openAddSubgroup.topologicallyBounded_iff _).mp
    h.boundedRange U trivial
  rw [Set.forall_mem_range] at hfV
  have h₁ := h.jointlyTopologicallyNilpotent.tendsto_zero V.mem_nhds_zero
  filter_upwards [(WithPiTopology.hasBasis_nhds_of_discrete p).mem_of_mem h₁] with x hx
  refine (hasSum_eval h x).sub_mem U.isClosed (hasSum_eval h p) fun i ↦ ?_
  by_cases hi : i.pow q ∈ V
  · exact sub_mem (hfV _ _ hi) (hfV _ _ hi)
  · rw [hx _ hi, sub_self]
    exact zero_mem U

theorem tendsto_monomial_one_cofinite_zero (R σ : Type*) [Semiring R] [TopologicalSpace R] :
    Tendsto (fun v : σ →₀ ℕ ↦ monomial (R := R) v 1) cofinite (𝓝 0) := fun U hU ↦ by
  rw [nhds_pi, mem_pi] at hU
  obtain ⟨I, hI, t, ht, hitU⟩ := hU
  refine hI.subset fun v hv ↦ by_contra fun hvI ↦ hv <| hitU fun i hi ↦ ?_
  classical simpa [apply_eq_coeff, coeff_monomial, show i ≠ v by grind] using mem_of_mem_nhds (ht i)

theorem jointlyTopologicallyNilpotent_X (R σ : Type*) [CommSemiring R] [TopologicalSpace R] :
    JointlyTopologicallyNilpotent (X (σ := σ) (R := R)) where
  tendsto_zero := by simp [pow_X_eq_monomial, tendsto_monomial_one_cofinite_zero]

theorem hasEval₂_of_continuous {R S σ : Type*} [CommSemiring R] [TopologicalSpace R]
    [CommRing S] [TopologicalSpace S] (f : MvPowerSeries σ R →+* S)
    (hf : Continuous f) (hfb : (⇑f ∘ C).BoundedRange) : HasEval₂ (f ∘ C) (f ∘ X) where
  jointlyTopologicallyNilpotent := (jointlyTopologicallyNilpotent_X _ _).map f hf
  boundedRange := hfb

/-- Universal property of `MvPowerSeries`: every continuous map with bounded range is `eval`. -/
theorem eq_eval {R S σ : Type*} [CommSemiring R] [CommRing S]
    [UniformSpace S] [IsUniformAddGroup S] [NonarchimedeanRing S] [CompleteSpace S] [T2Space S]
    [TopologicalSpace R] [DiscreteTopology R] (f : MvPowerSeries σ R →+* S)
    (hf : Continuous f) (hfb : (⇑f ∘ C).BoundedRange) : f = eval (f.comp C) (f ∘ X) := by
  ext p
  have hp := WithPiTopology.hasSum_of_monomials_self p
  refine (hp.map f hf).unique <| (hp.map _ (by fun_prop)).congr_fun fun v ↦ ?_
  simp [hasEval₂_of_continuous f hf hfb, ← apply_eq_coeff]
  simp [monomial_eq_mul_pow_X, map_finsuppPow]

/-- Universal property of `MvPowerSeries σ ℤ`. Every continuous map is `eval`. -/
theorem eq_intEval {σ R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
    [NonarchimedeanRing R] [CompleteSpace R] [T2Space R]
    (f : MvPowerSeries σ ℤ →+* R) (hf : Continuous f) : f = eval (Int.castRingHom R) (f ∘ X) := by
  have hC : f.comp C = Int.castRingHom R := Subsingleton.elim _ _
  have : f ∘ C = Int.cast := congr($hC)
  convert eq_eval f hf (by simp [this])
  all_goals first | exact hC | exact hC.symm | rfl

end MvPowerSeries
