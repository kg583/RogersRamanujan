module

import RogersRamanujan.Algebra.Ring.Subgroup
public import RogersRamanujan.Data.Finsupp.Defs
import RogersRamanujan.Data.Finsupp.Weight
import RogersRamanujan.Order.Antichain
public import RogersRamanujan.Order.Hom.Basic
public import RogersRamanujan.Order.WellFoundedSet
import RogersRamanujan.Tactic.OfClass
public import RogersRamanujan.Topology.Algebra.Nonarchimedean.IsSubgroupsBasis
public import RogersRamanujan.Topology.Algebra.Nonarchimedean.Strong
public import Mathlib.Algebra.Ring.Subgroup
public import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Int.Interval
public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.Topology.Algebra.UniformFilterBasis
import Mathlib.Topology.MetricSpace.Bounded

/-! # Multi-variable Laurent series

Multi-variable Laurent series are surprisingly tricky to handle, and here we commit to the following
definition:

* The partial order on `σ →₀ ℤ` will be given by comparing the total degree. Different elements
  with the same total degree are incomparable.
* (We will need a type synonym to enforce the above ordering.)
* Then the ring of multi-variable Laurent series will be defined as `HahnSeries` of that over `R`.

One side effect is that we now have `∑' n : ℕ, (x^2/y)^n` as a valid Laurent series.

For a more concrete description: the set of total degrees have to be bounded below, and for each
total degree, there should be finitely many non-zero coefficients.

-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section SumOrder

/-- Type synonym for the following partial order on `σ →₀ ℤ`:
- Compare total degree.
- Different elements with the same total degree are incomparable. -/
def SumOrder (σ : Type*) := σ →₀ ℤ
deriving AddCommMonoid, AddCommGroup, FunLike, DecidableEq

end SumOrder

namespace SumOrder
variable {σ : Type*} {f g : σ →₀ ℤ} {x y z : SumOrder σ}

open Relation Finsupp

/-- Convert a finsupp to a sum order. -/
noncomputable def of : (σ →₀ ℤ) ≃+ SumOrder σ := .refl _

/-- Wrapper of `Finsupp.degree`. -/
def degree : SumOrder σ →+ ℤ := Finsupp.degree

@[simp, grind =] theorem degree_of : (of f).degree = f.degree := rfl

theorem degree_apply : x.degree = (of.symm x).degree := rfl

@[simp] theorem degree_symm_of : (of.symm x).degree = x.degree := rfl

@[simp] theorem add_apply {σ : Type*} (p q : SumOrder σ) (i : σ) :
    (p + q) i = p i + q i := rfl

@[simp] theorem sub_apply {σ : Type*} (p q : SumOrder σ) (i : σ) :
    (p - q) i = p i - q i := rfl

@[simp] theorem zero_apply {σ : Type*} (i : σ) :
    (0 : SumOrder σ) i = 0 := rfl

theorem of_single_apply {σ : Type*} [DecidableEq σ] (i : σ) (n : ℤ) (j : σ) :
    (of (.single i n)) j = if i = j then n else 0 := Finsupp.single_apply

-- cannot make this `simp` because it would fire too often
theorem finsupp_apply {σ : Type*} (f : SumOrder σ) (i : σ) :
    DFunLike.coe (F := σ →₀ ℤ) f i = f i := rfl

instance : PartialOrder (SumOrder σ) where
  lt := (· < ·).onFun degree
  le := ReflGen <| (· < ·).onFun degree
  le_refl := by grind
  le_trans := by grind
  le_antisymm := by grind
  lt_iff_le_not_ge := by grind

@[simp, grind =]
theorem of_le_iff : of f ≤ of g ↔ f.degree < g.degree ∨ f = g :=
  (reflGen_iff _ _ _).trans <| by simp [Function.onFun, or_comm, eq_comm]

@[mono, grind .] theorem of_mono (hfg : f ≤ g) : of f ≤ of g := by
  rw [of_le_iff, or_iff_not_imp_right]
  exact fun hne ↦ degree_strictMono <| lt_of_le_of_ne hfg hne

@[grind =] theorem le_iff' : x ≤ y ↔ x.degree < y.degree ∨ x = y := of_le_iff

noncomputable instance : DecidableLE (SumOrder σ) := fun x y ↦
  decidable_of_iff' (x.degree < y.degree ∨ x = y) (by simp [le_iff'])

@[simp, grind =]
theorem of_lt_iff : of f < of g ↔ f.degree < g.degree := Iff.rfl

@[grind =] theorem lt_iff' : x < y ↔ x.degree < y.degree := Iff.rfl

@[elab_as_elim, induction_eliminator, cases_eliminator]
theorem of_induction {P : SumOrder σ → Prop} (ih : ∀ f, P (of f)) : ∀ f, P f := ih

instance : IsOrderedCancelAddMonoid (SumOrder σ) where
  add_le_add_left x y h z := by
    induction x; induction y; induction z; revert h
    simp_rw [le_iff', ← map_add, degree_apply, map_add, add_lt_add_iff_right, add_left_inj]
    exact id
  le_of_add_le_add_left x y z := by
    induction x; induction y; induction z
    simp_rw [le_iff', ← map_add, degree_apply, map_add, add_lt_add_iff_left, add_right_inj]
    exact id

theorem degree_strictMono : StrictMono (degree (σ := σ)) := fun _ _ h ↦ h

theorem degree_mono : Monotone (degree (σ := σ)) := degree_strictMono.monotone

theorem isAntichain_degree_eq (σ : Type*) (n : ℤ) :
    IsAntichain (· ≤ ·) {x : SumOrder σ | x.degree = n} := fun _ _ _ _ _ _ ↦ by grind

theorem isPWO_iff {s : Set (SumOrder σ)} :
    s.IsPWO ↔ ∃ M, (∀ x ∈ s, M ≤ x.degree) ∧ ∀ n, {x ∈ s | x.degree = n}.Finite := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  refine ⟨fun h ↦ ?_, fun ⟨M, hM, hn⟩ ↦ ?_⟩
  · use h.image_of_monotone degree_mono |>.isWF |>.min (hs.image _)
    refine ⟨fun x hx ↦ Set.IsWF.min_le _ _ <| by grind,
      fun n ↦ isAntichain_degree_eq σ n |>.subset (by grind) |>.isPWO_iff_finite |>.mp
        (h.mono <| by grind)⟩
  · rw [Set.isPWO_iff_exists]
    intro f hf
    have key : Set.range (degree ∘ f) |>.IsWF := bddBelow_def.mpr ⟨M, by grind⟩ |>.isWF
    obtain ⟨N, hN : (f N).degree = _⟩ := key.min_mem <| Set.range_nonempty _
    have N_min (n) : (f N).degree ≤ (f (N + n)).degree := hN ▸ key.min_le _ (by simp)
    by_cases heq : ∀ n, (f (N + n)).degree = (f N).degree
    · obtain ⟨m, -, n, -, hmn1, hmn2⟩ := Set.infinite_univ.exists_ne_map_eq_of_mapsTo
        (f := (f <| N + ·)) (by grind [Set.MapsTo]) (hn (f N).degree)
      exact ⟨N + min m n, N + max m n, by grind⟩
    · obtain ⟨m, hm⟩ := not_forall.mp heq
      refine ⟨N, N + m, by grind, le_iff'.mpr <| by grind⟩

/-- Pushforward of `SumOrder` along a map of index types. -/
noncomputable def map {σ τ : Type*} (f : σ → τ) : SumOrder σ →+ SumOrder τ where
  toFun p := of <| (of.symm p).mapDomain f
  map_zero' := by simp
  map_add' := by simp [Finsupp.mapDomain_add]

theorem map_injective {σ τ : Type*} {f : σ → τ} (hf : Function.Injective f) :
    Function.Injective (map f) := Finsupp.mapDomain_injective hf

theorem map_le_iff {σ τ : Type*} {f : σ → τ} (hf : Function.Injective f) :
    ∀ p q, map f p ≤ map f q ↔ p ≤ q := by
  simp [of.surjective.forall, map, (Finsupp.mapDomain_injective hf).eq_iff]

@[simp] theorem degree_map {σ τ : Type*} {f : σ → τ} (p : SumOrder σ) :
    degree (map f p) = degree p := by
  simp [degree_of, map]

/-- Order embedding on `SumOrder` induced by an injection of index types. -/
@[simps] noncomputable def mapEmbedding {σ τ : Type*} (f : σ ↪ τ) : SumOrder σ ↪o SumOrder τ where
  toFun := map f
  inj' := map_injective f.injective
  map_rel_iff' := map_le_iff f.injective _ _

@[simp] theorem map_apply_eq_zero_of
    {σ τ : Type*} (f : σ → τ) (p : SumOrder σ) (i : τ) (hi : i ∉ Set.range f) :
    map f p i = 0 := Finsupp.mapDomain_notin_range _ _ hi

@[simp] theorem range_map {σ τ : Type*} (f : σ → τ) :
    Set.range (map f) = {p | p.support ⊆ Set.range f} := by
  ext p
  constructor
  · rintro ⟨p, rfl⟩ i hi
    by_contra! h
    exact Finsupp.mem_support_iff.mp hi <| Finsupp.mapDomain_notin_range _ _ h
  · suffices Finsupp.supported ℤ ℤ (Set.range f) ≤ (map f).range.toIntSubmodule from @this p
    rw [Finsupp.supported_eq_span_single, Submodule.span_le]
    rintro - ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨.of (.single i 1), by simp [map]; rfl⟩

end SumOrder

open HahnSeries SumOrder

/-- The type of multi-variable Laurent series over a ring.

It is defined as `HahnSeries (SumOrder σ) R`. -/
def MvLaurentSeries (σ R : Type*) [Zero R] := R⟦SumOrder σ⟧
deriving Inhabited, Zero

namespace MvLaurentSeries
variable {σ R : Type*}

/-! ### Instances -/

section Instances

instance [AddMonoid R] : Add (MvLaurentSeries σ R) :=
  inferInstanceAs (Add (R⟦SumOrder σ⟧))

instance [NegZeroClass R] : Neg (MvLaurentSeries σ R) :=
  inferInstanceAs (Neg (R⟦SumOrder σ⟧))

instance [AddMonoid R] : AddMonoid (MvLaurentSeries σ R) :=
  inferInstanceAs (AddMonoid (R⟦SumOrder σ⟧))

instance {V : Type*} [Zero V] [SMulZeroClass R V] : SMul R (MvLaurentSeries σ V) :=
  inferInstanceAs (SMul R (V⟦SumOrder σ⟧))

instance [AddCommMonoid R] : AddCommMonoid (MvLaurentSeries σ R) :=
  inferInstanceAs (AddCommMonoid (R⟦SumOrder σ⟧))

instance [AddGroup R] : AddGroup (MvLaurentSeries σ R) :=
  inferInstanceAs (AddGroup (R⟦SumOrder σ⟧))

instance [AddGroup R] : Sub (MvLaurentSeries σ R) :=
  inferInstanceAs (Sub (R⟦SumOrder σ⟧))

instance [AddCommGroup R] : AddCommGroup (MvLaurentSeries σ R) :=
  inferInstanceAs (AddCommGroup (R⟦SumOrder σ⟧))

instance {V : Type*} [Zero V] [SMulZeroClass R V] : SMulZeroClass R (MvLaurentSeries σ V) :=
  inferInstanceAs (SMulZeroClass R (V⟦SumOrder σ⟧))

instance {V : Type*} [Monoid R] [AddMonoid V] [DistribMulAction R V] :
    DistribMulAction R (MvLaurentSeries σ V) :=
  inferInstanceAs (DistribMulAction R (V⟦SumOrder σ⟧))

instance {V : Type*} [Semiring R] [AddCommMonoid V] [Module R V] :
    Module R (MvLaurentSeries σ V) :=
  inferInstanceAs (Module R (V⟦SumOrder σ⟧))

noncomputable instance [Zero R] [IntCast R] : IntCast (MvLaurentSeries σ R) :=
  inferInstanceAs (IntCast (R⟦SumOrder σ⟧))

noncomputable instance [Zero R] [NNRatCast R] : NNRatCast (MvLaurentSeries σ R) :=
  inferInstanceAs (NNRatCast (R⟦SumOrder σ⟧))

noncomputable instance [Zero R] [NatCast R] : NatCast (MvLaurentSeries σ R) :=
  inferInstanceAs (NatCast (R⟦SumOrder σ⟧))

noncomputable instance [Zero R] [Nontrivial R] : Nontrivial (MvLaurentSeries σ R) :=
  inferInstanceAs (Nontrivial (R⟦SumOrder σ⟧))

noncomputable instance [Zero R] [One R] : One (MvLaurentSeries σ R) :=
  inferInstanceAs (One (R⟦SumOrder σ⟧))

noncomputable instance [Zero R] [RatCast R] : RatCast (MvLaurentSeries σ R) :=
  inferInstanceAs (RatCast (R⟦SumOrder σ⟧))

noncomputable instance [AddCommMonoidWithOne R] : AddCommMonoidWithOne (MvLaurentSeries σ R) :=
  inferInstanceAs (AddCommMonoidWithOne (R⟦SumOrder σ⟧))

noncomputable instance [NonUnitalNonAssocSemiring R] : Distrib (MvLaurentSeries σ R) :=
  inferInstanceAs (Distrib (R⟦SumOrder σ⟧))

noncomputable instance [NonUnitalNonAssocSemiring R] : Mul (MvLaurentSeries σ R) :=
  inferInstanceAs (Mul (R⟦SumOrder σ⟧))

noncomputable instance [NonUnitalNonAssocSemiring R] :
    NonUnitalNonAssocSemiring (MvLaurentSeries σ R) :=
  inferInstanceAs (NonUnitalNonAssocSemiring (R⟦SumOrder σ⟧))

noncomputable instance [AddCommGroupWithOne R] : AddCommGroupWithOne (MvLaurentSeries σ R) :=
  inferInstanceAs (AddCommGroupWithOne (R⟦SumOrder σ⟧))

noncomputable instance [NonAssocSemiring R] : NonAssocSemiring (MvLaurentSeries σ R) :=
  inferInstanceAs (NonAssocSemiring (R⟦SumOrder σ⟧))

noncomputable instance [NonUnitalNonAssocRing R] : NonUnitalNonAssocRing (MvLaurentSeries σ R) :=
  inferInstanceAs (NonUnitalNonAssocRing (R⟦SumOrder σ⟧))

noncomputable instance [NonUnitalSemiring R] : NonUnitalSemiring (MvLaurentSeries σ R) :=
  inferInstanceAs (NonUnitalSemiring (R⟦SumOrder σ⟧))

noncomputable instance [NonAssocRing R] : NonAssocRing (MvLaurentSeries σ R) :=
  inferInstanceAs (NonAssocRing (R⟦SumOrder σ⟧))

noncomputable instance [NonUnitalCommSemiring R] : NonUnitalCommSemiring (MvLaurentSeries σ R) :=
  inferInstanceAs (NonUnitalCommSemiring (R⟦SumOrder σ⟧))

noncomputable instance [NonUnitalRing R] : NonUnitalRing (MvLaurentSeries σ R) :=
  inferInstanceAs (NonUnitalRing (R⟦SumOrder σ⟧))

noncomputable instance [Semiring R] : Semiring (MvLaurentSeries σ R) :=
  inferInstanceAs (Semiring (R⟦SumOrder σ⟧))

noncomputable instance [CommSemiring R] : CommSemiring (MvLaurentSeries σ R) :=
  inferInstanceAs (CommSemiring (R⟦SumOrder σ⟧))

noncomputable instance [NonUnitalCommRing R] : NonUnitalCommRing (MvLaurentSeries σ R) :=
  inferInstanceAs (NonUnitalCommRing (R⟦SumOrder σ⟧))

noncomputable instance [Ring R] : Ring (MvLaurentSeries σ R) :=
  inferInstanceAs (Ring (R⟦SumOrder σ⟧))

noncomputable instance [CommRing R] : CommRing (MvLaurentSeries σ R) :=
  inferInstanceAs (CommRing (R⟦SumOrder σ⟧))

end Instances

/-! ### Basic definitions: coefficients and monomials -/

/-- The coefficient of `m` in a Laurent series. -/
def coeff [Zero R] (f : MvLaurentSeries σ R) (m : SumOrder σ) : R :=
  HahnSeries.coeff f m

@[simp] theorem hahnSeriesCoeff_eq_coeff [Zero R] :
    HahnSeries.coeff (Γ := SumOrder σ) (R := R) = coeff := rfl

@[ext] theorem ext [Zero R] {f g : MvLaurentSeries σ R} (h : ∀ m, f.coeff m = g.coeff m) : f = g :=
  HahnSeries.ext <| funext h

@[simp, grind =]
theorem coeff_zero [Zero R] {m : SumOrder σ} : (0 : MvLaurentSeries σ R).coeff m = 0 := rfl

@[simp, grind =]
theorem coeff_add [AddMonoid R] {f g : MvLaurentSeries σ R} {m : SumOrder σ} :
    (f + g).coeff m = f.coeff m + g.coeff m := rfl

@[simp, grind =]
theorem coeff_neg [NegZeroClass R] {f : MvLaurentSeries σ R} {m : SumOrder σ} :
    (-f).coeff m = -f.coeff m := rfl

@[simp, grind =]
theorem coeff_sub [AddGroup R] {f g : MvLaurentSeries σ R} {m : SumOrder σ} :
    (f - g).coeff m = f.coeff m - g.coeff m := rfl

theorem coeff_one [Zero R] [One R] {m : SumOrder σ} : (1 : MvLaurentSeries σ R).coeff m =
    if m = 0 then 1 else 0 := by
  convert HahnSeries.coeff_one
  all_goals rfl

theorem coeff_mul [NonUnitalNonAssocSemiring R] {f g : MvLaurentSeries σ R} {m : SumOrder σ} :
    (f * g).coeff m = ∑ ij ∈ Finset.addAntidiagonal f.isPWO_support g.isPWO_support m,
      f.coeff ij.fst * g.coeff ij.snd := rfl

/-- The add monoid homomorphism that extracts the coefficient of `m`. -/
def coeffAddHom [AddMonoid R] (m : SumOrder σ) : MvLaurentSeries σ R →+ R :=
  HahnSeries.coeff.addMonoidHom m

theorem coeffAddHom_apply [AddMonoid R] {m : SumOrder σ} {f : MvLaurentSeries σ R} :
    coeffAddHom m f = f.coeff m := rfl

/-- The linear map that extracts the coefficient of `m`. -/
def coeffLinearMap (R : Type*) {V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    (m : SumOrder σ) : MvLaurentSeries σ V →ₗ[R] V :=
  HahnSeries.coeff.linearMap m

@[simp] theorem coe_coeffLinearMap {V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    (m : SumOrder σ) : ⇑(coeffLinearMap R (V := V) m) = (coeff · m) := rfl

@[simp] theorem coeff_mk {R σ : Type*} [Zero R] (f hf i) :
    coeff (σ := σ) (R := R) ⟨f, hf⟩ i = f i := rfl

@[simp] theorem coeff_smul {R σ α : Type*} [Zero R] [SMulZeroClass α R]
    (x : α) (f : MvLaurentSeries σ R) : coeff (x • f) = x • coeff f := rfl

/-- `monomial i r` is the multivariate Laurent series with coefficient `r` at multi-index `i`. -/
noncomputable def monomial {R σ : Type*} [Semiring R] (i : SumOrder σ) :
    R →ₗ[R] MvLaurentSeries σ R where
  toFun := HahnSeries.single i
  map_add' x y := HahnSeries.single_add i x y
  map_smul' := by simp [HahnSeries.single, -smul_eq_mul, Pi.single_smul, MvLaurentSeries.ext_iff]

@[simp] theorem coeff_mul_monomial {R σ : Type*} [Semiring R]
    (i : SumOrder σ) (r : R) (p : MvLaurentSeries σ R) (j : SumOrder σ) :
    (p * monomial i r).coeff j = p.coeff (j - i) * r :=
  HahnSeries.coeff_mul_single

theorem coeff_mul_monomial_add
    {R σ : Type*} [Semiring R] (p : MvLaurentSeries σ R) (i j : SumOrder σ) (r : R) :
    (p * monomial j r).coeff (i + j) = p.coeff i * r :=
  HahnSeries.coeff_mul_single_add

/-! ### Support -/

/-- The support of a Laurent series. -/
def support [Zero R] (f : MvLaurentSeries σ R) : Set (SumOrder σ) :=
  HahnSeries.support f

theorem isPWO_support [Zero R] (f : MvLaurentSeries σ R) : (support f).IsPWO := f.2

@[grind =] theorem mem_support_iff [Zero R] {f : MvLaurentSeries σ R} {m : SumOrder σ} :
    m ∈ support f ↔ coeff f m ≠ 0 := Iff.rfl

@[grind! .] theorem support_add_subset [AddMonoid R] {f g : MvLaurentSeries σ R} :
    support (f + g) ⊆ support f ∪ support g := HahnSeries.support_add_subset f g

@[simp, grind =] theorem support_zero [Zero R] :
    support (0 : MvLaurentSeries σ R) = ∅ := HahnSeries.support_zero

@[simp, grind =, grind .] theorem support_eq_empty [Zero R] {f : MvLaurentSeries σ R} :
    support f = ∅ ↔ f = 0 := HahnSeries.support_eq_empty_iff

@[grind =] theorem support_neg [AddGroup R] (f : MvLaurentSeries σ R) :
    support (-f) = support f := HahnSeries.support_neg

@[grind! .] theorem support_smul {V : Type*} [Zero V] [SMulZeroClass R V]
    {f : MvLaurentSeries σ V} {r : R} :
    support (r • f) ⊆ support f := HahnSeries.support_smul_subset r f

open Pointwise in
@[grind .] theorem support_mul_subset [NonUnitalNonAssocSemiring R] {f g : MvLaurentSeries σ R} :
    support (f * g) ⊆ support f + support g := HahnSeries.support_mul_subset

theorem finite_degree_eq [Zero R] (f : MvLaurentSeries σ R) (n : ℤ) :
    {x | f.coeff x ≠ 0 ∧ x.degree = n}.Finite :=
  isAntichain_degree_eq σ n |>.subset (by grind) |>.isPWO_iff_finite |>.mp
    (isPWO_support f |>.mono (by grind))

/-! ### Degree coefficients -/

/-- For each total degree, the number of terms with that total degree is finite, so we extract it
as a `Finsupp`. -/
noncomputable def degreeCoeff [Zero R] (f : MvLaurentSeries σ R) (n : ℤ) : SumOrder σ →₀ R where
  toFun x := if x.degree = n then f.coeff x else 0
  support := finite_degree_eq f n |>.toFinset
  mem_support_toFun := by grind [Set.Finite.mem_toFinset]

@[grind =] theorem degreeCoeff_apply [Zero R] {f : MvLaurentSeries σ R} {n : ℤ} {x : SumOrder σ} :
    f.degreeCoeff n x = if x.degree = n then f.coeff x else 0 := rfl

@[grind =] theorem degreeCoeff_apply_of_eq [Zero R] {f : MvLaurentSeries σ R} {n : ℤ}
    {x : SumOrder σ} (h : x.degree = n) : f.degreeCoeff n x = f.coeff x := by grind

@[grind =] theorem degreeCoeff_apply_of_ne [Zero R] {f : MvLaurentSeries σ R} {n : ℤ}
    {x : SumOrder σ} (h : x.degree ≠ n) : f.degreeCoeff n x = 0 := by grind

theorem degreeCoeff_apply_degree [Zero R] {f : MvLaurentSeries σ R} {x : SumOrder σ} :
    f.degreeCoeff x.degree x = f.coeff x := by grind

/-- The add monoid homomorphism that extracts the total-degree coefficient of `n`. -/
noncomputable def degreeCoeffAddHom [AddCommMonoid R] (n : ℤ) :
    MvLaurentSeries σ R →+ SumOrder σ →₀ R where
  toFun f := f.degreeCoeff n
  map_zero' := by simp [Finsupp.ext_iff, degreeCoeff_apply]
  map_add' f g := by simp [Finsupp.ext_iff]; grind

/-! ### Valuation -/

/-- The valuation of a Laurent series is the minimum total degree of the monomials.

`0` is sent to `⊥ = -∞`. -/
noncomputable def val [Zero R] (f : MvLaurentSeries σ R) : WithBot ℤ :=
  open scoped Classical in if h : f = 0 then ⊥ else
    f.isPWO_support.image_of_monotone degree_mono |>.isWF |>.min <| by
      simpa [Set.image_nonempty, Set.nonempty_iff_ne_empty]

@[simp, grind =] theorem val_eq_bot_iff [Zero R] {f : MvLaurentSeries σ R} : f.val = ⊥ ↔ f = 0 := by
  simp [val]

/-- The valuation of a Laurent series is the minimum total degree of the monomials.

`0` is sent to the junk value `0`. -/
noncomputable def valInt [Zero R] (f : MvLaurentSeries σ R) : ℤ :=
  f.val.getD 0

theorem coe_valInt [Zero R] {f : MvLaurentSeries σ R} (hf : f ≠ 0) :
    (f.valInt : WithBot ℤ) = f.val := by
  unfold valInt
  generalize hv : f.val = v
  cases v with
  | bot => grind
  | coe v => simp [Option.getD]

theorem val_le_degree [Zero R] {f : MvLaurentSeries σ R} {x : SumOrder σ}
    (hfx : f.coeff x ≠ 0) : f.val ≤ x.degree := by
  rw [val, dif_neg (by grind), WithBot.coe_le_coe]
  exact Set.IsWF.min_le _ _ (by grind)

theorem valInt_le_degree [Zero R] {f : MvLaurentSeries σ R} {x : SumOrder σ}
    (hfx : f.coeff x ≠ 0) : f.valInt ≤ x.degree := by
  rw [← WithBot.coe_le_coe, coe_valInt (by grind)]
  exact val_le_degree hfx

/-! ### Order subgroups and topology -/

/-- The subgroup of Laurent series of order at least `n`. -/
def orderSubgroup (σ R : Type*) [AddGroup R] (n : ℤ) : AddSubgroup (MvLaurentSeries σ R) where
  carrier := {f | ∀ m ∈ support f, n ≤ m.degree}
  zero_mem' := by simp
  add_mem' hf hg m hm := by grind
  neg_mem' hf m hm := by grind

@[grind =] theorem mem_orderSubgroup [AddGroup R] {f : MvLaurentSeries σ R} {n : ℤ} :
    f ∈ orderSubgroup σ R n ↔ ∀ m ∈ support f, n ≤ m.degree := Iff.rfl

variable (σ R) in
theorem iInf_orderSubgroup [AddGroup R] : ⨅ n, orderSubgroup σ R n = ⊥ := by
  simp [AddSubgroup.eq_bot_iff_forall, mem_orderSubgroup, MvLaurentSeries.ext_iff,
    mem_support_iff, forall_comm (α := ℤ), ← IsTop.eq_1]

@[grind =] theorem sub_mem_orderSubgroup [AddGroup R] {f g : MvLaurentSeries σ R} {n : ℤ} :
    f - g ∈ orderSubgroup σ R n ↔ ∀ x, x.degree < n → f.coeff x = g.coeff x := by
  simp [mem_orderSubgroup, mem_support_iff, ← coeffAddHom_apply, sub_eq_zero]
  grind

@[grind =] theorem mem_orderSubgroup_iff_degreeCoeff
    [AddGroup R] {f : MvLaurentSeries σ R} {n : ℤ} :
    f ∈ orderSubgroup σ R n ↔ ∀ m < n, f.degreeCoeff m = 0 := by
  simp [Finsupp.ext_iff, degreeCoeff_apply]
  grind

@[grind .] theorem orderSubgroup_anti [AddGroup R] {n m : ℤ} (h : n ≤ m) :
    orderSubgroup σ R m ≤ orderSubgroup σ R n := fun _ _ ↦ by grind

theorem exists_mem_orderSubgroup [AddGroup R] (f : MvLaurentSeries σ R) :
    ∃ n, f ∈ orderSubgroup σ R n := by
  obtain h₁ | h₁ := f.support.eq_empty_or_nonempty
  · exact ⟨0, by simp [support_eq_empty.mp h₁]⟩
  have h₂ := Set.isPWO_iff_isWF.mp <| f.isPWO_support.image_of_monotone degree_mono
  use h₂.min <| Set.image_nonempty.mpr h₁
  exact fun m hm ↦ Set.IsWF.min_le _ _ <| Set.mem_image_of_mem _ hm

@[grind →] theorem mul_mem_orderSubgroup [Ring R] {f g : MvLaurentSeries σ R} {m n : ℤ}
    (hf : f ∈ orderSubgroup σ R m) (hg : g ∈ orderSubgroup σ R n) :
    f * g ∈ orderSubgroup σ R (m + n) := fun _p hp ↦ by
  obtain ⟨a, ha, b, hb, rfl⟩ := support_mul_subset hp
  rw [map_add]
  exact add_le_add (hf a ha) (hg b hb)

open scoped Pointwise in
theorem orderSubgroup_mul [Ring R] {m n : ℤ} :
    orderSubgroup σ R m * orderSubgroup σ R n ≤ orderSubgroup σ R (m + n) := by grind

theorem boundedRingSubgroupsBasis_orderSubgroup [Ring R] :
    BoundedRingSubgroupsBasis (orderSubgroup σ R) := .of_covers
  (fun i j ↦ ⟨max i j,
    le_inf (orderSubgroup_anti (le_max_left i j)) (orderSubgroup_anti (le_max_right i j))⟩)
  (fun k i ↦ ⟨i - k, AddSubgroup.mul_le_iff_coe.mp <| by
    simpa using orderSubgroup_mul (m := k) (n := i - k)⟩)
  (fun k i ↦ ⟨i - k, AddSubgroup.mul_le_iff_coe.mp <| by
    simpa using orderSubgroup_mul (m := i - k) (n := k)⟩)
  exists_mem_orderSubgroup

theorem ringSubgroupsBasis_orderSubgroup [Ring R] :
    RingSubgroupsBasis (orderSubgroup σ R) :=
  boundedRingSubgroupsBasis_orderSubgroup.toRingSubgroupsBasis

noncomputable instance [Ring R] : UniformSpace (MvLaurentSeries σ R) :=
  ringSubgroupsBasis_orderSubgroup.toRingFilterBasis.uniformSpace

open Filter Topology

theorem hasBasis_nhds_zero [Ring R] :
    HasBasis (𝓝 (0 : MvLaurentSeries σ R)) (fun _ ↦ True) (orderSubgroup σ R ·) :=
  ringSubgroupsBasis_orderSubgroup.hasBasis_nhds_zero

theorem hasBasis_nhds_zero_nat [Ring R] :
    HasBasis (𝓝 (0 : MvLaurentSeries σ R)) (fun _ : ℕ ↦ True) (orderSubgroup σ R ·) :=
  ringSubgroupsBasis_orderSubgroup.hasBasis_nhds_zero.to_hasBasis
    (fun i _ ↦ ⟨i.toNat, trivial, by grind [SetLike.coe_subset_coe]⟩)
    fun i _ ↦ ⟨i, trivial, le_rfl⟩

theorem isOpen_orderSubgroup [Ring R] {i} : IsOpen (ofClass% orderSubgroup σ R i) :=
  (ringSubgroupsBasis_orderSubgroup.openAddSubgroup i).2

instance [Ring R] : NonarchimedeanRing (MvLaurentSeries σ R) :=
  ringSubgroupsBasis_orderSubgroup.nonarchimedean

instance [Ring R] : StrongNonarchimedeanRing (MvLaurentSeries σ R) where
  exists_mul_subset_self U hu :=
    let ⟨i, _, hi⟩ := ringSubgroupsBasis_orderSubgroup.hasBasis_nhds_zero.mem_iff.mp hu
    ⟨orderSubgroup σ R i.toNat, zero_mem _, isOpen_orderSubgroup,
      le_trans (orderSubgroup_anti (by grind)) hi,
      AddSubgroup.mul_le_iff_coe.mp <| orderSubgroup_mul.trans <| by grind⟩

instance [Ring R] : IsUniformAddGroup (MvLaurentSeries σ R) :=
  AddGroupFilterBasis.isUniformAddGroup _

theorem hasBasis_nhds [Ring R] {f} :
    (𝓝 f).HasBasis (fun _ ↦ True) ({g | g - f ∈ orderSubgroup σ R ·}) :=
  ringSubgroupsBasis_orderSubgroup.hasBasis_nhds f

open Uniformity

theorem hasBasis_uniformity [Ring R] :
    HasBasis (𝓤 (MvLaurentSeries σ R)) (fun _ ↦ True) ({p | p.2 - p.1 ∈ orderSubgroup σ R ·}) :=
  hasBasis_nhds_zero.uniformity_of_nhds_zero

theorem hasBasis_uniformity_nat [Ring R] :
    HasBasis (𝓤 (MvLaurentSeries σ R))
      (fun _ : ℕ ↦ True) ({p | p.2 - p.1 ∈ orderSubgroup σ R ·}) :=
  hasBasis_nhds_zero_nat.uniformity_of_nhds_zero

instance [Ring R] : CompleteSpace (MvLaurentSeries σ R) where
  complete {a} ha := by
    obtain ⟨ha1, ha2⟩ := by rwa [hasBasis_uniformity.cauchy_iff] at ha
    simp only [Set.mem_setOf_eq, forall_const] at ha2
    choose s hsa hs using ha2
    have key (i) := a.nonempty_of_mem (hsa i)
    choose f hf using key
    have agree m n (hmn : m ≤ n) : f n - f m ∈ orderSubgroup σ R m :=
      let ⟨x, hxm, hxn⟩ := a.nonempty_of_mem <| a.inter_mem (hsa m) (hsa n)
      sub_add_sub_cancel (f n) x (f m) ▸ add_mem (orderSubgroup_anti hmn <| by grind) (by grind)
    simp_rw [sub_mem_orderSubgroup] at hs agree
    by_cases h₀ : ∀ x, (f (x.degree + 1)).coeff x = 0
    · refine ⟨0, hasBasis_nhds_zero.ge_iff.mpr fun i _ ↦ a.mem_of_superset (hsa i) fun x hx p hp ↦
        le_of_not_gt fun h ↦ mem_support_iff.mp hp ?_⟩
      rw [← hs _ _ hx _ (hf i) p h, agree _ _ (by grind) _ (by grind), h₀]
    obtain ⟨A, hA⟩ := not_forall.mp h₀
    have bdd (x) (hx : (f (x.degree + 1)).coeff x ≠ 0) :
        (f (A.degree + 1)).valInt ≤ x.degree := by
      obtain h | h := lt_or_ge x.degree A.degree
      · exact valInt_le_degree <| by rwa [agree (x.degree + 1) _ (by grind) _ (by grind)]
      · exact le_trans (valInt_le_degree hA) h
    use { coeff x := (f <| x.degree + 1).coeff x
          isPWO_support' := isPWO_iff.mpr ⟨(f (A.degree + 1)).valInt, bdd, fun n ↦ by
            convert finite_degree_eq (f (n + 1)) n using 2
            grind [Function.support]⟩ }
    refine hasBasis_nhds.ge_iff.mpr fun i _ ↦ a.mem_of_superset (hsa i) fun x hx ↦
      sub_mem_orderSubgroup.mpr fun p hpi ↦ ?_
    rw [← hs _ _ hx _ (hf i) _ hpi, agree (p.degree + 1) _ (by grind) _ (by grind)]
    rfl

instance [Ring R] : IsSubgroupsBasis (orderSubgroup σ R) where
  hasBasis_nhds_zero := hasBasis_nhds_zero

instance [Ring R] : T2Space (MvLaurentSeries σ R) := by
  let B := ringSubgroupsBasis_orderSubgroup (σ := σ) (R := R)
  rw [B.toRingFilterBasis.toAddGroupFilterBasis.t2Space_iff_sInter_subset rfl]
  simpa [AddSubgroup.eq_bot_iff_forall] using iInf_orderSubgroup σ R

instance [Ring R] : T3Space (MvLaurentSeries σ R) := inferInstance

/-! ### The monomial `xPow` -/

/-- The monomial `xᵢⁿ` in a multivariate Laurent series ring. -/
noncomputable def xPow
    {R σ : Type*} [Zero R] [One R] (i : σ) (n : ℤ) : MvLaurentSeries σ R :=
  .single (.of <| .single i n) 1

theorem coeff_xPow {R σ : Type*} [Zero R] [One R] (i : σ) (n : ℤ) (v : SumOrder σ) :
    (xPow (R := R) i n).coeff v = if v = (.of <| .single i n) then 1 else 0 := by
  convert HahnSeries.coeff_single
  all_goals rfl

@[simp] theorem coeff_xPow_single {R σ : Type*} [Zero R] [One R] (i : σ) (n : ℤ) :
    (xPow (R := R) i n).coeff (.of <| .single i n) = 1 := by simp [coeff_xPow]

@[simp] theorem xPow_zero {R σ : Type*} [Zero R] [One R] (i : σ) :
    xPow (R := R) i 0 = 1 := by
  simp [xPow]

theorem xPow_add {R σ : Type*} [Semiring R] (i : σ) (n m : ℤ) :
    xPow (R := R) i (n + m) = xPow (R := R) i n * xPow (R := R) i m := by
  rw [xPow, xPow, xPow, HahnSeries.single_mul_single, ← map_add, Finsupp.single_add]
  simp

theorem xPow_pow {R σ : Type*} [Semiring R] (i : σ) (n : ℤ) (m : ℕ) :
    xPow (R := R) i n ^ m = xPow (R := R) i (n * m) := by
  rw [xPow, xPow, HahnSeries.single_pow, ← map_nsmul, Finsupp.smul_single]
  simp [mul_comm]

/-- `xPow i n` as a unit, with inverse `xPow i (-n)`. -/
@[simps] noncomputable def xPowUnits
    {R σ : Type*} [Semiring R] (i : σ) (n : ℤ) : (MvLaurentSeries σ R)ˣ where
  val := xPow i n
  inv := xPow i (-n)
  val_inv := by simp [← xPow_add]
  inv_val := by simp [← xPow_add]

theorem xPowUnits_zpow {R σ : Type*} [Semiring R] (i : σ) (n m : ℤ) :
    xPowUnits (R := R) i n ^ m = xPowUnits (R := R) i (n * m) := by
  ext : 1
  obtain ⟨m, rfl | rfl⟩ := m.eq_nat_or_neg <;> simp [xPow_pow]

@[simp] theorem xPow_mem_orderSubgroup_iff
    {R σ : Type*} [Ring R] [Nontrivial R] (i : σ) (n m : ℤ) :
    xPow i n ∈ orderSubgroup σ R m ↔ m ≤ n := by
  simp [mem_orderSubgroup, mem_support_iff, xPow, coeff, HahnSeries.coeff_single]

@[simp] theorem isTopologicallyNilpotent_xPow_iff
    {R σ : Type*} [Ring R] [Nontrivial R] (i : σ) (n : ℤ) :
    IsTopologicallyNilpotent (xPow (R := R) i n) ↔ 0 < n := by
  suffices (∀ (ib : ℕ), ∃ ia : ℕ, ∀ x, ia ≤ x → ib ≤ n * x) ↔ 0 < n by
    simpa [IsTopologicallyNilpotent, xPow_pow, atTop_basis.tendsto_iff hasBasis_nhds_zero_nat]
  refine ⟨fun h ↦ let ⟨a, ha⟩ := h 1; pos_of_mul_pos_left (by have := ha a; omega) a.cast_nonneg,
    fun h b ↦ ?_⟩
  lift n to ℕ using h.le
  exact ⟨b, fun a ha ↦ by grw [← ha, ← show 1 ≤ (n : ℤ) by grind, one_mul]⟩

@[simp] theorem monomial_single {R σ : Type*} [Semiring R] (i : σ) (n : ℤ) :
    monomial (R := R) (.of (.single i n)) 1 = xPow i n := rfl

@[simp] theorem coeff_mul_xPow {R σ : Type*} [Semiring R]
    (i : σ) (n : ℤ) (p : MvLaurentSeries σ R) (j : SumOrder σ) :
    (p * xPow i n).coeff j = p.coeff (j - .of (.single i n)) := by simp [← monomial_single]

theorem xPow_natCast {R σ : Type*} [Semiring R] (i : σ) (n : ℕ) :
    xPow (R := R) i n = xPow i 1 ^ n := by simp [xPow_pow]

/-! ### Pushforward: `mapVar` -/

/-- Pushforward ring homomorphism on multivariate Laurent series along an injection of
variables. -/
noncomputable def mapVar (R : Type*) [Semiring R] {σ τ : Type*} (f : σ ↪ τ) :
    MvLaurentSeries σ R →+* MvLaurentSeries τ R :=
  HahnSeries.embDomainRingHom (SumOrder.map f) (SumOrder.map_injective f.injective) <| by
    simp [SumOrder.map_le_iff f.injective]

theorem mapVar_injective {R σ τ : Type*} [Semiring R] (f : σ ↪ τ) :
    (⇑(mapVar R f)).Injective := HahnSeries.embDomain_injective

@[simp] theorem coeff_mapVar_map {R σ τ : Type*} [Semiring R] (f : σ ↪ τ)
    (p : MvLaurentSeries σ R) (i : SumOrder σ) :
    (mapVar R f p).coeff (i.map f) = p.coeff i := HahnSeries.embDomain_coeff

@[simp] theorem coeff_mapVar_eq_zero_of
    {R σ τ : Type*} [Semiring R] (f : σ ↪ τ) (p : MvLaurentSeries σ R)
    {i : SumOrder τ} (hi : ¬(i.support : Set τ) ⊆ Set.range f) :
    (mapVar R f p).coeff i = 0 := HahnSeries.embDomain_notin_range (by simpa using hi)

@[simp] theorem mapVar_monomial {R σ τ : Type*} [Semiring R] (f : σ ↪ τ) (i : SumOrder σ) (r : R) :
    (monomial i r).mapVar R f = monomial (i.map f) r := HahnSeries.embDomain_single

@[simp] theorem mapVar_xPow {R σ τ : Type*} [Semiring R] (f : σ ↪ τ) (i : σ) (n : ℤ) :
    (xPow i n).mapVar R f = xPow (f i) n := by simp [← monomial_single, SumOrder.map]

@[simp] theorem support_mapVar
    {R σ τ : Type*} [Semiring R] (f : σ ↪ τ) (p : MvLaurentSeries σ R) :
    (p.mapVar R f).support = SumOrder.map f '' p.support := by
  ext i
  simp_rw [mem_support_iff]
  by_cases hi : i ∈ Set.range (SumOrder.map f)
  · obtain ⟨i, rfl⟩ := hi
    simp [(SumOrder.map_injective f.injective).eq_iff, mem_support_iff]
  · simp_rw [(Set.image_subset_range _ _).mt hi]
    simp only [SumOrder.range_map, Set.mem_setOf_eq] at hi
    simp [hi]

@[fun_prop] theorem mapVar_continuous {R σ τ : Type*} [Ring R] (f : σ ↪ τ) :
    Continuous (mapVar R f) := continuous_of_continuousAt_zero _ <| by
  rw [ContinuousAt, map_zero, hasBasis_nhds_zero_nat.tendsto_iff hasBasis_nhds_zero_nat]
  simpa [mem_orderSubgroup] using fun n ↦ ⟨n, fun _ ↦ id⟩

/-! ### Coefficient extraction: `comapVar` -/

/-- Coefficient extraction: `comapVar R f v` sends a `τ`-variate Laurent series to a `σ`-variate
one by reading off the coefficient of the monomial `v` in the complement variables.
Satisfies `comapVar R f v (mapVar R f p * monomial v 1) = p`. -/
noncomputable def comapVar (R : Type*) [Semiring R] {σ τ : Type*} (f : σ ↪ τ) (v : SumOrder τ) :
    MvLaurentSeries τ R →ₗ[R] MvLaurentSeries σ R where
  toFun p :=
  { coeff i := p.coeff (i.map f + v)
    isPWO_support' := .of_image (.comp (SumOrder.mapEmbedding f) (.addRight' v)) <| by
      convert p.isPWO_support.mono (s := {y ∈ p.support | ∃ x, SumOrder.map f x + v = y}) (by grind)
      simp [Set.ext_iff]
      grind }
  map_add' := by simp [MvLaurentSeries.ext_iff]
  map_smul' := by simp [MvLaurentSeries.ext_iff]

@[simp] theorem coeff_comapVar {R σ τ : Type*} [Semiring R] (f : σ ↪ τ) (v : SumOrder τ)
    (p : MvLaurentSeries τ R) (i : SumOrder σ) :
    coeff (comapVar R f v p) i = p.coeff (i.map f + v) := rfl

@[simp] theorem comapVar_mapVar_mul_monomial
    {R σ τ : Type*} [Semiring R] (f : σ ↪ τ) (v : SumOrder τ) (p : MvLaurentSeries σ R) :
    comapVar R f v (mapVar R f p * monomial v 1) = p := by
  ext; simp

@[simp] theorem comapVar_mapVar_mul_xPow {R σ τ : Type*} [Semiring R]
    (f : σ ↪ τ) (i : τ) (n : ℤ) (p : MvLaurentSeries σ R) :
    comapVar R f (.of <| .single i n) (mapVar R f p * xPow i n) = p := by
  simp [← monomial_single]

theorem comapVar_mapVar_mul_xPow_eq_ite {R σ τ : Type*} [Semiring R]
    (f : σ ↪ τ) (i : τ) (hi : i ∉ Set.range f) (m n : ℤ) (p : MvLaurentSeries σ R) :
    comapVar R f (.of <| .single i m) (mapVar R f p * xPow i n) = if m = n then p else 0 := by
  by_cases h : m = n
  · simp [h]
  ext j
  simp only [coeff_comapVar, coeff_mul_xPow, h, ↓reduceIte]
  exact coeff_mapVar_eq_zero_of _ _ <| Set.not_subset.mpr ⟨i, by
    classical simpa [finsupp_apply, hi, SumOrder.of_single_apply, sub_eq_zero]⟩

@[simp] theorem support_comapVar
    {R σ τ : Type*} [Semiring R] (f : σ ↪ τ) (v : SumOrder τ) (p : MvLaurentSeries τ R) :
    (comapVar R f v p).support = (·.map f + v) ⁻¹' p.support := by
  ext
  simp [mem_support_iff]

@[fun_prop] theorem comapVar_continuous {R σ τ : Type*} [Ring R] (f : σ ↪ τ) (v : SumOrder τ) :
    Continuous (comapVar R f v) := continuous_of_continuousAt_zero _ <| by
  rw [ContinuousAt, map_zero, hasBasis_nhds_zero.tendsto_iff hasBasis_nhds_zero]
  simpa [mem_orderSubgroup] using fun n ↦ ⟨n + v.degree, fun p hp x hx ↦
    (add_le_add_iff_right v.degree).mp <| by grw [hp _ hx, map_add, SumOrder.degree_map]⟩

end MvLaurentSeries
