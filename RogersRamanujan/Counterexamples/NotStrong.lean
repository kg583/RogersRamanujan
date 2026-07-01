module

import RogersRamanujan.Algebra.BigOperators.Intervals
public import RogersRamanujan.Analysis.LocallyConvex.WithSeminorms
import RogersRamanujan.Analysis.Normed.Group.Ultra
public import RogersRamanujan.NumberTheory.Padics.PadicNumbers
import RogersRamanujan.NumberTheory.QTheory.Basic
public import RogersRamanujan.NumberTheory.QTheory.Defs
import RogersRamanujan.Topology.Algebra.InfiniteSum.Nonarchimedean
public import RogersRamanujan.Topology.Algebra.Nonarchimedean.Strong
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.UniformFilterBasis

/-! # A nonarchimedean ring that is not strongly nonarchimedean

We construct a Frechet-type space of sequences in `ℚ_p` where the topology is nonarchimedean but
not strongly nonarchimedean.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace NotStrong

variable {p : ℕ} [Fact p.Prime]
open Real Filter Topology QTheory

/-- The weighted coordinate seminorm used to define the Frechet-type counterexample space. -/
noncomputable def frechet (N : ℕ+) (x : ℕ → ℚ_[p]) (n : ℕ) : ℝ :=
  ‖x n‖ * p ^ (- n ^ 3 / N : ℝ)

@[bound] theorem frechet_nonneg (N : ℕ+) (x : ℕ → ℚ_[p]) (n : ℕ) : 0 ≤ frechet N x n := by
  unfold frechet
  positivity

theorem frechet_add_le (N : ℕ+) (x y : ℕ → ℚ_[p]) (n : ℕ) :
    frechet N (x + y) n ≤ max (frechet N x n) (frechet N y n) := by
  unfold frechet
  grw [← max_mul_of_nonneg _ _ (by positivity), Pi.add_apply, Padic.nonarchimedean]

theorem frechet_mul (N : ℕ+) (x y : ℕ → ℚ_[p]) (n : ℕ) :
    frechet N (x * y) n = frechet (2 * N) x n * frechet (2 * N) y n := by
  unfold frechet
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  simp_rw [Pi.mul_apply, mul_mul_mul_comm, ← rpow_add hp, ← norm_mul,
    show ((2 * N : ℕ+) : ℝ) = 2 * (N : ℝ) by norm_num, div_mul_eq_div_div_swap, add_halves]

@[simp] theorem frechet_neg (N : ℕ+) (x : ℕ → ℚ_[p]) (n : ℕ) :
    frechet N (-x) n = frechet N x n := by simp [frechet]

theorem frechet_sub_le (N : ℕ+) (x y : ℕ → ℚ_[p]) (n : ℕ) :
    frechet N (x - y) n ≤ max (frechet N x n) (frechet N y n) := by
  grw [sub_eq_add_neg, frechet_add_le, frechet_neg]

@[simp] theorem frechet_smul (N : ℕ+) (a : ℚ_[p]) (x : ℕ → ℚ_[p]) (n : ℕ) :
    frechet N (a • x) n = ‖a‖ * frechet N x n := by simp [frechet, mul_assoc]

variable (p) in
theorem frechet_one_le (N : ℕ+) (n : ℕ) :
    frechet (p := p) N 1 n ≤ 1 := by
  simpa [frechet] using rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast (Fact.out : p.Prime).one_le)
    (div_nonpos_of_nonpos_of_nonneg (by simp) (by simp))

variable (p) in
@[simp] theorem frechet_zero (N : ℕ+) (n : ℕ) : frechet N (0 : ℕ → ℚ_[p]) n = 0 := by simp [frechet]

@[simp] theorem frechet_eq_zero_iff (N : ℕ+) (x : ℕ → ℚ_[p]) (n : ℕ) :
    frechet N x n = 0 ↔ x n = 0 := by
  simp [frechet, rpow_eq_zero_iff_of_nonneg, (Fact.out : p.Prime).ne_zero]

variable (p)

/-- The subalgebra of `ℕ → ℚ_[p]` on which all weighted coordinate seminorms are bounded. -/
def frechetSubalgebra : Subalgebra ℚ_[p] (ℕ → ℚ_[p]) where
  carrier := {x | ∀ N : ℕ+, ∃ M : ℝ, ∀ n, frechet N x n ≤ M}
  zero_mem' N := ⟨0, fun n ↦ by simp [frechet]⟩
  add_mem' hx hy N :=
    let ⟨Mx, hxM⟩ := hx N
    let ⟨My, hyM⟩ := hy N
    ⟨max Mx My, fun n ↦ (frechet_add_le ..).trans <| max_le_max (hxM n) (hyM n)⟩
  mul_mem' {x y} hx hy N :=
    let ⟨Mx, hMx⟩ := hx (2 * N)
    let ⟨My, hMy⟩ := hy (2 * N)
    ⟨Mx * My, fun n ↦ frechet_mul N x y n ▸ mul_le_mul (hMx n) (hMy n)
      (frechet_nonneg (2 * N) y n) ((frechet_nonneg (2 * N) x n).trans (hMx n))⟩
  algebraMap_mem' x N := by
    refine ⟨‖x‖, fun n ↦ ?_⟩
    grw [Algebra.algebraMap_eq_smul_one, frechet_smul, frechet_one_le, mul_one]

/-- The Frechet-type `ℚ_[p]`-algebra used to witness failure of strong nonarchimedeanity. -/
def FrechetSpace (p : ℕ) [Fact p.Prime] : Type :=
  { x : ℕ → ℚ_[p] // ∀ N : ℕ+, ∃ M : ℝ, ∀ n, frechet N x n ≤ M }

instance : CommRing (FrechetSpace p) := (frechetSubalgebra p).toCommRing
instance : Algebra ℚ_[p] (FrechetSpace p) := (frechetSubalgebra p).algebra

instance : FunLike (FrechetSpace p) ℕ ℚ_[p] where
  coe x := x.val
  coe_injective _ _ := Subtype.ext

namespace FrechetSpace

variable {p}

@[simp] theorem val_eq_coe (x : FrechetSpace p) : x.val = ⇑x := rfl

variable (p) in
@[simp] theorem coe_zero : ⇑(0 : FrechetSpace p) = 0 := rfl

@[simp] theorem coe_add (x y : FrechetSpace p) : ⇑(x + y) = ⇑x + ⇑y := rfl

@[simp] theorem coe_smul (a : ℚ_[p]) (x : FrechetSpace p) : ⇑(a • x) = a • ⇑x := rfl

@[simp] theorem coe_neg (x : FrechetSpace p) : ⇑(-x) = -⇑x := rfl

@[simp] theorem coe_one : ⇑(1 : FrechetSpace p) = 1 := rfl

@[simp] theorem coe_mul (x y : FrechetSpace p) : ⇑(x * y) = ⇑x * ⇑y := rfl

@[simp] theorem coe_sub (x y : FrechetSpace p) : ⇑(x - y) = ⇑x - ⇑y := rfl

@[simp] theorem coe_pow (x : FrechetSpace p) (n : ℕ) : ⇑(x ^ n) = ⇑x ^ n := rfl

@[simp] theorem coe_natCast (n : ℕ) : ⇑(n : FrechetSpace p) = n := rfl

@[simp] theorem coe_prod {ι : Type*} (s : Finset ι) (f : ι → FrechetSpace p) :
    ⇑(∏ i ∈ s, f i) = ∏ i ∈ s, ⇑(f i) := by
  classical induction s using Finset.induction_on <;> simp [*]

theorem bddAbove_range_frenchet (x : FrechetSpace p) (N : ℕ+) :
    BddAbove (Set.range (frechet N ⇑x)) := by simpa [bddAbove_def] using x.2 N

/-- The supremum seminorm induced by `frechet N` on `FrechetSpace p`. -/
noncomputable def norm (N : ℕ+) : Seminorm ℚ_[p] (FrechetSpace p) where
  toFun x := ⨆ n, frechet N x n
  map_zero' := by simp
  add_le' x y := ciSup_le fun n ↦ by
    grw [coe_add, frechet_add_le, max_le_add_of_nonneg (by bound) (by bound),
      le_ciSup (x.bddAbove_range_frenchet N) n, le_ciSup (y.bddAbove_range_frenchet N) n]
  neg' x := by simp
  smul' a x := by simp [Real.mul_iSup_of_nonneg]

theorem norm_def (x : FrechetSpace p) (N : ℕ+) : x.norm N = ⨆ n, frechet N x n := rfl

theorem frechet_le_norm (x : FrechetSpace p) (N : ℕ+) (n : ℕ) :
    frechet N x n ≤ x.norm N := le_ciSup (x.bddAbove_range_frenchet N) n

theorem norm_mul_le (x y : FrechetSpace p) (N : ℕ+) :
    (x * y).norm N ≤ x.norm (2 * N) * y.norm (2 * N) := ciSup_le fun n ↦ by
  grw [coe_mul, frechet_mul, frechet_le_norm, frechet_le_norm]
  bound

theorem norm_add_le_max (x y : FrechetSpace p) (N : ℕ+) :
    (x + y).norm N ≤ max (x.norm N) (y.norm N) := ciSup_le fun n ↦ by
  grw [coe_add, frechet_add_le, frechet_le_norm, frechet_le_norm]

@[simp] theorem norm_eq_zero_iff (x : FrechetSpace p) (N : ℕ+) :
    x.norm N = 0 ↔ x = 0 :=
  ⟨fun h ↦ DFunLike.ext _ _ fun n ↦ (frechet_eq_zero_iff N ..).mp <|
    (frechet_nonneg ..).antisymm' <| h ▸ x.frechet_le_norm .., by grind⟩

variable (p) in
/-- The family of seminorms generating the topology on `FrechetSpace p`. -/
noncomputable def seminormFamily : SeminormFamily ℚ_[p] (FrechetSpace p) ℕ+ := norm

@[simp] theorem seminormFamily_apply (N : ℕ+) : seminormFamily p N = norm N := rfl

noncomputable instance : UniformSpace (FrechetSpace p) :=
  (seminormFamily p).addGroupFilterBasis.uniformSpace

instance : IsUniformAddGroup (FrechetSpace p) :=
  (seminormFamily p).addGroupFilterBasis.isUniformAddGroup

noncomputable instance (priority := high) : TopologicalSpace (FrechetSpace p) := inferInstance

instance : IsTopologicalAddGroup (FrechetSpace p) :=
  (seminormFamily p).addGroupFilterBasis.isTopologicalAddGroup

variable (p) in
theorem withSeminorms : WithSeminorms (seminormFamily p) := ⟨rfl⟩

instance : NonarchimedeanAddGroup (FrechetSpace p) :=
  (withSeminorms p).nonarchimedeanAddGroup fun N ↦ (norm_add_le_max · · N)

instance : ContinuousSMul ℚ_[p] (FrechetSpace p) := (withSeminorms p).continuousSMul

variable (p) in
/-- The open ball of radius `ε` around `0` for the `N`-th seminorm on `FrechetSpace p`, as an
open additive subgroup. -/
noncomputable def openAddSubgroup (N : ℕ+) (ε : ℝ) (hε : 0 < ε) :
    OpenAddSubgroup (FrechetSpace p) :=
  (withSeminorms p).ballOpenAddSubgroup N (norm_add_le_max · · N) ε hε

@[simp] theorem mem_openAddSubgroup (N : ℕ+) (ε : ℝ) (hε : 0 < ε) (x : FrechetSpace p) :
    x ∈ openAddSubgroup p N ε hε ↔ x.norm N < ε := Iff.rfl

variable (p) in
theorem setOf_norm_lt_mem_nhds_zero (N : ℕ+) (ε : ℝ) (hε : 0 < ε) :
    {x : FrechetSpace p | x.norm N < ε} ∈ 𝓝 0 := (openAddSubgroup p N ε hε).mem_nhds_zero

variable (p) in
theorem uniformContinuous_norm (N : ℕ+) :
    UniformContinuous (norm (p := p) N) := (norm (p := p) N).uniformContinuous_of_forall <| by
  simpa [Seminorm.ball] using setOf_norm_lt_mem_nhds_zero p N

variable (p) in
theorem tendsto_mul_nhds_zero :
    Tendsto (fun x y : FrechetSpace p ↦ x * y).uncurry (𝓝 0 ×ˢ 𝓝 0) (𝓝 0) := by
  refine ((withSeminorms p).tendsto_nhds_zero ..).mpr fun N ε hε ↦ ?_
  have h₁ := setOf_norm_lt_mem_nhds_zero p (2 * N) (√ε) (by positivity)
  filter_upwards [prod_mem_prod h₁ h₁] with ⟨x, y⟩ ⟨hx, hy⟩
  dsimp
  grw [norm_mul_le, ← mul_self_sqrt hε.le]
  exact mul_lt_mul'' hx hy (by simp) (by simp)

variable (p) in
theorem tendsto_mul_nhds_zero_left (x : FrechetSpace p) :
    Tendsto (fun y : FrechetSpace p ↦ x * y) (𝓝 0) (𝓝 0) := by
  refine ((withSeminorms p).tendsto_nhds_zero ..).mpr fun N ε hε ↦ ?_
  by_cases hx : x.norm (2 * N) = 0
  · simp [-nhds_discrete, (norm_eq_zero_iff ..).mp hx, hε]
  have h₁ := setOf_norm_lt_mem_nhds_zero p (2 * N) (ε / x.norm (2 * N)) (by positivity)
  filter_upwards [h₁] with y hy
  grw [seminormFamily_apply, norm_mul_le]
  exact (lt_div_iff₀' (by positivity)).mp hy

instance : IsTopologicalRing (FrechetSpace p) := .of_addGroup_of_nhds_zero
  (tendsto_mul_nhds_zero p) (tendsto_mul_nhds_zero_left p)
  (by simpa [mul_comm] using tendsto_mul_nhds_zero_left p)

instance (priority := high) : ContinuousMul (FrechetSpace p) := inferInstance

instance : NonarchimedeanRing (FrechetSpace p) where
  __ := (inferInstance : NonarchimedeanAddGroup (FrechetSpace p))

variable (p) in
/-- Coordinate evaluation as a continuous linear map. -/
@[simps!] noncomputable def evalCLM (n : ℕ) : FrechetSpace p →L[ℚ_[p]] ℚ_[p] where
  __ := ((Pi.evalAlgHom ℚ_[p] (fun _ ↦ ℚ_[p]) n).comp (frechetSubalgebra p).val).toLinearMap
  cont := continuous_of_continuousAt_zero _ <|
    (NormedAddGroup.tendsto_nhds_zero ..).mpr fun ε hε ↦ by
    have hp : 0 < p := (Fact.out : p.Prime).pos
    have h₁ : 0 < (p : ℝ) ^ (-n ^ 3 : ℝ) := by positivity
    have h₂ := setOf_norm_lt_mem_nhds_zero p 1 (ε * p ^ (-n ^ 3 : ℝ)) (by positivity)
    filter_upwards [h₂] with x hx
    simp [Subalgebra.val]
    simpa [frechet, h₁] using (x.frechet_le_norm 1 n).trans_lt hx

/-- The coordinatewise limit of a filter on `FrechetSpace p`. -/
noncomputable def coordLimit (F : Filter (FrechetSpace p)) (n : ℕ) : ℚ_[p] :=
  lim (Filter.map (evalCLM p n) F)

/-- A Cauchy filter converges coordinatewise in `ℚ_[p]`. -/
theorem tendsto_coordLimit {F : Filter (FrechetSpace p)} (hF : Cauchy F) (n : ℕ) :
    Tendsto (fun x ↦ x n) F (𝓝 (coordLimit F n)) :=
  (hF.map (evalCLM p n).uniformContinuous).le_nhds_lim

theorem frechet_sub_coordLimit_le
    {F : Filter (FrechetSpace p)} (hF : Cauchy F) {ε : ℝ} (hε : 0 < ε) (N : ℕ+) :
    ∀ᶠ (x : FrechetSpace p) in F, ∀ n, frechet N (⇑x - coordLimit F) n ≤ ε := by
  have : 1 ≤ (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_le
  have := hF.1
  have h₁ := (IsUniformAddGroup.cauchy_iff_tendsto _).mp hF |>.2
    (setOf_norm_lt_mem_nhds_zero p N ε hε)
  have ⟨s, hsf, hsn⟩ := mem_prod_self_iff.mp h₁
  filter_upwards [hsf] with x hxs n
  have h₁ := tendsto_coordLimit hF n
    (Metric.ball_mem_nhds (coordLimit F n) (ε := ε * p ^ (n ^ 3 / N : ℝ)) (by positivity))
  let ⟨y, hys, hyn⟩ := nonempty_of_mem (inter_mem hsf h₁)
  grw [← sub_add_sub_cancel _ ⇑y, frechet_add_le, ← coe_sub, frechet_le_norm,
    show norm _ _ < _ from @hsn (x, y) ⟨hxs, hys⟩, frechet, Pi.sub_apply, mem_ball_iff_norm.mp hyn]
  simp [mul_assoc, ← rpow_add (by positivity : 0 < (p : ℝ)), neg_div]

/-- The coordinatewise limit of a Cauchy filter still lies in the Fréchet subalgebra. -/
theorem coordLimit_mem_frechetSubalgebra {F : Filter (FrechetSpace p)} (hF : Cauchy F) :
    coordLimit F ∈ frechetSubalgebra p := fun N ↦ by
  have := hF.1
  obtain ⟨x, hx⟩ := nonempty_of_mem (frechet_sub_coordLimit_le hF one_pos N)
  refine ⟨max (x.norm N) 1, fun n ↦ ?_⟩
  grw [← sub_sub_cancel ⇑x (coordLimit F), frechet_sub_le, frechet_le_norm, hx n]

/-- The canonical limit candidate built from the coordinatewise limits of a Cauchy filter. -/
noncomputable def cauchyLimit (F : Filter (FrechetSpace p)) (hF : Cauchy F) : FrechetSpace p :=
  ⟨coordLimit F, coordLimit_mem_frechetSubalgebra hF⟩

/-- A Cauchy filter converges to the Fréchet point built from coordinatewise limits. -/
theorem le_nhds_cauchyLimit {F : Filter (FrechetSpace p)} (hF : Cauchy F) :
    F ≤ 𝓝 (cauchyLimit F hF) := by
  rw [← tendsto_id', (withSeminorms p).tendsto_nhds_le]
  rintro N ε hε
  filter_upwards [frechet_sub_coordLimit_le hF hε N] with x hx
  exact Real.iSup_le (fun n ↦ hx n) hε.le

instance : CompleteSpace (FrechetSpace p) where
  complete hf := ⟨_, le_nhds_cauchyLimit hf⟩

variable (p)

/-- The sequence `n ↦ p^{-n^2}` viewed as an element of `FrechetSpace p`. -/
noncomputable def a : FrechetSpace p where
  val n := p ^ (-n ^ 2 : ℤ)
  property N := by
    have hp : 1 ≤ (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_le
    let f : ℕ → ℝ := fun n ↦ p ^ (n ^ 2 - n ^ 3 / N : ℝ)
    suffices ∃ M, ∀ n, f n ≤ M by
      simpa [frechet, ← rpow_intCast, ← rpow_add (by positivity : 0 < (p : ℝ)), neg_div]
    refine ⟨(Finset.range (N + 1)).sup' (by simp) f, fun n ↦ ?_⟩
    by_cases! hn : n ≤ N
    · exact Finset.le_sup' _ (by simpa)
    trans f 0
    · unfold f
      nth_grw 1 [hn]
      field_simp
      simp
    exact Finset.le_sup' _ (by simp)

@[simp] theorem a_apply (n : ℕ) : a p n = p ^ (-n ^ 2 : ℤ) := rfl

theorem isTopologicallyNilpotent_p : IsTopologicallyNilpotent (p : FrechetSpace p) := by
  suffices IsTopologicallyNilpotent (algebraMap ℚ_[p] _ p : FrechetSpace p) by simpa
  have hp : IsTopologicallyNilpotent (p : ℚ_[p]) := by simp
  exact hp.map (continuous_algebraMap _ _)

theorem not_tendsto_a_pow_mul_p_pow_choose_two_zero :
    ¬Tendsto (fun n ↦ (a p ^ n * p ^ n.choose 2)) atTop (𝓝 0) := by
  simp_rw [(withSeminorms p).tendsto_nhds, not_forall, eventually_atTop]
  refine ⟨1, 1, one_pos, fun ⟨N, hN⟩ ↦ ?_⟩
  obtain ⟨k, h3k, hNk⟩ : ∃ k, 3 ≤ k ∧ N ≤ k := ⟨max N 3, by simp⟩
  refine (hN (3 * k) (by nlinarith)).not_ge <| le_trans ?_ <| frechet_le_norm _ _ (2 * k)
  have h1p : 1 ≤ (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_le
  have h0p : 0 < (p : ℝ) := by positivity
  suffices 1 ≤ (p : ℝ) ^ ((2 * k) ^ 2 * (3 * k) - (3 * k).choose 2 - (2 * k) ^ 3 : ℝ) by
    simpa [frechet, rpow_sub h0p, rpow_neg h0p.le, div_eq_mul_inv, rpow_mul h0p.le,
      ← rpow_natCast, -rpow_ofNat, ← rpow_intCast]
  refine one_le_rpow h1p ?_
  grw [Nat.choose_le_pow, Nat.cast_pow, Nat.cast_mul]
  suffices 0 ≤ ((4 * k - 9) * k ^ 2 : ℝ) by convert this using 1 <;> first | rfl | ring
  nth_grw 1 [← h3k]
  norm_num

theorem not_strongNonarchimedean : ¬StrongNonarchimedeanRing (FrechetSpace p) := fun _ ↦
  not_tendsto_a_pow_mul_p_pow_choose_two_zero p <| tendsto_pow_mul_pow_choose_two <|
    isTopologicallyNilpotent_p p

/-- `(a; q)_∞` does not exist: the sequence does not have a limit. -/
theorem not_tendsto_qPochhammer (L : FrechetSpace p) :
    ¬Tendsto ((a p; p)_·) atTop (𝓝 L) := by
  have hp : p.Prime := Fact.out
  revert L
  rw [← not_exists, ← cauchy_map_iff_exists_tendsto, ← CauchySeq,
    NonarchimedeanAddGroup.cauchySeq_iff_tendsto_sub_nhds_zero]
  simp_rw [(withSeminorms p).tendsto_nhds, not_forall, eventually_atTop]
  refine ⟨1, 1, one_pos, fun ⟨N, hN⟩ ↦ (hN (N ^ 2) (by nlinarith)).not_ge ?_⟩
  refine le_trans ?_ <| frechet_le_norm _ _ N
  suffices (1 : ℝ) ≤ (∏ i ∈ Finset.range (N ^ 2), ‖(1 - (p ^ N ^ 2 : ℚ_[p])⁻¹ * p ^ i : ℚ_[p])‖) *
      (p ^ N ^ 3 : ℝ)⁻¹ by
    rw [qPochhammer_succ', ← mul_sub_one]
    simpa [frechet, qPochhammer, ← Nat.cast_pow, -Int.natCast_pow]
  have h₁ {i : ℕ} (hb : i ∈ Finset.range (N ^ 2)) :
      ‖(1 - (p ^ N ^ 2 : ℚ_[p])⁻¹ * p ^ i : ℚ_[p])‖ = p ^ (N ^ 2 - i) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add' (by simp [hp.ne_zero]),
      IsUltrametricDist.norm_sub_of_lt
        (by simpa using one_lt_zpow₀ (by simp [hp.one_lt]) (by grind)),
      Padic.norm_p_zpow, ← zpow_natCast, Nat.cast_sub (by grind)]
    grind
  simp_rw +contextual [h₁, Finset.prod_pow_eq_pow_sum, Finset.sum_range_natSub, ← zpow_natCast]
  rw [← zpow_neg, ← zpow_add' (by simp [hp.ne_zero])]
  refine one_le_zpow₀ (by simp [hp.one_le]) <| sub_nonneg_of_le <| Nat.cast_le.mpr <|
    (Nat.le_div_iff_mul_le (by grind)).mpr ?_
  obtain h | h := lt_or_ge N 2
  · clear * - h; decide +revert
  nth_grw 1 [h]
  grind

end FrechetSpace

example : ∃ (R : Type) (_ : CommRing R) (_ : UniformSpace R) (_ : IsUniformAddGroup R)
    (_ : NonarchimedeanRing R) (_ : CompleteSpace R), ¬ StrongNonarchimedeanRing R :=
  ⟨_, _, _, inferInstance, inferInstance, inferInstance, FrechetSpace.not_strongNonarchimedean p⟩

end NotStrong
