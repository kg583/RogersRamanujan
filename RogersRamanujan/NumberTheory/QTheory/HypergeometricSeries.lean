module

import RogersRamanujan.Algebra.BigOperators.Intervals
public import RogersRamanujan.Data.Fin.VecNotation
import RogersRamanujan.NumberTheory.QTheory.Basic
import RogersRamanujan.NumberTheory.QTheory.BinomialTheorem
public import RogersRamanujan.NumberTheory.QTheory.Defs
import RogersRamanujan.NumberTheory.QTheory.Nonarchimedean
import RogersRamanujan.NumberTheory.QTheory.StrongNonarchimedean
import RogersRamanujan.Topology.Algebra.InfiniteSum.Module
import RogersRamanujan.Topology.Algebra.InfiniteSum.Nonarchimedean
import RogersRamanujan.Topology.Algebra.Nonarchimedean.Bounded
public import RogersRamanujan.Topology.Algebra.Nonarchimedean.Strong
import RogersRamanujan.Topology.Algebra.TopologicallyNilpotent
public import RogersRamanujan.Util.Unconditional
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Util.Superscript
public meta import Mathlib.Util.Superscript -- shake: keep

/-! # Hypergeometric series in q-theory
-/

@[expose] public section

open Filter Topology SummationFilter
open scoped QTheoryUnsafe

variable {R : Type*} [CommRing R]

/-! ### Helper lemmas -/

lemma tendsto_qBinomial_zero [UniformSpace R] [IsUniformAddGroup R]
    [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R] (a : R) {q z : R}
    (hq : IsTopologicallyNilpotent q) (hz : IsTopologicallyNilpotent z) :
    Tendsto (fun n ↦ (a)_n * bInv (q)_n * z ^ n) atTop (𝓝 0) := by
  convert ((tendsto_qPochhammer_qPochhammerInf hq).mul
    (tendsto_bInv_qPochhammer_bInv_qPochhammerInf hq)).mul hz using 2
  ring

/-- Summability of q-binomial series terms: `∑ (a;q)_n / (q;q)_n * z^n` is summable
when `z` and `q` are topologically nilpotent. -/
lemma summable_qBinomial [UniformSpace R] [IsUniformAddGroup R]
    [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R] (a : R) {q z : R}
    (hq : IsTopologicallyNilpotent q) (hz : IsTopologicallyNilpotent z) :
    Summable fun n ↦ (a)_n * bInv (q)_n * z ^ n :=
  NonarchimedeanAddGroup.summable_of_tendsto_atTop_zero <| tendsto_qBinomial_zero a hq hz

lemma tendsto_mul_mul_pow_mul_zero [TopologicalSpace R] [IsTopologicalRing R]
    {f g : ℕ → R} {q : R} (hf : Tendsto f atTop (𝓝 0)) (hg : Tendsto g atTop (𝓝 0))
    (hq : IsTopologicallyNilpotent q) :
    Tendsto (fun n m ↦ f n * g m * q ^ (n * m)).uncurry cofinite (𝓝 0) := by
  rw [← Nat.cofinite_eq_atTop] at hf hg
  exact (tendsto_mul_cofinite_nhds_zero hf hg).mul_topologicallyBounded <|
    hq.topologicallyBounded.mono (by grind)

/-- In a `StrongNonarchimedeanRing`, if `f(n) → 0` and `g(m) → 0`,
then `∑ f(n) * g(m) * q^(n*m)` is summable over `ℕ × ℕ`. -/
theorem summable_mul_mul_pow_mul [UniformSpace R] [IsUniformAddGroup R]
    [CompleteSpace R] [NonarchimedeanRing R] {f g : ℕ → R} {q : R}
    (hf : Tendsto f atTop (𝓝 0)) (hg : Tendsto g atTop (𝓝 0)) (hq : IsTopologicallyNilpotent q) :
    Summable (fun n m ↦ f n * g m * q ^ (n * m)).uncurry :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero <| tendsto_mul_mul_pow_mul_zero hf hg hq

/-! ### q-Hypergeometric series `ᵣφₛ` -/

/-- The `n`-th term of the basic hypergeometric series `ᵣφₛ`. -/
noncomputable def qHypergeometricInner
    (q : R) {r s : ℕ} (a : Fin r → R) (b : Fin s → R) (t : R) (e n : ℕ) :=
  (∏ i, (a i)_n) * bInv (q)_n * (∏ j, bInv (b j)_n) * ((-1) ^ n * q ^ n.choose 2) ^ e * t ^ n

/-- The basic hypergeometric series `ᵣφₛ(a₁,…,aᵣ; b₁,…,bₛ; q, t)`:
`∑ₙ (∏ᵢ (aᵢ;q)ₙ) / ((q;q)ₙ ∏ⱼ (bⱼ;q)ₙ) · [(-1)ⁿ q^(n choose 2)]^(1+s-r) · tⁿ`.
The series converges when `q` and `t` are topologically nilpotent and the `(bⱼ)_∞` are invertible.
-/
noncomputable def qHypergeometric [TopologicalSpace R]
    (q : R) {r s : ℕ} (a : Fin r → R) (b : Fin s → R) (t : R) : R :=
  ∑' n, qHypergeometricInner q a b t (s + 1 - r) n

-- TODO: the following summability statement should be true, and this would relax some hypotheses
-- on invertibility used in several hypergeometric identities.
-- theorem qHypergeometric_Summable (q : R) {r s : ℕ} (a : Fin r → R) (b : Fin s → R) (t : R)
--     (hq : IsTopologicallyNilpotent q) (ht : IsTopologicallyNilpotent t)
--     (hbi : ∀ j n, IsUnit ((b j)_n)) :
--     Summable fun n ↦ (∏ i, qPochhammer (a i) q n) * bInv (qPochhammer q q n) *
--       (∏ j, bInv (qPochhammer (b j) q n)) * ((-1) ^ n * q ^ n.choose 2) ^ ((1 + s) - r) * t ^ n
--     := by
--   sorry

section Meta

open Lean Elab Term Parser Mathlib Tactic Superscript PrettyPrinter
open Syntax MonadTraverser Formatter Qq Meta

declare_unconditional_syntax hypergeometricPhi := "φ"

syntax hypergeometricArgs := "(" term,* "; " term,* "; " term ", " term ")"
attribute [nolint docBlame] hypergeometricArgs

/-- Notation for hypergeometric series: `₂φ₁(x, y; z; q, t)` parses as
`qHypergeometric q ![x, y] ![z] t`. -/
syntax (name := hypergeometric)
  subscript(num) noWs hypergeometricPhi noWs subscript(num) noWs hypergeometricArgs : term

/-- Build the `qHypergeometric` expression from elaborated arguments. -/
meta def mkHypergeometricExpr {u : Level} {R : Q(Type u)}
    (cR : Q(CommRing $R)) (tR : Q(TopologicalSpace $R))
    {r s : ℕ} (a : Fin r → Q($R)) (b : Fin s → Q($R)) (q t : Q($R)) : Q($R) :=
  q(qHypergeometric $q $(PiFin.mkLiteralQ a) $(PiFin.mkLiteralQ b) $t)

/-- Elaborator for `ᵣφₛ(a₁, ..., aᵣ; b₁, ..., bₛ; q, t)`. -/
@[term_elab hypergeometric]
meta def elabHypergeometric : TermElab := fun stx typ? ↦ do
  let `(hypergeometric| $r:subscript$_$s:subscript$args:hypergeometricArgs) := stx | failure
  have r := TSyntax.getNat (.mk r)
  have s := TSyntax.getNat (.mk s)
  let `(hypergeometricArgs| ($a:term,*; $b:term,*; $q:term, $t:term)) := args | failure
  if a.getElems.size != r then
    throwError "expected {r} arguments for the first input; got {a.getElems.size}"
  if b.getElems.size != s then
    throwError "expected {s} arguments for the second input; got {b.getElems.size}"
  have fst := a.getElems[0]?.getD <| b.getElems[0]?.getD <| q
  have typ := typ?.getD <| ← inferType <| ← elabTerm fst none
  let ⟨.succ _, ~q($R), _⟩ ← inferTypeQ (← elabTerm fst typ) | throwError "Expected type"
  let cR ← synthInstanceQ q(CommRing $R)
  let tR ← synthInstanceQ q(TopologicalSpace $R)
  return mkHypergeometricExpr cR tR
    (← a.getElems.mapM (elabTermEnsuringTypeQ · R)).toList.get
    (← b.getElems.mapM (elabTermEnsuringTypeQ · R)).toList.get
    (← elabTermEnsuringTypeQ q R)
    (← elabTermEnsuringTypeQ t R)

open Delaborator SubExpr

/-- Delaborator for `qHypergeometric`, displaying as `ᵣφₛ(...)`. -/
@[app_delab qHypergeometric]
meta def hypergeometricDelab : Delab := do
  let (``qHypergeometric, #[_R, _, _, _q, r, s, a, b, _t]) := (← getExpr).getAppFnArgs | failure
  let some r ← getNatValue? r | failure
  let some s ← getNatValue? s | failure
  let some a := a.vecLit? | failure
  let some b := b.vecLit? | failure
  if a.length != r then failure
  if b.length != s then failure
  let aD ← a.toArray.mapM fun e ↦ withTheReader SubExpr (fun _ ↦ ⟨e, Nat.zero⟩) delab
  let bD ← b.toArray.mapM fun e ↦ withTheReader SubExpr (fun _ ↦ ⟨e, Nat.zero⟩) delab
  let q ← withNaryArg 3 delab
  let t ← withNaryArg 8 delab
  let phi ← `(hypergeometricPhi| φ)
  let args ← `(hypergeometricArgs| ($aD:term,*; $bD:term,*; $q:term, $t:term))
  have r := Syntax.mkNumLit s!"{r}"
  have s := Syntax.mkNumLit s!"{s}"
  `(term| $r:subscript$phi$s:subscript$args:hypergeometricArgs)

variable [TopologicalSpace R] (x y z q t : R) in
/-- info: ₂φ₁(x + y, y; z; q, t) : R -/
#guard_msgs in
#check ₂φ₁(x+y,y;z;q,t)

variable [TopologicalSpace R] (z q t : R) in
/-- info: ₀φ₁(; z; q, t) : R -/
#guard_msgs in
#check ₀φ₁(;z;q,t)

end Meta

theorem summable_qHypergeometricInner
    [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R] [StrongNonarchimedeanRing R]
    [T2Space R] {r s : ℕ} (a : Fin r → R) (b : Fin s → R) {q t : R} (hb : ∀ i, IsUnit (b i)_∞)
    (hq : IsTopologicallyNilpotent q) (ht : IsTopologicallyNilpotent t) (e : ℕ) :
    Summable (qHypergeometricInner q a b t e) := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_atTop_zero <|
    (tendsto_finsetProd _ fun _ _ ↦ tendsto_qPochhammer_qPochhammerInf hq).mul
    (tendsto_bInv_qPochhammer_bInv_qPochhammerInf hq) |>.mul
    (tendsto_finsetProd _ fun _ _ ↦ tendsto_bInv_qPochhammer_bInv_qPochhammerInf' hq (hb _))
    |>.boundedRange |>.mul ?_ |>.mul_tendsto_zero ht
  refine .mono (hq.topologicallyBounded.neg.union hq.topologicallyBounded) fun _ ↦ ?_
  simp [neg_one_pow_eq_ite, ← pow_mul, neg_pow (_ ^ _)]
  grind

theorem qHypergeometric_reindex [TopologicalSpace R]
    {r₁ r₂ s₁ s₂ : ℕ} {a : Fin r₁ → R} {b : Fin s₁ → R}
    (er : Fin r₂ ≃ Fin r₁) (es : Fin s₂ ≃ Fin s₁) (q t : R) :
    qHypergeometric q (a ∘ er) (b ∘ es) t = qHypergeometric q a b t := by
  simp [qHypergeometric, qHypergeometricInner, ← er.prod_comp, ← es.prod_comp]
  obtain rfl := by simpa using Fintype.card_congr er
  obtain rfl := by simpa using Fintype.card_congr es
  rfl

@[simp] theorem qHypergeometric_vecCons_vecCons [TopologicalSpace R]
    {r s : ℕ} {a : Fin r → R} {b : Fin s → R} {x q : R}
    (hx : ∀ n, IsUnit (x)_n) (t : R) :
    qHypergeometric q (Matrix.vecCons x a) (Matrix.vecCons x b) t = qHypergeometric q a b t := by
  unfold qHypergeometric qHypergeometricInner
  simp only [Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Nat.reduceSubDiff]
  simp_rw [mul_assoc, mul_left_comm, (hx _).mul_bInv_cancel_assoc]

@[simp] theorem qHypergeometric_1_0_eq
    [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
    [StrongNonarchimedeanRing R] [T2Space R]
    {a q t : R} (hq : IsTopologicallyNilpotent q) (ht : IsTopologicallyNilpotent t) :
    ₁φ₀(a; ; q, t) = (a * t)_∞ * bInv (t)_∞ := by
  simp [qHypergeometric, qHypergeometricInner, qPochhammerInf_div_qPochhammerInf_eq_tsum ht hq]

/-! ### q-Hypergeometric series `₂φ₁` -/

lemma qHypergeometric_2_1_eq [TopologicalSpace R] (a₁ a₂ b₁ q t : R) :
    ₂φ₁(a₁, a₂; b₁; q, t) =
    ∑' n, (a₁)_n * (a₂)_n * bInv (q)_n * bInv (b₁)_n * t ^ n := by
  simp [qHypergeometric, qHypergeometricInner]

/-- Since `qHypergeometric_Heine'` is symmetric,
we only need to prove one half of it! -/
theorem qHypergeometric_Heine_half
    [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
    [StrongNonarchimedeanRing R] [T2Space R]
    {x y a q t : R} (hq : IsTopologicallyNilpotent q) (hy : IsTopologicallyNilpotent y)
    (hay : IsUnit (a * y)_∞) :
    (a * y)_∞ * bInv (y)_∞ * ₂φ₁(x, y; a * y; q, t) =
    ∑' n, ∑' m, (x)_n * bInv (q)_n * t ^ n * ((a)_m * bInv (q)_m * y ^ m) * q ^ (n * m) :=
  calc (a * y)_∞ * bInv (y)_∞ * ₂φ₁(x, y; a * y; q, t)
    = (a * y)_∞ * bInv (y)_∞ * ∑' n, (x)_n * (y)_n * bInv (q)_n * bInv (a * y)_n * t ^ n := by
        rw [qHypergeometric_2_1_eq]
  _ = ∑' n, (x)_n * bInv (q)_n * t ^ n * ((a * (y * q ^ n))_∞ * bInv (y * q ^ n)_∞) := by
    rw [← (hay.mul (.bInv _)).tsum_mul_left]
    congr! 2 with n
    simp [qPochhammerInf_shift_eq_bInv_qPochhammer_mul hq,
      hq, hay, isUnit_qPochhammerInf hy hq, ← mul_assoc a y (q ^ n)]
    ac_rfl
  _ = ∑' n, (x)_n * bInv (q)_n * t ^ n * ∑' m, (a)_m * bInv (q)_m * (y * q ^ n) ^ m := by
    simp_rw [qPochhammerInf_div_qPochhammerInf_eq_tsum (hy.mul_pow hq) hq]
  _ = ∑' n, ∑' m, (x)_n * bInv (q)_n * t ^ n * ((a)_m * bInv (q)_m * y ^ m) * q ^ (n * m) := by
    simp_rw [← (summable_qBinomial a hq (hy.mul_pow hq)).tsum_mul_left, mul_pow, ← pow_mul]
    ac_rfl

/-- The `₂φ₁` transformation formula by Heine is:
`₂φ₁(x, y; z; q, t) = (y)_∞(xt)_∞ / (z)_∞(t)_∞ · ₂φ₁(z/y, t; xt; q, y)`.

Here we instead write `z` as `a * y` so that what we call `z/y` is just `a`,
which allows us to not have to assume that `y` is a unit.
This also makes the transformation symmetric.

TODO: relax the hypothesis `hxt : IsUnit ((x * t)_∞)` to `hxt : ∀ n, IsUnit (x * t)_n`.
-/
theorem qHypergeometric_Heine'
    [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
    [StrongNonarchimedeanRing R] [T2Space R]
    {x y a q t : R} (hq : IsTopologicallyNilpotent q) (ht : IsTopologicallyNilpotent t)
    (hy : IsTopologicallyNilpotent y)
    (hxt : IsUnit (x * t)_∞) (hay : IsUnit (a * y)_∞) :
    ₂φ₁(x, y; a * y; q, t) =
    (y)_∞ * (x * t)_∞ * bInv (a * y)_∞ * bInv (t)_∞ * ₂φ₁(a, t; x * t; q, y) := by
  simp_rw [mul_assoc]
  rw [← (isUnit_qPochhammerInf hy hq).bInv_mul_eq_iff_eq_mul, mul_left_comm,
    hay.eq_bInv_mul_iff_mul_eq, ← mul_assoc, ← mul_assoc,
    qHypergeometric_Heine_half hq hy hay,
    qHypergeometric_Heine_half hq ht hxt,
    ← (summable_mul_mul_pow_mul (tendsto_qBinomial_zero a hq hy)
        (tendsto_qBinomial_zero x hq ht) hq).tsum_comm]
  ac_rfl

/-- The `₂φ₁` transformation formula by Heine:
`₂φ₁(x, y; z; q, t) = (y)_∞(xt)_∞ / (z)_∞(t)_∞ · ₂φ₁(z/y, t; xt; q, y)`.
This is the Heine transformation for the basic hypergeometric series.
See Corollary 2.3 of Andrews, "The Theory of Partitions".

See `qHypergeometric_Heine'` for a more general version.

TODO: relax the hypothesis `hxt : IsUnit ((x * t)_∞)` to `hxt : ∀ n, IsUnit (x * t)_n`.
-/
theorem qHypergeometric_Heine
    [UniformSpace R] [IsUniformAddGroup R]
    [CompleteSpace R] [StrongNonarchimedeanRing R] [T2Space R]
    {x y z q t : R} (hq : IsTopologicallyNilpotent q) (ht : IsTopologicallyNilpotent t)
    (hy : IsTopologicallyNilpotent y)
    (hxt : IsUnit (x * t)_∞) (hyu : IsUnit y) (hzu : IsUnit (z)_∞) :
    ₂φ₁(x, y; z; q, t) =
    (y)_∞ * (x * t)_∞ * bInv (z)_∞ * bInv (t)_∞ * ₂φ₁(z * bInv y, t; x * t; q, y) := by
  nth_rw 1 2 [show z = z * bInv y * y by simp [mul_assoc, hyu]] at hzu ⊢
  exact qHypergeometric_Heine' hq ht hy hxt hzu

/-- The q-analogue of Gauss theorem says:
`₂φ₁(x,y;z;q,z/xy) = (z/x)_∞(z/y)_∞ / (z)_∞(z/xy)_∞`.

We state it here without using inverses of variables by doing the substitution `z ↦ t * x * y`.
-/
theorem qHypergeometric_Gauss'
    [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
    [StrongNonarchimedeanRing R] [T2Space R]
    {x y q t : R} (hq : IsTopologicallyNilpotent q) (ht : IsTopologicallyNilpotent t)
    (hy : IsTopologicallyNilpotent y)
    (hxt : IsUnit (x * t)_∞) (hxyt : IsUnit (x * y * t)_∞) :
    ₂φ₁(x, y; x * y * t; q, t) = (x * t)_∞ * (y * t)_∞ * bInv (x * y * t)_∞ * bInv (t)_∞ := by
  rw [mul_right_comm, qHypergeometric_Heine' hq ht hy hxt (by rwa [mul_right_comm]),
    qHypergeometric_vecCons_vecCons (isUnit_qPochhammer_of_isUnit_qPochhammerInf hq hxt),
    qHypergeometric_1_0_eq hq hy]
  grind

/-- The q-analogue of Gauss theorem, proved by Heine:
`₂φ₁(x,y;z;q,z/xy) = (z/x)_∞(z/y)_∞ / (z)_∞(z/xy)_∞`.
See Corollary 2.4 of Andrews, "The Theory of Partitions".

See `qHypergeometric_Gauss'` for a more general version.

TODO: the hypothesis `hzyu : IsUnit (z * bInv y)_∞` is used to evaluate the inner sum
(`h_inner`), can likely be relaxed to `∀ n, IsUnit (z * bInv y)_n`.
-/
theorem qHypergeometric_Gauss
    [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
    [StrongNonarchimedeanRing R] [T2Space R]
    {x y q z : R} (hxu : IsUnit x) (hyu : IsUnit y)
    (hq : IsTopologicallyNilpotent q) (hzxy : IsTopologicallyNilpotent (z * bInv x * bInv y))
    (hy : IsTopologicallyNilpotent y)
    (hz : IsUnit (z)_∞) (hzy : IsUnit (z * bInv y)_∞) :
    ₂φ₁(x, y; z; q, z * bInv x * bInv y) =
      (z * bInv x)_∞ * (z * bInv y)_∞ * bInv (z)_∞ * bInv (z * bInv x * bInv y)_∞ := by
  have h : z = x * y * (z * bInv x * bInv y) := by grind
  have h₁ : x * (z * bInv x * bInv y) = z * bInv y := by grind
  have h₂ : y * (z * bInv x * bInv y) = z * bInv x := by grind
  nth_rw 1 [h, qHypergeometric_Gauss' hq hzxy hy (by rwa [h₁]) (by rwa [← h]), h₁, h₂, ← h]
  ac_rfl

/-- Rogers' first transformation law for `₂φ₁`:
`₂φ₁(x,y;z;q,t) = (z/y)_∞(yt)_∞ / (t)_∞(z)_∞ * ₂φ₁(y,xyt/z;yt,q,z/y)`.
Originally proved by Rogers in "On a Three-fold Symmetry in the Elements of Heine's Series".
See also Equation (2.15) of Andrews, "q-Series: Their Development and Application in Analysis,
Number Theory, Combinatorics, Physics, and Computer Algebra".
-/
theorem qHypergeometric_Rogers
    [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
    [StrongNonarchimedeanRing R] [T2Space R]
    {q : R} (hq : IsTopologicallyNilpotent q) (x y z t : R) (hy : IsTopologicallyNilpotent y)
    (hyu : IsUnit y) (hzu : IsUnit z) (hzu_inf : IsUnit (z)_∞)
    (ht : IsTopologicallyNilpotent t) (hxt : IsUnit (x * t)_∞)
    (hzy : IsTopologicallyNilpotent (z * bInv y)) :
    ₂φ₁(x, y; z; q, t) =
      (z * bInv y)_∞ * (y * t)_∞ * bInv (t)_∞ * bInv (z)_∞ *
        ₂φ₁(y, x * y * t * bInv z; y * t; q, z * bInv y) := by
  have hzyu : IsUnit (z * bInv y) := .of_mul_eq_one (y * bInv z) (by grind)
  have hzyu_inv : bInv (z * bInv y) = y * bInv z := by grind
  have hty : IsUnit (t * y)_∞ := isUnit_qPochhammerInf (ht.mul hy) hq
  -- Swap parameters in ₂φ₁
  have h2phi1_swap₁ : ₂φ₁(z * bInv y, t; x * t; q, y) =
      ₂φ₁(t, z * bInv y; x * t; q, y) := by
    simp only [qHypergeometric_2_1_eq]; congr 1; ext n; ring
  have h2phi1_swap₂ : ₂φ₁(x * y * t * bInv z, y; t * y; q, z * bInv y) =
      ₂φ₁(y, x * y * t * bInv z; y * t; q, z * bInv y) := by
    simp only [mul_comm t y, qHypergeometric_2_1_eq]; congr 1; ext n; ring
  -- Apply Heine twice with a parameter swap in between
  rw [qHypergeometric_Heine hq ht hy hxt hyu hzu_inf, h2phi1_swap₁,
    qHypergeometric_Heine hq hy hzy hty hzyu hxt, hzyu_inv,
    show (x * t) * (y * bInv z) = x * y * t * bInv z by ring,
    show (t * y)_∞ = (y * t)_∞ by congr 1; ring, h2phi1_swap₂]
  -- Cancel `(y)_∞ * bInv((y)_∞)` and `(x*t)_∞ * bInv((x*t)_∞)`
  simp [mul_assoc, mul_left_comm,
    (isUnit_qPochhammerInf hy hq).mul_bInv_cancel_assoc,
    hxt.mul_bInv_cancel_assoc]

/-- Rogers' second transformation law for `₂φ₁`:
`₂φ₁(x,y;z;q,t) = (xyt/z)_∞ / (t)_∞ * ₂φ₁(z/x,z/y;z,q,xyt/z)`.
Originally proved by Rogers in "On a Three-fold Symmetry in the Elements of Heine's Series".
See also Equation (2.16) of Andrews, "q-Series: Their Development and Application in Analysis,
Number Theory, Combinatorics, Physics, and Computer Algebra".
-/
theorem qHypergeometric_Rogers_2
    [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
    [StrongNonarchimedeanRing R] [T2Space R]
    {q : R} (hq : IsTopologicallyNilpotent q) (x y z t : R) (hxu : IsUnit x)
    (hy : IsTopologicallyNilpotent y) (hyu : IsUnit y)
    (hzu : IsUnit z) (hzu_inf : IsUnit (z)_∞)
    (ht : IsTopologicallyNilpotent t) (hxt : IsUnit (x * t)_∞)
    (hzy : IsTopologicallyNilpotent (z * bInv y))
    (hxyz : IsTopologicallyNilpotent (x * y * t * bInv z)) :
    ₂φ₁(x, y; z; q, t) =
      (x * y * t * bInv z)_∞ * bInv (t)_∞ *
        ₂φ₁(z * bInv x, z * bInv y; z; q, x * y * t * bInv z) := by
  have hyt_eq : y * t = z * bInv x * (x * y * t * bInv z) := by grind
  have hyz : y * (z * bInv y) = z := by grind
  have hyt_inf : IsUnit (y * t)_∞ := isUnit_qPochhammerInf (hy.mul ht) hq
  -- Apply Rogers 1 to the LHS, then Heine' to the inner ₂φ₁
  rw [qHypergeometric_Rogers hq x y z t hy hyu hzu hzu_inf ht hxt hzy]
  nth_rw 2 [hyt_eq]
  rw [qHypergeometric_Heine' hq hzy hxyz (by rwa [hyz]) (by rwa [← hyt_eq]),
    hyz, ← hyt_eq]
  -- Cancel three unit pairs: `(z/y)_∞`, `(yt)_∞`, `(z)_∞`
  simp [mul_assoc, mul_left_comm,
    (isUnit_qPochhammerInf hzy hq).mul_bInv_cancel_assoc,
    hyt_inf.mul_bInv_cancel_assoc, hzu_inf.mul_bInv_cancel_assoc]

/-! ### q-hypergeometric series `₃φ₂` -/

lemma qHypergeometric_3_2_eq [TopologicalSpace R] (a₁ a₂ a₃ b₁ b₂ q t : R) :
    ₃φ₂(a₁, a₂, a₃; b₁, b₂; q, t) =
      ∑' n, (a₁)_n * (a₂)_n * (a₃)_n *
        bInv (q)_n * bInv (b₁)_n * bInv (b₂)_n * t ^ n := by
  simp only [qHypergeometric, qHypergeometricInner, Fin.prod_univ_succ, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Finset.univ_unique, Fin.default_eq_zero,
    Matrix.cons_val_fin_one, Finset.prod_const, Finset.card_singleton, pow_one, Nat.reduceAdd,
    tsub_self, pow_zero, mul_one]
  congr 1; ext n; ring

/-- The summand of the `₃φ₂` series vanishes when the third parameter is `(q⁻¹)^m` and the
summation index exceeds `m`, because `((q⁻¹)^m; q)_k = 0` for `k > m`. -/
lemma qHypergeometric_3_2_summand_eq_zero {q : R}
    (a₁ a₂ b₁ b₂ t : R) {m k : ℕ} (hk : m < k) :
    (a₁)_k * (a₂)_k * ((bInv q) ^ m)_k * bInv (q)_k * bInv (b₁)_k * bInv (b₂)_k * t ^ k = 0 := by
  simp [qPochhammer_pow_bInv_eq_zero (q := q) hk]

/-- Key shift identity: `(a·q⁻¹; q)_{k+1} = (1 - a·q⁻¹) · (a; q)_k` when `q⁻¹ · q = 1`.
This follows from `qPochhammer_succ` and `a·q⁻¹·q = a`. -/
lemma qPochhammer_mul_bInv_succ {q : R} (hqu : IsUnit q) (a : R) (k : ℕ) :
    (a * bInv q)_(k + 1) = (1 - a * bInv q) * (a)_k := by
  rw [qPochhammer_succ, mul_assoc, hqu.bInv_mul_cancel, mul_one]

/-- The Pfaff–Saalschütz sum rewritten as a triangular double sum: applying Cauchy's
identity `qPochhammer_mul_eq_sum_qChoose` to `(a*b*c*q^k; q)_(n-k)` and the tower identity
`qChoose_tower` turns the single Pochhammer factor into `(b)_(k+r)` weighted by
`qChoose n (k+r) * qChoose (k+r) k`. -/
lemma qPfaffSaalschutz_sum_eq_triangle_sum (a b c q : R) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      qChoose q n k * (a)_k * (b)_k * c ^ k * (c)_(n - k) * (a * b * c * q ^ k)_(n - k) =
    ∑ k ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n - k + 1),
      qChoose q n (k + r) * qChoose q (k + r) k * (a)_k * (b)_(k + r) *
      c ^ k * (a * c) ^ r * (c)_(n - k) * (a * c)_(n - (k + r)) := by
  refine Finset.sum_congr rfl fun k hk => ?_
  -- Step 1: expand `(a*b*c*q^k; q)_(n-k)` by Cauchy with `u = b*q^k`, `v = a*c`.
  rw [show a * b * c * q ^ k = (b * q ^ k) * (a * c) by ring,
    qPochhammer_mul_eq_sum_qChoose (b * q ^ k) (a * c) (n - k), Finset.mul_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hkr : k + r ≤ n := by rw [Finset.mem_range] at hk hr; omega
  -- Step 2: rewrite the summand using `qChoose_mul` and `(b)_k * (b*q^k)_r = (b)_(k+r)`.
  have hpoch : (b)_k * (b * q ^ k)_r = (b)_(k + r) := (qPochhammer_add' k r).symm
  have htower : qChoose q n k * qChoose q (n - k) r =
      qChoose q n (k + r) * qChoose q (k + r) k := by
    rw [qChoose_mul q (show k ≤ k + r by omega), Nat.add_sub_cancel_left]
  have hreorder : qChoose q n k * (a)_k * (b)_k * c ^ k * (c)_(n - k) *
      (qChoose q (n - k) r * (b * q ^ k)_r * (a * c) ^ r * (a * c)_(n - (k + r))) =
    (qChoose q n k * qChoose q (n - k) r) * (a)_k * ((b)_k * (b * q ^ k)_r) * c ^ k *
      (c)_(n - k) * (a * c) ^ r * (a * c)_(n - (k + r)) := by ring
  rw [show n - k - r = n - (k + r) by omega, hreorder, htower, hpoch]
  ring

/-- Closed form for the inner sum arising after reindexing the Pfaff–Saalschütz double sum:
`∑_{k ≤ m} qChoose m k (a)_k c^k (a c)^(m-k) (c)_(n-k) = c^m (c)_(n-m) (a c q^(n-m))_m`,
proved by factoring out `c^m (c)_(n-m)` and applying Cauchy's identity in reverse. -/
lemma qPfaffSaalschutz_inner_sum_eq (a c q : R) {n m : ℕ} (hm : m ≤ n) :
    ∑ k ∈ Finset.range (m + 1), qChoose q m k * (a)_k * c ^ k * (a * c) ^ (m - k) * (c)_(n - k) =
    c ^ m * (c)_(n - m) * (a * c * q ^ (n - m))_m := by
  -- Per-term: factor out `c^m * (c; q)_(n-m)` from each summand.
  have hsummand : ∀ k ∈ Finset.range (m + 1),
      qChoose q m k * (a)_k * c ^ k * (a * c) ^ (m - k) * (c)_(n - k) =
      c ^ m * (c)_(n - m) *
        (qChoose q m k * (a)_k * a ^ (m - k) * (c * q ^ (n - m))_(m - k)) := fun k hk => by
    have hk' : k ≤ m := by simpa using hk
    rw [mul_pow, show n - k = (n - m) + (m - k) by omega, qPochhammer_add']
    have hpow : c ^ k * c ^ (m - k) = c ^ m := by rw [← pow_add, show k + (m - k) = m by omega]
    linear_combination
      (qChoose q m k * (a)_k * a ^ (m - k) * (c)_(n - m) * (c * q ^ (n - m))_(m - k)) * hpow
  -- The remaining inner sum equals `(a*c*q^(n-m); q)_m` by reverse-Cauchy.
  have hcauchy : ∑ k ∈ Finset.range (m + 1),
      qChoose q m k * (a)_k * a ^ (m - k) * (c * q ^ (n - m))_(m - k) =
      (a * c * q ^ (n - m))_m := by
    rw [show a * c * q ^ (n - m) = (c * q ^ (n - m)) * a by ring,
      qPochhammer_mul_eq_sum_qChoose, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ m := by simpa using hk
    rw [show m + 1 - 1 - k = m - k by omega, Nat.sub_sub_self hk', qChoose_symm hk']
    ring
  rw [Finset.sum_congr rfl hsummand, ← Finset.mul_sum, hcauchy]

/-- The polynomial identity underlying `qPfaffSaalschutz_denom_cleared`:
`∑ k, qChoose n k · (a)_k · (b)_k · c^k · (c)_(n-k) · (a*b*c*q^k)_(n-k) = (a*c)_n · (b*c)_n`. -/
theorem sum_qChoose_mul_qPochhammer_eq_qPochhammer_mul (a b c q : R) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      qChoose q n k * (a)_k * (b)_k * c ^ k * (c)_(n - k) * (a * b * c * q ^ k)_(n - k) =
    (a * c)_n * (b * c)_n := by
  -- Pre-cleanup: rewrite `(a*c)^r` as `(a*c)^((k+r)-k)` to match `sum_triangle_reindex`.
  have hcleanup : ∀ k ∈ Finset.range (n + 1), ∀ r ∈ Finset.range (n - k + 1),
      qChoose q n (k + r) * qChoose q (k + r) k * (a)_k * (b)_(k + r) *
        c ^ k * (a * c) ^ r * (c)_(n - k) * (a * c)_(n - (k + r)) =
      qChoose q n (k + r) * qChoose q (k + r) k * (a)_k * (b)_(k + r) *
        c ^ k * (a * c) ^ ((k + r) - k) * (c)_(n - k) * (a * c)_(n - (k + r)) :=
    fun k _ r _ => by rw [Nat.add_sub_cancel_left]
  -- For each `m`, factor outer constants and apply `qPfaffSaalschutz_inner_sum_eval`,
  -- then collapse `(a*c)_(n-m) * (a*c*q^(n-m))_m = (a*c)_n`.
  have hcollapse : ∀ m ∈ Finset.range (n + 1),
      (∑ k ∈ Finset.range (m + 1),
          qChoose q n m * qChoose q m k * (a)_k * (b)_m * c ^ k * (a * c) ^ (m - k) *
          (c)_(n - k) * (a * c)_(n - m)) =
      (a * c)_n * (qChoose q n m * (b)_m * c ^ m * (c)_(n - m)) := fun m hm => by
    have hm' : m ≤ n := by simpa using hm
    have hreorder : ∀ k, qChoose q n m * qChoose q m k * (a)_k * (b)_m * c ^ k *
        (a * c) ^ (m - k) * (c)_(n - k) * (a * c)_(n - m) =
        qChoose q n m * (b)_m * (a * c)_(n - m) *
        (qChoose q m k * (a)_k * c ^ k * (a * c) ^ (m - k) * (c)_(n - k)) := fun _ => by ring
    have hcol : (a * c)_(n - m) * (a * c * q ^ (n - m))_m = (a * c)_n := by
      conv_rhs => rw [show n = (n - m) + m by omega]; rw [qPochhammer_add']
    rw [Finset.sum_congr rfl fun k _ => hreorder k,
      ← Finset.mul_sum, qPfaffSaalschutz_inner_sum_eq a c q hm']
    linear_combination (qChoose q n m * (b)_m * c ^ m * (c)_(n - m)) * hcol
  -- Wire steps together.
  rw [qPfaffSaalschutz_sum_eq_triangle_sum,
    Finset.sum_congr rfl fun k hk =>
      Finset.sum_congr rfl fun r hr => hcleanup k hk r hr,
    ← sum_triangle_reindex (f := fun r j => qChoose q n j * qChoose q j r * (a)_r * (b)_j *
      c ^ r * (a * c) ^ (j - r) * (c)_(n - r) * (a * c)_(n - j)),
    Finset.sum_congr rfl hcollapse,
    ← Finset.mul_sum, qPochhammer_mul_eq_sum_qChoose b c n]

/-- **Cleared-denominator q-Pfaff-Saalschutz identity**.
This is the Cauchy product identity after multiplying both sides by `(q)_n · (z)_n · (c)_n`
to clear all `qPochhammer_inv` denominators, which is
`∑ k ∈ range (n + 1), (x)_k (y)_k (q^{n+1-k})_k c^k (q^{k+1})_{n-k} (z q^k)_{n-k} (c)_{n-k}` equals
`(q)_n (z/x)_n (z/y)_n` where `c = z / (x * y)`.
Proof uses `sum_qChoose_mul_qPochhammer_eq_qPochhammer_mul` and `qPochhammer_qChoose_coeff`. -/
theorem qPfaffSaalschutz_denom_cleared {q : R} (x y z : R) (n : ℕ)
    (hx : IsUnit x) (hy : IsUnit y) :
    let c := z * bInv x * bInv y
    ∑ k ∈ Finset.range (n + 1),
      (x)_k * (y)_k * (q ^ (n + 1 - k))_k * c ^ k *
        (q ^ (k + 1))_(n - k) * (z * q ^ k)_(n - k) * (c)_(n - k) =
      (q)_n * (z * bInv x)_n * (z * bInv y)_n := by
  intro c
  have hx1 : x * bInv x = 1 := hx.mul_bInv_cancel
  have hy1 : y * bInv y = 1 := hy.mul_bInv_cancel
  -- Substitutions: with `c = z * bInv x * bInv y`, we have `x*y*c = z`,
  -- `x*c = z * bInv y`, and `y*c = z * bInv x`.
  have habc : x * y * c = z := by grind
  have hac : x * c = z * bInv y := by grind
  have hbc : y * c = z * bInv x := by grind
  -- Per-summand: identity (4) `qPochhammer_qChoose_coeff` factors out `(q; q)_n`.
  have hsummand : ∀ k ∈ Finset.range (n + 1),
      (x)_k * (y)_k * (q ^ (n + 1 - k))_k * c ^ k *
        (q ^ (k + 1))_(n - k) * (z * q ^ k)_(n - k) * (c)_(n - k) =
      (q)_n * (qChoose q n k * (x)_k * (y)_k * c ^ k * (c)_(n - k) * (z * q ^ k)_(n - k)) :=
    fun k hk => by
      have hk' : k ≤ n := by simpa using hk
      linear_combination ((x)_k * (y)_k * c ^ k * (c)_(n - k) * (z * q ^ k)_(n - k)) *
        (qPochhammer_qChoose_coeff q hk').symm
  rw [Finset.sum_congr rfl hsummand, ← Finset.mul_sum]
  have h := sum_qChoose_mul_qPochhammer_eq_qPochhammer_mul x y c q n
  rw [habc, hac, hbc] at h
  linear_combination (q)_n * h

/-- **Cauchy product coefficient identity**
`∑ k ∈ range (n + 1), (x)_k (y)_k (q^{n+1-k})_k c^k / ((q)_k (z)_k (c)_{n-k} (z q^k)_{n-k})`
is `(z/x)_n (z/y)_n / ((z)_n (c)_n)` when `c = z / (x * y)`.
Derived from the cleared-denominator identity `qPfaffSaalschutz_denom_cleared`
by dividing both sides by `(q)_n · (z)_n · (c)_n`.
-/
lemma qPfaffSaalschutz_cauchyProduct
    [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
    [StrongNonarchimedeanRing R] [T2Space R]
    {q : R} (hq : IsTopologicallyNilpotent q) (x y z : R) (n : ℕ)
    (hxu : IsUnit x) (hyu : IsUnit y) (hz : ∀ n, IsUnit (z)_n)
    (hzxy : ∀ k, IsUnit (z * bInv x * bInv y)_k) :
    ∑ k ∈ Finset.range (n + 1),
      (x)_k * (y)_k * (q ^ (n + 1 - k))_k * (z * bInv x * bInv y) ^ k *
        bInv (q)_k * bInv (z)_k * bInv ((z * bInv x * bInv y * q ^ (n - k))_k) =
    (z * bInv x)_n * (z * bInv y)_n * bInv (z)_n * bInv (z * bInv x * bInv y)_n := by
  -- Abbreviation
  set c := z * bInv x * bInv y
  -- The cleared identity: `∑ T_k = (q)_n * (a)_n * (b)_n`
  have hcleared := qPfaffSaalschutz_denom_cleared (q := q) x y z n hxu hyu
  change ∑ k ∈ Finset.range (n + 1),
      (x)_k * (y)_k * (q ^ (n + 1 - k))_k * c ^ k * (q ^ (k + 1))_(n - k) *
        (z * q ^ k)_(n - k) * (c)_(n - k) =
    (q)_n * (z * bInv x)_n * (z * bInv y)_n at hcleared
  -- `F = (q)_n * (z)_n * (c)_n` is a unit, so we can cancel
  have huF := ((isUnit_qPochhammer hq hq n).mul (hz n)).mul (hzxy n)
  apply huF.mul_left_cancel
  -- Use calc: `F * LHS = ∑ T_k = (q)_n * (a)_n * (b)_n = F * RHS`
  have hRHS : (q)_n * (z)_n * (c)_n *
      ((z * bInv x)_n * (z * bInv y)_n * bInv (z)_n * bInv (c)_n) =
        (q)_n * (z * bInv x)_n * (z * bInv y)_n := by grind
  rw [hRHS, Finset.mul_sum, ← hcleared]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [Finset.mem_range] at hk
  have := qPochhammer_add' (a := q) (q := q) k (n - k)
  have := qPochhammer_add' (a := z) (q := q) k (n - k)
  have := qPochhammer_add' (a := c) (q := q) (n - k) k
  grind

/-- The q-Pfaff-Saalschutz summation formula for `₃φ₂`:
`₃φ₂(x,y,q⁻ⁿ;z,xyq¹⁻ⁿ/z;q,q) = (z/x)_n (z/y)_n / ((z)_n (z/(xy))_n)`.
See Equation (3.3.12) of Andrews, "The Theory of Partitions".
NOTE: `hzxy` is only used to show that `(z/(xy) * q^{n-k})_k` is a unit for `0 ≤ k ≤ n`.
-/
theorem qHypergeometric_PfaffSaalschutz
    [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
    [StrongNonarchimedeanRing R] [T2Space R]
    {q : R} (hq : IsTopologicallyNilpotent q) (x y z : R) (n : ℕ)
    (hqu : IsUnit q) (hxu : IsUnit x) (hyu : IsUnit y) (hzu : IsUnit z)
    (hz : ∀ k, IsUnit (z)_k)
    (hxyqz : ∀ k, IsUnit (x * y * q * (bInv q) ^ n * bInv z)_k)
    (hzxy : IsTopologicallyNilpotent (z * bInv x * bInv y)) :
    ₃φ₂(x, y, (bInv q) ^ n; z, x * y * q * (bInv q) ^ n * bInv z; q, q) =
      (z * bInv x)_n * (z * bInv y)_n * bInv (z)_n * bInv (z * bInv x * bInv y)_n := by
  set p := bInv q with hp_def
  set c := z * bInv x * bInv y with hc_def
  -- Key unit relations:
  have hpq : p * q = 1 := hqu.bInv_mul_cancel
  have : c * (x * y * q * bInv z) = q := by grind
  set d := x * y * q * p ^ n * bInv z with hd_def
  -- Step 1: Expand ₃φ₂ as tsum
  rw [qHypergeometric_3_2_eq]
  -- Step 2: Convert tsum to Finset.sum (terms vanish for k > n)
  rw [tsum_eq_sum (s := Finset.range (n + 1)) (by
    intro k hk
    rw [Finset.mem_range, not_lt] at hk
    have h : (p ^ n)_k = 0 := by
      rw [hp_def]; exact qPochhammer_pow_bInv_eq_zero (q := q) (by omega : n < k)
    simp [h])]
  -- Step 3: Show each ₃φ₂ summand equals the Cauchy product summand via reversal identities
  have hterm : ∀ k ∈ Finset.range (n + 1),
      (x)_k * (y)_k * (p ^ n)_k * bInv (q)_k * bInv (z)_k * bInv (d)_k * q ^ k =
        (x)_k * (y)_k * (q ^ (n + 1 - k))_k * c ^ k *
          bInv (q)_k * bInv (z)_k * bInv ((c * q ^ (n - k))_k) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hk_le : k ≤ n := by omega
    -- Cleared-denominator: `(p^n;q)_k · q^k · (c·q^{n-k};q)_k = (q^{n+1-k};q)_k · c^k · (d;q)_k`
    have : (p ^ n)_k * q ^ k * (c * q ^ (n - k))_k = (q ^ (n + 1 - k))_k * c ^ k * (d)_k := by
      have hcu : IsUnit c := (hzu.mul (.bInv x)).mul (.bInv y)
      have hcbu : IsUnit (bInv c) := .bInv _
      have hd_eq : d = bInv c * q * bInv q ^ n := by grind
      have h1 := qPochhammer_bInv_pow' hqu (n := k) (N := n)
      have h2 := qPochhammer_bInv_pow hqu (hcbu.mul hqu) (n := k) (N := n) hk_le
      have h3 : (c * bInv q * q ^ (n + 1 - k))_k = (c * q ^ (n - k))_k := by
        congr 1; rw [show n + 1 - k = 1 + (n - k) by lia]; grind
      grind [hcu.pow_mul_bInv_pow_same, hcbu.bInv_mul hqu, mul_pow]
    -- Derive bInv version via unit cancellation
    have hzqnk : IsTopologicallyNilpotent (c * q ^ (n - k)) := hzxy.mul_pow hq
    grind [isUnit_qPochhammer hzqnk hq k, hxyqz k]
  -- Step 4: Apply Finset.sum_congr + Cauchy product lemma
  exact (Finset.sum_congr rfl hterm).trans
    (qPfaffSaalschutz_cauchyProduct hq x y z n hxu hyu hz (isUnit_qPochhammer hzxy hq ·))
