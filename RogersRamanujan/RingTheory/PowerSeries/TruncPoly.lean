module

public import Mathlib.RingTheory.PowerSeries.Inverse

/-! # Truncated polynomials / power series

We define truncated polynomials / power series (they are the same thing), which are lists of
coefficients up to a specified degree.

-/

@[expose] public section

open PowerSeries in
theorem PowerSeries.coeff_invOfUnit_congr {R : Type*} [Ring R] {f g : R⟦X⟧} {n : ℕ} {u : Rˣ}
    (ih : ∀ m ≤ n, f.coeff m = g.coeff m) :
    (invOfUnit f u).coeff n = (invOfUnit g u).coeff n := by
  rw [coeff_invOfUnit, coeff_invOfUnit]
  split_ifs with hn
  · rfl
  congr 1
  refine Finset.sum_congr rfl fun ⟨m₁, m₂⟩ hm₁ ↦ ?_
  rw [Finset.mem_antidiagonal] at hm₁
  split_ifs with hm₂
  · rw [ih _ (by omega), coeff_invOfUnit_congr (g := g) (by grind)]
  · rfl

open PowerSeries in
theorem PowerSeries.le_order_iff {R : Type*} [Semiring R] {f : R⟦X⟧} {n : ℕ} :
    n ≤ f.order ↔ ∀ i < n, f.coeff i = 0 :=
  ⟨fun h _i hi ↦ coeff_of_lt_order _ (Nat.cast_lt.mpr hi |>.trans_le h), nat_le_order _ _⟩

open PowerSeries in
theorem PowerSeries.lt_order_iff {R : Type*} [Semiring R] {f : R⟦X⟧} {n : ℕ} :
    n < f.order ↔ ∀ i ≤ n, f.coeff i = 0 := by
  rw [← ENat.add_one_le_iff (by simp), ← Nat.cast_succ, le_order_iff]
  simp

open PowerSeries in
theorem PowerSeries.C_natCast {R : Type*} [Semiring R] {k : ℕ} :
    C (k : R) = k := map_natCast _ _

open PowerSeries in
theorem PowerSeries.C_intCast {R : Type*} [Ring R] {k : ℤ} :
    C (k : R) = k := map_intCast _ _

open PowerSeries in
theorem PowerSeries.coeff_natCast {R : Type*} [Semiring R] {k i : ℕ} :
    (k : R⟦X⟧).coeff i = if i = 0 then k else 0 := by
  rw [← C_natCast, coeff_C, apply_ite Nat.cast, Nat.cast_zero]

open PowerSeries in
theorem PowerSeries.coeff_intCast {R : Type*} [Ring R] {k : ℤ} {i : ℕ} :
    (k : R⟦X⟧).coeff i = if i = 0 then k else 0 := by
  rw [← C_intCast, coeff_C, apply_ite Int.cast, Int.cast_zero]

/-- Truncated polynomials / power series of degree `< n`. -/
structure TruncPoly (R : Type*) (n : ℕ) where of ::
  /-- The list of coefficients. -/
  coeffs : Fin n → R
deriving Inhabited, DecidableEq

open Finset

namespace TruncPoly

variable {R : Type*} {n : ℕ}

theorem coeffs_injective : Function.Injective (coeffs : TruncPoly R n → Fin n → R) :=
  fun ⟨f⟩ ⟨g⟩ ↦ by grind

instance [Subsingleton (Fin n → R)] : Subsingleton (TruncPoly R n) :=
  coeffs_injective.subsingleton

instance [Zero R] : Zero (TruncPoly R n) where
  zero := ⟨fun _ ↦ 0⟩

/-- The coefficient of `X^i` in `f`. If `i ≥ n`, return the junk value `0`. -/
def coeff [Zero R] (f : TruncPoly R n) (i : ℕ) : R := if h : i < n then f.coeffs ⟨i, h⟩ else 0

theorem coeff_of [Zero R] {f : Fin n → R} {i : ℕ} (hi : i < n) :
    (of f).coeff i = f ⟨i, hi⟩ := by
  rw [coeff, dif_pos hi]

@[ext] theorem ext [Zero R]
    {f g : TruncPoly R n} (ih : ∀ i < n, f.coeff i = g.coeff i) : f = g := by
  obtain ⟨f⟩ := f
  obtain ⟨g⟩ := g
  congr
  ext i
  convert ih i i.2 <;> simp [coeff]

@[simp]
theorem coeff_eq_zero_of_ge [Zero R] {f : TruncPoly R n} {i : ℕ} (hi : n ≤ i) : f.coeff i = 0 := by
  rw [coeff, dif_neg (not_lt_of_ge hi)]

@[simp] theorem coeff_zero [Zero R] {i : ℕ} : (0 : TruncPoly R n).coeff i = 0 := by
  unfold coeff
  split_ifs <;> rfl

instance [Add R] : Add (TruncPoly R n) where
  add f g := ⟨fun i ↦ f.coeffs i + g.coeffs i⟩

@[simp] theorem coeff_add [AddZeroClass R] {f g : TruncPoly R n} {i : ℕ} :
    (f + g).coeff i = f.coeff i + g.coeff i := by
  unfold coeff
  split_ifs
  · rfl
  · simp

instance [Neg R] : Neg (TruncPoly R n) where
  neg f := ⟨fun i ↦ -f.coeffs i⟩

@[simp] theorem coeff_neg [NegZeroClass R] {f : TruncPoly R n} {i : ℕ} :
    (-f).coeff i = -f.coeff i := by
  unfold coeff
  split_ifs
  · rfl
  · simp

instance [Sub R] : Sub (TruncPoly R n) where
  sub f g := ⟨fun i ↦ f.coeffs i - g.coeffs i⟩

@[simp] theorem coeff_sub [SubNegZeroMonoid R] {f g : TruncPoly R n} {i : ℕ} :
    (f - g).coeff i = f.coeff i - g.coeff i := by
  unfold coeff
  split_ifs
  · rfl
  · simp

instance {α : Type*} [SMul α R] : SMul α (TruncPoly R n) where
  smul c f := ⟨fun i ↦ c • f.coeffs i⟩

@[simp] theorem coeff_smul {α : Type*} [Zero R] [SMulZeroClass α R] {c : α}
    {f : TruncPoly R n} {i : ℕ} : (c • f).coeff i = c • f.coeff i := by
  unfold coeff
  split_ifs
  · rfl
  · simp

instance [AddZeroClass R] : AddZeroClass (TruncPoly R n) :=
  fast_instance% (coeffs_injective (R := R) (n := n)).addZeroClass _ rfl fun _ _ ↦ rfl

instance [AddMonoid R] : AddMonoid (TruncPoly R n) :=
  fast_instance% (coeffs_injective (R := R) (n := n)).addMonoid _
    rfl (fun _ _ ↦ rfl) fun _ _ ↦ rfl

instance [AddCommMonoid R] : AddCommMonoid (TruncPoly R n) :=
  fast_instance% (coeffs_injective (R := R) (n := n)).addCommMonoid _
    rfl (fun _ _ ↦ rfl) fun _ _ ↦ rfl

instance [AddGroup R] : AddGroup (TruncPoly R n) :=
  fast_instance% (coeffs_injective (R := R) (n := n)).addGroup _
    rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) fun _ _ ↦ rfl

instance [AddCommGroup R] : AddCommGroup (TruncPoly R n) :=
  fast_instance% (coeffs_injective (R := R) (n := n)).addCommGroup _
    rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/-- Coefficient as an additive homomorphism. -/
@[simps] def coeffAddHom [AddZeroClass R] (i : ℕ) : TruncPoly R n →+ R where
  toFun f := f.coeff i
  map_zero' := by simp
  map_add' f g := by simp

@[simp] theorem coeff_sum [AddCommMonoid R] {ι : Type*} {s : Finset ι} {f : ι → TruncPoly R n}
    {i : ℕ} : (s.sum f).coeff i = s.sum (f · |>.coeff i) :=
  map_sum (coeffAddHom i) ..

/-- The list of all coefficients as an additive homomorphism. -/
@[simps] def coeffsAddHom [AddZeroClass R] : TruncPoly R n →+ Fin n → R where
  toFun f := f.coeffs
  map_zero' := rfl
  map_add' _ _ := rfl

instance [Semiring R] : Module R (TruncPoly R n) :=
  fast_instance% Function.Injective.module _ coeffsAddHom coeffs_injective fun _ _ ↦ rfl

instance [Semiring R] : Module.IsTorsionFree R (TruncPoly R n) where
  isSMulRegular r hr x y hxy := ext fun i _ ↦ hr.left <| by
    simpa using congr(($hxy).coeff i)

open Polynomial in
/-- A chosen lifting from truncated polynomials to polynomials where all the higher coefficients
are zero. -/
noncomputable def liftPoly [Semiring R] : TruncPoly R n →ₗ[R] R[X] where
  toFun f := ∑ i ∈ range n, C (f.coeff i) * X ^ i
  map_add' f g := by simp [add_mul, sum_add_distrib]
  map_smul' c f := by simp [smul_eq_C_mul, mul_sum, mul_assoc]

@[simp] theorem coeff_liftPoly [Semiring R] {f : TruncPoly R n} {i : ℕ} (hi : i < n) :
    (liftPoly f).coeff i = f.coeff i := by
  simp [liftPoly, coeff_of hi, hi]

/-- Multiplication by convolution. -/
instance [AddCommMonoid R] [Mul R] : Mul (TruncPoly R n) where
  mul f g := .of fun i ↦ ∑ p ∈ antidiagonal i.val, f.coeff p.1 * g.coeff p.2

@[simp] theorem coeff_mul [AddCommMonoid R] [Mul R] {f g : TruncPoly R n} {i : ℕ} (hi : i < n) :
    (f * g).coeff i = ∑ p ∈ antidiagonal i, f.coeff p.1 * g.coeff p.2 := by
  rw [coeff, dif_pos hi]
  rfl

instance [Zero R] [One R] : One (TruncPoly R n) where
  one := .of fun i ↦ if i.val = 0 then 1 else 0

instance [Zero R] [NatCast R] : NatCast (TruncPoly R n) where
  natCast n := .of fun i ↦ if i.val = 0 then n else 0

instance [AddCommMonoid R] [Mul R] [One R] : Pow (TruncPoly R n) ℕ where pow x n := npowRec n x

end TruncPoly

namespace PowerSeries
variable {R : Type*} [Semiring R] {f g : R⟦X⟧} {n : ℕ}

open TruncPoly

/-- The simp NF will be `PowerSeries.truncPoly`. -/
noncomputable def truncPolyAux (f : R⟦X⟧) (n : ℕ) :
    TruncPoly R n := .of fun i ↦ f.coeff i

theorem truncPolyAux_mul : (f * g).truncPolyAux n = f.truncPolyAux n * g.truncPolyAux n := by
  ext i hi
  rw [truncPolyAux, TruncPoly.coeff_mul hi, coeff_of hi, PowerSeries.coeff_mul]
  refine sum_congr rfl fun p hp ↦ ?_
  rw [mem_antidiagonal] at hp
  rw [truncPolyAux, truncPolyAux, coeff_of (by grind), coeff_of (by grind)]

theorem truncPolyAux_coe_liftPoly {f : TruncPoly R n} :
    (f.liftPoly : R⟦X⟧).truncPolyAux n = f := by
  ext i hi
  simp [liftPoly, ← Polynomial.coeToPowerSeries.ringHom_apply, truncPolyAux, coeff_of hi]
  simp [coeff_X_pow, coeff_of hi, hi]

theorem truncPolyAux_surjective : Function.Surjective (truncPolyAux (R := R) · n) :=
  fun _ ↦ ⟨_, truncPolyAux_coe_liftPoly⟩

theorem truncPolyAux_natCast {k : ℕ} : (k : R⟦X⟧).truncPolyAux n = k := by
  ext i hi
  simp_rw [truncPolyAux, coeff_of hi, coeff_natCast, apply_ite Nat.cast, Nat.cast_zero]
  rfl

theorem truncPolyAux_one :
    (1 : R⟦X⟧).truncPolyAux n = 1 := by
  rw [← Nat.cast_one, truncPolyAux_natCast]
  ext i hi
  simp_rw [TruncPoly.coeff, dif_pos hi]
  exact ite_congr rfl (by simp) (by simp)

theorem truncPolyAux_pow {k : ℕ} :
    (f ^ k).truncPolyAux n = f.truncPolyAux n ^ k := by
  induction k with
  | zero => exact truncPolyAux_one
  | succ k ih => exact (truncPolyAux_mul).trans congr($ih * _)

noncomputable instance _root_.TruncPoly.semiring : Semiring (TruncPoly R n) :=
  fast_instance% truncPolyAux_surjective.semiring _ rfl truncPolyAux_one (fun _ _ ↦ rfl)
    (fun _ _ ↦ truncPolyAux_mul) (fun _ _ ↦ rfl) (fun _ _ ↦ truncPolyAux_pow)
    fun _ ↦ truncPolyAux_natCast

/-- The canonical ring homomorphism from power series to truncated polynomials. -/
noncomputable def truncPoly (R : Type*) [Semiring R] (n : ℕ) :
    R⟦X⟧ →+* TruncPoly R n where
  toFun f := f.truncPolyAux n
  map_one' := truncPolyAux_one
  map_mul' _ _ := truncPolyAux_mul
  map_zero' := rfl
  map_add' _ _ := rfl

open Lean PrettyPrinter Delaborator SubExpr in
/-- Delaborator for `truncPoly` to omit the ring. -/
meta def delabTruncPoly : Delab := do
  let tD ← withNaryFn delab
  let nD ← withNaryArg 2 delab
  `($tD $nD)

open Lean PrettyPrinter Delaborator SubExpr in
/-- Delaborator for `truncPoly` to omit the ring when it is applied to a power series. -/
@[app_delab DFunLike.coe]
meta def delabTruncPolyApp : Delab := do
  let e ← getExpr
  let (_, #[_, _, _, _, f, _]) := e.getAppFnArgs | failure
  let (`PowerSeries.truncPoly, #[_, _, _]) := f.getAppFnArgs | failure
  let tD ← withNaryArg 4 delabTruncPoly
  let pD ← withNaryArg 5 delab
  `($tD $pD)

@[simp] theorem truncPoly_coe_liftPoly {f : TruncPoly R n} :
    (f.liftPoly : R⟦X⟧).truncPoly R n = f :=
  truncPolyAux_coe_liftPoly

@[simp] theorem coeff_truncPoly {f : R⟦X⟧} {i : ℕ} (hi : i < n) :
    (truncPoly R n f).coeff i = f.coeff i := by
  rw [TruncPoly.coeff, dif_pos hi]
  rfl

theorem truncPoly_surjective : Function.Surjective (truncPoly R n) :=
  fun _ ↦ ⟨_, truncPoly_coe_liftPoly⟩

@[simp] theorem truncPoly_smul (r : R) (p : R⟦X⟧) :
    (r • p).truncPoly R n = r • p.truncPoly R n := by
  ext; simp [*]

@[simp] theorem truncPoly_C_mul (r : R) (p : TruncPoly R n) :
    (C r).truncPoly R n * p = r • p := by
  obtain ⟨p, rfl⟩ := truncPoly_surjective p
  rw [← map_mul, ← smul_eq_C_mul, truncPoly_smul]

theorem truncPoly_eq_iff' {g : TruncPoly R n} :
    f.truncPoly R n = g ↔ ∀ i < n, f.coeff i = g.coeff i := by
  rw [TruncPoly.ext_iff]
  exact forall₂_congr fun i hi ↦ by rw [coeff_truncPoly hi]

theorem truncPoly_eq_iff :
    f.truncPoly R n = g.truncPoly R n ↔ ∀ i < n, f.coeff i = g.coeff i := by
  rw [TruncPoly.ext_iff]
  exact forall₂_congr fun i hi ↦ by rw [coeff_truncPoly hi, coeff_truncPoly hi]

@[ext low]
theorem ext_truncPoly (h : ∀ n, f.truncPoly R n = g.truncPoly R n) : f = g := by
  ext n
  rw [← coeff_truncPoly n.lt_succ_self, h, coeff_truncPoly n.lt_succ_self]

theorem truncPoly_eq_zero : f.truncPoly R n = 0 ↔ n ≤ f.order := by
  simp [le_order_iff, truncPoly_eq_iff']
alias ⟨_, truncPoly_eq_zero_of_le_order⟩ := truncPoly_eq_zero

theorem truncPoly_pow_eq_zero (hf : f.constantCoeff = 0) {m n : ℕ} (hm : m ≤ n) :
    f.truncPoly R m ^ n = 0 := by
  rw [← map_pow, truncPoly_eq_zero]
  rw [← one_le_order_iff_constCoeff_eq_zero] at hf
  grw [← le_order_pow, ← hf, nsmul_one, Nat.cast_le, hm]

end PowerSeries

-- KL: This is `(PowerSeries.truncPoly R n).comp Polynomial.coeToPowerSeries.ringHom`.
/- namespace Polynomial
variable {R : Type*} [Semiring R]

open TruncPoly

def trunc (R : Type*) [Semiring R] (n : ℕ) : R[X] →+* TruncPoly R n where
  toFun f := .of fun i ↦ f.coeff i
  map_zero' := rfl
  map_one' := by ext i hi; simp [coeff_of hi, coeff_one]; rfl
  map_add' _ _ := by ext; simp [coeff_of, *]
  map_mul' _ _ := by
    ext i hi
    rw [coeff_of hi, coeff_mul, TruncPoly.coeff_mul hi]
    refine sum_congr rfl fun p hp ↦ ?_
    rw [mem_antidiagonal] at hp
    rw [coeff_of (by grind), coeff_of (by grind)]

end Polynomial
 -/

namespace TruncPoly
variable {R : Type*} {n : ℕ}

open PowerSeries

noncomputable instance [CommSemiring R] : CommSemiring (TruncPoly R n) :=
  fast_instance% truncPolyAux_surjective.commSemiring _ rfl truncPolyAux_one (fun _ _ ↦ rfl)
    (fun _ _ ↦ truncPolyAux_mul) (fun _ _ ↦ rfl) (fun _ _ ↦ truncPolyAux_pow)
    (fun _ ↦ truncPolyAux_natCast)

instance [Zero R] [IntCast R] : IntCast (TruncPoly R n) where
  intCast n := .of fun i ↦ if i.val = 0 then n else 0

theorem truncPolyAux_intCast [Ring R] {k : ℤ} : (k : R⟦X⟧).truncPolyAux n = k := by
  ext i hi
  simp_rw [truncPolyAux, coeff_of hi, coeff_intCast, apply_ite Int.cast, Int.cast_zero]
  rfl

noncomputable instance [Ring R] : Ring (TruncPoly R n) :=
  fast_instance% truncPolyAux_surjective.ring _ rfl truncPolyAux_one (fun _ _ ↦ rfl)
    (fun _ _ ↦ truncPolyAux_mul) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)  (fun _ _ ↦ rfl)
    (fun _ _ ↦ truncPolyAux_pow) (fun _ ↦ truncPolyAux_natCast) fun _ ↦ truncPolyAux_intCast

noncomputable instance [CommRing R] : CommRing (TruncPoly R n) :=
  fast_instance% {}

section Ring
variable [Ring R]

/-- Inverse of a truncated polynomial -/
noncomputable def invOfUnit (f : TruncPoly R n) (u : Rˣ) : TruncPoly R n :=
  ((liftPoly f : R⟦X⟧).invOfUnit u).truncPoly R n

theorem _root_.PowerSeries.truncPoly_invOfUnit {f : R⟦X⟧} {u : Rˣ} :
    (f.invOfUnit u).truncPoly R n = (f.truncPoly R n).invOfUnit u := by
  rw [invOfUnit, truncPoly_eq_iff]
  intro i hi
  refine coeff_invOfUnit_congr fun j hj ↦ ?_
  rw [Polynomial.coeff_coe, coeff_liftPoly (hj.trans_lt hi), coeff_truncPoly (hj.trans_lt hi)]

theorem invOfUnit_mul {f : TruncPoly R n} {u : Rˣ} (hf : f.coeff 0 = u) :
    invOfUnit f u * f = 1 := by
  obtain _ | n := n
  · subsingleton
  nth_rw 2 [← truncPoly_coe_liftPoly (f := f)]
  rw [invOfUnit, ← map_mul, invOfUnit_mul, map_one]
  rwa [← coeff_zero_eq_constantCoeff, Polynomial.coeff_coe, coeff_liftPoly (by grind)]

theorem mul_invOfUnit {f : TruncPoly R n} {u : Rˣ} (hf : f.coeff 0 = u) :
    f * invOfUnit f u = 1 := by
  obtain _ | n := n
  · subsingleton
  nth_rw 1 [← truncPoly_coe_liftPoly (f := f)]
  rw [invOfUnit, ← map_mul, mul_invOfUnit, map_one]
  rwa [← coeff_zero_eq_constantCoeff, Polynomial.coeff_coe, coeff_liftPoly (by grind)]

end Ring

end TruncPoly
