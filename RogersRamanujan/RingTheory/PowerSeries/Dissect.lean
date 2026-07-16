module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Data.ZMod.Basic

public import RogersRamanujan.RingTheory.PowerSeries.DiscreteTopology
public import RogersRamanujan.RingTheory.PowerSeries.Evaluation

/-! # Dissection of power series

This file develops the `l`-dissection of a power series (splitting it into pieces supported on a
single residue class mod `l`).

## Main definitions

* `PowerSeries.dissect`: the piece of a power series supported on one residue class mod `l`
* `PowerSeries.dissectShift`: given a power series `f`, shift it to live entirely on `r` mod `l`
* `PowerSeries.Supp`: a power series which is supported on a residue class `r` mod `l`

## Main results

* `PowerSeries.sum_dissect`: a power series is the sum of its `l` dissection pieces
* `PowerSeries.Supp.dissect_eq_of_sum`: dissecting a sum of power series supported on every
  `r` mod `l` yields one of the addends
-/

@[expose] public section

open PowerSeries DiscreteTopology

namespace PowerSeries

/-- The piece of `f` supported on the residue class `r` mod `l`: the power series obtained from
`f` by zeroing out every coefficient at an index `n` with `n % l ≠ r`. -/
noncomputable def dissect {R : Type*} [Semiring R] (f : R⟦X⟧) (l : ℕ+) (r : ZMod l) : R⟦X⟧ :=
  mk fun n ↦ if (n : ZMod l) = r then f.coeff n else 0

@[simp]
theorem coeff_dissect {R : Type*} [Semiring R] (f : R⟦X⟧) (l : ℕ+) (r : ZMod l) (n : ℕ) :
    (f.dissect l r).coeff n = if (n : ZMod l) = r then f.coeff n else 0 :=
  coeff_mk _ _

theorem coeff_dissect_of_mod {R : Type*} [Semiring R] (f : R⟦X⟧) {l : ℕ+} {r : ZMod l} {n : ℕ}
    (h : (n : ZMod l) = r) : (f.dissect l r).coeff n = f.coeff n := by simp [h]

theorem coeff_dissect_of_not_mod {R : Type*} [Semiring R] (f : R⟦X⟧) {l : ℕ+} {r : ZMod l} {n : ℕ}
    (h : (n : ZMod l) ≠ r) : (f.dissect l r).coeff n = 0 := by simp [h]

/-- A power series is the sum of its `l` dissection pieces, one for each residue mod `l`. -/
theorem sum_dissect {R : Type*} [Semiring R] (f : R⟦X⟧) {l : ℕ+} :
    ∑ r ∈ Finset.range l, f.dissect l r = f := by
  ext n
  rw [map_sum, Finset.sum_eq_single (n % l)]
  · exact coeff_dissect_of_mod f (ZMod.natCast_mod n l).symm
  · refine fun r hrmem hr ↦ coeff_dissect_of_not_mod f (fun h ↦ hr ?_)
    have := (ZMod.natCast_eq_natCast_iff' n r l).mp h
    rw [Nat.mod_eq_of_lt (Finset.mem_range.mp hrmem)] at this
    exact this.symm
  · exact fun h ↦ absurd (Finset.mem_range.mpr (Nat.mod_lt n l.pos)) h

/-- `f.dissect l r` reindexed along the residue class `n = l * m + r`: the power series in `m`
with coefficients `f.coeff (l * m + r)`. -/
noncomputable def dissectShift {R : Type*} [Semiring R] (f : R⟦X⟧) (l : ℕ+) (r : ZMod l) : R⟦X⟧ :=
  mk fun m ↦ f.coeff (l * m + r.val)

@[simp]
theorem coeff_dissectShift {R : Type*} [Semiring R] (f : R⟦X⟧) (l : ℕ+) (r : ZMod l) (m : ℕ) :
    (f.dissectShift l r).coeff m = f.coeff (l * m + r.val) :=
  coeff_mk _ _

/-- Evaluating the `r`-mod-`l` dissection piece of `F` at a topologically nilpotent `q` is the
sum of `F`'s coefficients along the residue class `r`, each paired with the matching power of
`q`. -/
theorem hasSum_intEval_dissect {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [NonarchimedeanRing R] [CompleteSpace R] [T2Space R] (F : ℤ⟦X⟧) {l : ℕ+} {r : ZMod l} {q : R}
    (hq : IsTopologicallyNilpotent q := by simp) :
    HasSum (fun m : ℕ ↦ (F.dissectShift l r).coeff m * q ^ (l * m + r.val))
      (intEval q (F.dissect l r)) := by
  have hinj : Function.Injective (fun m : ℕ ↦ l * m + r.val) := fun a b hab ↦ by
    simp only [add_left_inj] at hab
    exact Nat.eq_of_mul_eq_mul_left (by simp) hab
  have hzero : ∀ n : ℕ, n ∉ Set.range (fun m : ℕ ↦ l * m + r.val) →
      (F.dissect l r).coeff n * q ^ n = 0 := by
    intro n hn
    have hne : (n : ZMod l) ≠ r := by
      intro h
      obtain ⟨k, hk⟩ := (ZMod.natCast_eq_iff l n r).mp h
      exact hn ⟨k, by dsimp only; omega⟩
    simp [coeff_dissect_of_not_mod F hne]
  simpa [Function.comp_def] using (hinj.hasSum_iff hzero).mpr (hasSum_intEval hq (F.dissect l r))

/-- `Supp l r f`: The power series `f` over `ZMod l` is supported on the residue class
`r` mod `l` -/
def Supp (l : ℕ+) (r : ZMod l) (f : (ZMod l)⟦X⟧) : Prop :=
  ∀ n : ℕ, (n : ZMod l) ≠ r → f.coeff n = 0

namespace Supp

@[simp]
theorem add {l : ℕ+} {r : ZMod l} {f g : (ZMod l)⟦X⟧} (hf : Supp l r f) (hg : Supp l r g) :
    Supp l r (f + g) := by
  intro n hn; simp [map_add, hf n hn, hg n hn]

@[simp]
theorem mul {l : ℕ+} {r r' : ZMod l} {f g : (ZMod l)⟦X⟧} (hf : Supp l r f) (hg : Supp l r' g) :
    Supp l (r + r') (f * g)  := by
  intro n hn
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  by_cases hi : (p.1 : ZMod l) = r
  · by_cases hj : (p.2 : ZMod l) = r'
    · exact absurd (by rw [← hp]; push_cast; rw [hi, hj]) hn
    · simp [hg p.2 hj]
  · simp [hf p.1 hi]

@[simp]
theorem C {l : ℕ+} (c : ZMod l) : Supp l 0 (PowerSeries.C c) := by
  intro n hn
  have h0 : n ≠ 0 := by by_contra; rw [this] at hn; simp at hn
  rw [PowerSeries.coeff_C, if_neg h0]

@[simp]
theorem pow {l : ℕ+} {r : ZMod l} {f : (ZMod l)⟦X⟧} (hf : Supp l r f) :
    ∀ k : ℕ, Supp l (k * r) (f ^ k)
  | 0 => by simpa using Supp.C 1
  | k + 1 => by
    have h := (hf.pow k).mul hf
    rwa [← pow_succ, show (k : ZMod l) * r + r = (↑(k + 1) : ZMod l) * r by push_cast; ring] at h

@[simp]
theorem const_mul {l : ℕ+} {r : ZMod l} {f : (ZMod l)⟦X⟧} (c : ZMod l) (hf : Supp l r f) :
    Supp l r (PowerSeries.C c * f) := by simpa using (Supp.C c).mul hf

@[simp]
theorem dissect_self {l : ℕ+} {r : ZMod l} {f : (ZMod l)⟦X⟧} (hf : Supp l r f) :
    f.dissect l r = f := by
  ext n; rw [coeff_dissect]
  by_cases h : (n : ZMod l) = r
  · rw [if_pos h]
  · rw [if_neg h, hf n h]

@[simp]
theorem dissect_ne {l : ℕ+} {r r' : ZMod l} {f : (ZMod l)⟦X⟧} (hf : Supp l r f)
    (hrr' : r ≠ r') : f.dissect l r' = 0 := by
  ext n; rw [coeff_dissect]
  by_cases h : (n : ZMod l) = r'
  · rw [if_pos h, hf n (by rw [h]; exact hrr'.symm), map_zero]
  · rw [if_neg h, map_zero]

@[simp]
theorem dissect_supp {l : ℕ+} {r : ZMod l} (f : (ZMod l)⟦X⟧) :
    Supp l r (f.dissect l r) := by
  intro n hn; rw [coeff_dissect] at *; rw [if_neg hn]

@[simp]
theorem dissect_add {l : ℕ+} {r : ZMod l} (f g : (ZMod l)⟦X⟧) :
    (f + g).dissect l r = f.dissect l r + g.dissect l r := by
  ext n; simp only [map_add, coeff_dissect]; split_ifs <;> simp

theorem dissect_sum {ι : Type*} {l : ℕ+} {r : ZMod l} (s : Finset ι) (f : ι → (ZMod l)⟦X⟧) :
    (∑ i ∈ s, f i).dissect l r = ∑ i ∈ s, (f i).dissect l r := by
  classical
  induction s using Finset.induction with
  | empty => ext n; simp [coeff_dissect]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, dissect_add, ih]

/-- If `f` is the sum of pieces `Rf d`, one for each residue class mod `l`, and each `Rf d` is
supported on residue class `d`, then `f`'s dissection on residue class `a` recovers `Rf a.val`. -/
theorem dissect_eq_of_sum {l : ℕ+} {Rf : ℕ → (ZMod l)⟦X⟧} {f : (ZMod l)⟦X⟧} (a : ZMod l)
    (hsum : f = ∑ d ∈ Finset.range l, Rf d) (hSupp : ∀ d : ℕ, d < l → Supp l d (Rf d)) :
    f.dissect l a = Rf a.val := by
  rw [hsum, show (∑ d ∈ Finset.range l, Rf d).dissect l a
      = ∑ d ∈ Finset.range l, (Rf d).dissect l a from dissect_sum _ _]
  rw [Finset.sum_eq_single a.val]
  · have hSa : Supp l a (Rf a.val) := by
      nth_rewrite 1 [← ZMod.natCast_zmod_val a]; exact hSupp a.val a.val_lt
    exact dissect_self hSa
  · intro d hdmem hd
    refine dissect_ne (hSupp d (Finset.mem_range.mp hdmem)) (fun hcontra => hd ?_)
    have := congrArg ZMod.val hcontra
    rwa [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hdmem)] at this
  · exact fun h => absurd (Finset.mem_range.mpr a.val_lt) h

/-- Peeling one factor supported on a single residue class out of a dissected product. -/
theorem dissect_mul_supp {l : ℕ+} {r r' : ZMod l} {f g : (ZMod l)⟦X⟧}
    (hg : Supp l r' g) :
    (f * g).dissect l r = (f.dissect l (r - r')) * g := by
  ext n
  rw [coeff_dissect, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  by_cases hn : (n : ZMod l) = r
  · rw [if_pos hn]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    rw [coeff_dissect]
    by_cases hp2 : g.coeff p.2 = 0
    · rw [hp2, mul_zero, mul_zero]
    · have hjr : (p.2 : ZMod l) = r' := by by_contra hne; exact hp2 (hg p.2 hne)
      have hc := congrArg (Nat.cast : ℕ → ZMod l) hp
      push_cast at hc
      rw [hn, hjr] at hc
      rw [if_pos (by linear_combination hc)]
  · rw [if_neg hn]
    refine (Finset.sum_eq_zero fun p hp => ?_).symm
    rw [Finset.mem_antidiagonal] at hp
    rw [coeff_dissect]
    by_cases hp1 : (p.1 : ZMod l) = r - r'
    · rw [if_pos hp1]
      by_cases hp2 : g.coeff p.2 = 0
      · rw [hp2, mul_zero]
      · have hjr : (p.2 : ZMod l) = r' := by by_contra hne; exact hp2 (hg p.2 hne)
        have hc := congrArg (Nat.cast : ℕ → ZMod l) hp
        push_cast at hc
        exact absurd (by rw [← hc, hp1, hjr]; ring) hn
    · rw [if_neg hp1, zero_mul]

theorem dissect_mul_dissect_sum {l : ℕ+} {r : ZMod l} (f g : (ZMod l)⟦X⟧) :
    (f * g).dissect l r
      = ∑ r' ∈ Finset.range l, (f.dissect l (r - r')) * g.dissect l r' := by
  conv_lhs => rw [← sum_dissect g (l := l), Finset.mul_sum, dissect_sum]
  exact Finset.sum_congr rfl fun r' _ => dissect_mul_supp (dissect_supp g)

end Supp

@[simp]
theorem coeff_mul_eq_zero_of_forall {R : Type*} [CommSemiring R] (f g : R⟦X⟧) (m : ℕ)
    (h : ∀ i j, i + j = m → f.coeff i = 0 ∨ g.coeff j = 0) : (f * g).coeff m = 0 := by
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  rcases h p.1 p.2 hp with hh | hh <;> simp [hh]

end PowerSeries

lemma isNilpotent_pow_X_p (p : ℕ) (hp : Nat.Prime p) :
    IsTopologicallyNilpotent (X ^ p : (ZMod p)⟦X⟧) := by
  simp only [isTopologicallyNilpotent_iff_isNilpotent_constantCoeff, map_pow, constantCoeff_X]
  rw [zero_pow]
  · simp only [IsNilpotent.zero]
  exact Nat.Prime.ne_zero hp
