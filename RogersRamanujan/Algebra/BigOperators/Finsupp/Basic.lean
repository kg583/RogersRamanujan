module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-! # Big operators over `Finsupp`
-/

@[expose] public section

open Finset

namespace Finsupp

/-- The multivariate power `∏ i, q i ^ v i` indexed by a `Finsupp` `v : σ →₀ ℕ`. -/
def pow {σ S : Type*} [CommMonoid S] (v : σ →₀ ℕ) (q : σ → S) : S :=
  v.prod (q · ^ ·)

theorem pow_def {σ S : Type*} [CommMonoid S] (v : σ →₀ ℕ) (q : σ → S) :
    v.pow q = v.prod (q · ^ ·) := rfl

theorem pow_fintype {σ S : Type*} [Fintype σ] [CommMonoid S] (v : σ →₀ ℕ) (q : σ → S) :
    v.pow q = ∏ i, q i ^ v i := prod_pow ..

theorem _root_.map_finsuppPow {σ S T : Type*} [CommMonoid S] [CommMonoid T]
    {v : σ →₀ ℕ} {q : σ → S} {F : Type*} [FunLike F S T] [MonoidHomClass F S T] (f : F) :
    f (v.pow q) = v.pow (f ∘ q) := (map_finsuppProd ..).trans <| by simp [pow_def]

@[simp] theorem prod_pow_eq_pow {σ S : Type*} [CommMonoid S] (v : σ →₀ ℕ) (q : σ → S) :
    v.prod (q · ^ ·) = v.pow q := rfl

@[simp] theorem pow_zero {σ S : Type*} [CommMonoid S] (q : σ → S) :
    (0 : σ →₀ ℕ).pow q = 1 := prod_zero_index

@[simp] theorem pow_single {σ S : Type*} [CommMonoid S] (q : σ → S) (i : σ) (n : ℕ) :
    (single i n).pow q = q i ^ n := prod_single_index (by simp)

@[simp] theorem pow_add {σ S : Type*} [CommMonoid S] (v₁ v₂ : σ →₀ ℕ) (q : σ → S) :
    (v₁ + v₂).pow q = v₁.pow q * v₂.pow q :=
  open Classical in prod_add_index (by simp) (by simp [_root_.pow_add])

@[simp] theorem pow_sum {ι σ S : Type*} [CommMonoid S] (s : Finset ι) (v : ι → σ →₀ ℕ)
    (q : σ → S) : (∑ i ∈ s, v i).pow q = ∏ i ∈ s, (v i).pow q := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s his ih => simp [ih]

@[simp] theorem pow_finsuppSum {ι α σ S : Type*} [CommMonoid S] [Zero α] (s : ι →₀ α)
    (v : ι → α → σ →₀ ℕ) (q : σ → S) : (s.sum v).pow q = s.prod fun i a ↦ (v i a).pow q :=
  pow_sum ..

end Finsupp
