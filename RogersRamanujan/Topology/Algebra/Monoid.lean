module

import RogersRamanujan.Order.Filter.Cofinite
import RogersRamanujan.Order.Filter.Prod
import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Order.Filter.Cofinite
import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs

/-! # Continuous multiplication

Existence of neighborhoods of `0` whose product lies in a given neighborhood.
-/

@[expose] public section

open Filter Topology

theorem exists_nhds_zero_mul_mem
    {M : Type*} [MulZeroClass M] [TopologicalSpace M] [ContinuousMul M]
    {U : Set M} (hU : U ∈ 𝓝 0) :
    ∃ V ∈ 𝓝 0, ∀ x₁ ∈ V, ∀ x₂ ∈ V, x₁ * x₂ ∈ U :=
  mem_prod_self_iff'.mp <| nhds_prod_eq.rec <| continuous_mul.tendsto (0, 0) <| by simpa using hU

theorem exists_nhds_zero_mul_mem_left
    {M : Type*} [MulZeroClass M] [TopologicalSpace M] [ContinuousMul M]
    {U : Set M} (hU : U ∈ 𝓝 0) (a : M) :
    ∃ V₁ ∈ 𝓝 a, ∃ V₂ ∈ 𝓝 0, ∀ x₁ ∈ V₁, ∀ x₂ ∈ V₂, x₁ * x₂ ∈ U :=
  mem_prod_iff'.mp <| nhds_prod_eq.rec <| continuous_mul.tendsto (a, 0) <| by simpa using hU

theorem exists_nhds_zero_mul_mem_right
    {M : Type*} [MulZeroClass M] [TopologicalSpace M] [ContinuousMul M]
    {U : Set M} (hU : U ∈ 𝓝 0) (a : M) :
    ∃ V₁ ∈ 𝓝 0, ∃ V₂ ∈ 𝓝 a, ∀ x₁ ∈ V₁, ∀ x₂ ∈ V₂, x₁ * x₂ ∈ U :=
  mem_prod_iff'.mp <| nhds_prod_eq.rec <| continuous_mul.tendsto (0, a) <| by simpa using hU

theorem tendsto_prod_cofinite_nhds_zero_of_fin {M α : Type*} {n : ℕ} [TopologicalSpace M]
    [CommMonoidWithZero M] [ContinuousMul M] {f : Fin n → α → M}
    (hf : ∀ i, Tendsto (f i) cofinite (𝓝 0)) :
    Tendsto (fun x : Fin n → α ↦ ∏ i, f i (x i)) cofinite (𝓝 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp_rw [Fin.prod_univ_succ, ← (Fin.consEquiv _).map_cofinite,
      tendsto_map'_iff, Function.comp_def, Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
    convert tendsto_mul_cofinite_nhds_zero (hf 0) (ih (f := (f ·.succ)) (by grind))

theorem tendsto_prod_cofinite_nhds_zero {M α σ : Type*} [Fintype σ] [TopologicalSpace M]
    [CommMonoidWithZero M] [ContinuousMul M] {f : σ → α → M}
    (hf : ∀ i, Tendsto (f i) cofinite (𝓝 0)) :
    Tendsto (fun x : σ → α ↦ ∏ i, f i (x i)) cofinite (𝓝 0) := by
  let e := Fintype.equivFin σ
  convert (tendsto_prod_cofinite_nhds_zero_of_fin (f := f ∘ e.symm) (by grind)).comp
    (f := e.piCongrLeft fun _ ↦ α) (Equiv.injective _).tendsto_cofinite
  simp [Equiv.piCongrLeft, ← e.prod_comp]
