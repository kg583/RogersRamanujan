module

public import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Lattice
public import Mathlib.Order.Filter.Bases.Basic
import Mathlib.Order.Filter.Bases.Finite
import Mathlib.Order.Filter.Tendsto

/-! # Finite intersections of filter bases

The basis of `iInf l` for a finite family of filters `l`.
-/

@[expose] public section

open Filter Finset

namespace Filter

theorem HasBasis.iInf_finite
    {α : Type*} {ι : Type*} [Finite ι] {ι' : ι → Type*} {l : ι → Filter α}
    {p : (i : ι) → ι' i → Prop} {s : (i : ι) → ι' i → Set α}
    (hl : ∀ i, (l i).HasBasis (p i) (s i)) :
    (iInf l).HasBasis (fun f : (i : ι) → ι' i ↦ ∀ i, p i (f i)) fun f ↦ ⋂ i, s i (f i) := by
  classical
  choose d hd using fun i ↦ (hl i).ex_mem
  refine (HasBasis.iInf hl).to_hasBasis (fun j hj ↦ ?_) fun j hj ↦ ?_
  · exact ⟨fun i ↦ if hi : i ∈ j.1 then j.2 ⟨i, hi⟩ else d i, by grind,
      by simp [Set.subset_def]; grind⟩
  · exact ⟨⟨.univ, fun i ↦ j i.1⟩, ⟨by simp, by grind⟩, by simp⟩

theorem HasBasis.finset_inf
    {α : Type*} {ι : Type*} {ι' : ι → Type*} {l : ι → Filter α} {t : Finset ι}
    {p : (i : ι) → ι' i → Prop} {s : (i : ι) → ι' i → Set α}
    (hl : ∀ i ∈ t, (l i).HasBasis (p i) (s i)) :
    (t.inf l).HasBasis (fun f : (i : ι) → i ∈ t → ι' i ↦ ∀ i hi, p i (f i hi))
      fun f ↦ t.attach.inf fun i ↦ s i.1 (f i.1 i.2) := by
  classical
  choose d hd using fun i hi ↦ (hl i hi).ex_mem
  rw [← inf_attach, attach_eq_univ, inf_univ_eq_iInf]
  refine (HasBasis.iInf_finite fun i ↦ hl i.1 i.2).to_hasBasis (fun j hj ↦ ?_) fun j hj ↦ ?_
  · refine ⟨fun i hi ↦ j ⟨i, hi⟩, by grind, by simp⟩
  · refine ⟨fun i ↦ j i.1 i.2, by grind, by simp⟩

@[simp] theorem tendsto_finsetSup
    {α β ι : Type*} {f : α → β} {x : ι → Filter α} {s : Finset ι} {y : Filter β} :
    Tendsto f (s.sup x) y ↔ ∀ i ∈ s, Tendsto f (x i) y := by
  simp [Finset.sup_eq_iSup]

end Filter
