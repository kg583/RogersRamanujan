module

public import Mathlib.Order.Filter.Defs
import Mathlib.Order.Filter.Prod

/-! # Product filters

Helpers about `Tendsto` against a product filter and `Filter.mem_prod_iff`.
-/

@[expose] public section

open Filter

namespace Filter.Tendsto

theorem fst' {α β γ : Type*} {f : α → γ}
    {s : Filter α} {t : Filter β} {u : Filter γ}
    (hf : Tendsto f s u) : Tendsto (fun p : α × β ↦ f p.1) (s ×ˢ t) u :=
  hf.comp tendsto_fst

theorem snd' {α β γ : Type*} {f : β → γ}
    {s : Filter α} {t : Filter β} {u : Filter γ}
    (hf : Tendsto f t u) : Tendsto (fun p : α × β ↦ f p.2) (s ×ˢ t) u :=
  hf.comp tendsto_snd

end Filter.Tendsto

theorem Filter.mem_prod_iff'
    {α β : Type*} {fa : Filter α} {fb : Filter β} {s : Set (α × β)} :
    s ∈ fa ×ˢ fb ↔ ∃ sa ∈ fa, ∃ sb ∈ fb, ∀ xa ∈ sa, ∀ xb ∈ sb, (xa, xb) ∈ s := by
  simp [mem_prod_iff, Set.prod_subset_iff]

theorem Filter.mem_prod_self_iff'
    {α : Type*} {f : Filter α} {s : Set (α × α)} :
    s ∈ f ×ˢ f ↔ ∃ t ∈ f, ∀ x₁ ∈ t, ∀ x₂ ∈ t, (x₁, x₂) ∈ s := by
  rw [mem_prod_iff']
  refine ⟨fun ⟨s₁, hs₁, s₂, hs₂, hs⟩ ↦ ⟨s₁ ∩ s₂, inter_mem hs₁ hs₂, by grind⟩, by grind⟩
