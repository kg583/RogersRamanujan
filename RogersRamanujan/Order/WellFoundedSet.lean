module

public import Mathlib.Order.WellFoundedSet

/-! # Partially well-ordered sets

Equivalent characterizations of `Set.IsPWO` and its behavior under order embeddings.
-/

@[expose] public section

namespace Set

theorem isPWO_iff_exists {α : Type*} [Preorder α] {s : Set α} :
    s.IsPWO ↔ ∀ f : ℕ → α, (∀ (n : ℕ), f n ∈ s) → ∃ m n, m < n ∧ f m ≤ f n :=
  ⟨fun hs f hf ↦ hs (⟨_, hf ·⟩), fun hs f ↦ hs (f ·) (by grind)⟩

theorem isPWO_image_iff {α β : Type*} [Preorder α] [Preorder β] (f : α ↪o β)
    (s : Set α) : (f '' s).IsPWO ↔ s.IsPWO := by
  refine ⟨fun h a ↦ ?_, (·.image_of_monotone f.monotone)⟩
  obtain ⟨m, n, h1, h2⟩ := h (Subtype.map f (by grind) ∘ a)
  exact ⟨m, n, h1, by simpa using h2⟩

theorem IsPWO.of_image {α β : Type*} [Preorder α] [Preorder β] (f : α ↪o β)
    {s : Set α} (h : (f '' s).IsPWO) : s.IsPWO :=
  (isPWO_image_iff f s).mp h

end Set
