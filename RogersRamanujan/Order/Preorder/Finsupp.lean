module

public import Mathlib.Order.Preorder.Finsupp

/-! # Decidable order on `Finsupp`

Decidability of `≤` on `ι →₀ M` when `M` has a decidable order.
-/

@[expose] public section

namespace Finsupp

instance {ι M : Type*} [Preorder M] [Zero M] [DecidableLE M] : DecidableLE (ι →₀ M) := fun f g ↦
  decidable_of_iff ((∀ i ∈ f.support, f i ≤ g i) ∧ (∀ i ∈ g.support, f i ≤ g i)) <| by
    rw [le_def]; grind

end Finsupp
