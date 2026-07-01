module

public import Mathlib.Data.Finsupp.Defs

/-! # `Finsupp` definitions
-/

@[expose] public section

namespace Finsupp

instance {ι α : Type*} [Zero α] [DecidableEq α] : DecidableEq (ι →₀ α) := fun f g ↦
  decidable_of_iff ((∀ i ∈ f.support, f i = g i) ∧ (∀ i ∈ g.support, f i = g i)) <| by
    simp [Finsupp.ext_iff]; grind

end Finsupp
