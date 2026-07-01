module

public import Mathlib.Order.WellFoundedSet

/-! # Antichains and partial well-ordering

An antichain is partially well-ordered iff it is finite.
-/

@[expose] public section

namespace IsAntichain

theorem isPWO_iff_finite {α : Type*} [Preorder α] {s : Set α}
    (hs : IsAntichain (· ≤ ·) s) : s.IsPWO ↔ s.Finite := hs.partiallyWellOrderedOn_iff

end IsAntichain
