module

public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Order.Hom.Basic

/-! # Order embeddings

The right-addition order embedding `addRight'`.
-/

@[expose] public section

namespace OrderEmbedding

/-- The order embedding `· + x` given by right addition. -/
def addRight' {α : Type*} [Add α] [IsRightCancelAdd α]
    [LE α] [AddRightMono α] [AddRightReflectLE α] (x : α) : α ↪o α where
  toFun := (· + x)
  inj' := add_left_injective x
  map_rel_iff' := add_le_add_iff_right x

@[simp] theorem addRight'_apply {α : Type*} [Add α] [IsRightCancelAdd α]
    [LE α] [AddRightMono α] [AddRightReflectLE α] (x : α) (y : α) :
    addRight' x y = y + x := rfl

end OrderEmbedding
