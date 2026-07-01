module

public import Mathlib.Topology.Algebra.SeparationQuotient.Basic

/-! # Separation quotient
-/

@[expose] public section

namespace SeparationQuotient

@[simp] theorem coe_mkRingHom
    {R : Type*} [TopologicalSpace R] [NonAssocSemiring R] [IsTopologicalSemiring R] :
    ⇑(mkRingHom (R := R)) = mk := rfl

instance (A : Type*) [Ring A] [TopologicalSpace A] [IsTopologicalRing A] :
    IsTopologicalRing (SeparationQuotient A) where

end SeparationQuotient
