module

public import Mathlib.Algebra.Ring.Basic -- shake: keep

/-! # Basic results on rings
-/

@[expose] public section

namespace IsRegular

theorem neg {R : Type*} [Mul R] [HasDistribNeg R] {x : R} (hx : IsRegular x) :
    IsRegular (-x) where
  left a b hab := hx.left <| by simpa using hab
  right a b hab := hx.right <| by simpa using hab

end IsRegular
