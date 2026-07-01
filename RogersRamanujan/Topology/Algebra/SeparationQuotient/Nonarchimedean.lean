module

import RogersRamanujan.Topology.Algebra.Nonarchimedean.OpenMap
import RogersRamanujan.Topology.Algebra.SeparationQuotient.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.Algebra.SeparationQuotient.Basic

/-! # Separation quotient of a nonarchimedean ring
-/

@[expose] public section

namespace SeparationQuotient

instance (A : Type*) [AddGroup A] [TopologicalSpace A] [NonarchimedeanAddGroup A] :
    NonarchimedeanAddGroup (SeparationQuotient A) :=
  IsOpenMap.nonarchimedeanAddGroup mkAddMonoidHom isOpenMap_mk continuous_mk

instance (A : Type*) [Ring A] [TopologicalSpace A] [NonarchimedeanRing A] :
    NonarchimedeanRing (SeparationQuotient A) :=
  IsOpenMap.nonarchimedeanRing mkRingHom isOpenMap_mk continuous_mk

end SeparationQuotient
