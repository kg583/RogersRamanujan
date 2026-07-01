module

public import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.TopologicallyNilpotent

/-! # Basic normed ring lemmas
-/

@[expose] public section

theorem isTopologicallyNilpotent_iff_norm_lt_one
    {R : Type*} [SeminormedRing R] [NormMulClass R] (x : R) :
    IsTopologicallyNilpotent x ↔ ‖x‖ < 1 :=
  tendsto_pow_atTop_nhds_zero_iff_norm_lt_one
