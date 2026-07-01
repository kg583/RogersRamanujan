module

public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-! # Infinite sums in modules
-/

@[expose] public section

theorem IsUnit.tsum_mul_left
    {ι R : Type*} [Ring R] [TopologicalSpace R] [ContinuousConstSMul R R] [T2Space R]
    {f : ι → R} {L : SummationFilter ι} {a : R} (ha : IsUnit a) :
    ∑'[L] i, a * f i = a * ∑'[L] i, f i :=
  tsum_const_smul' ha.unit
