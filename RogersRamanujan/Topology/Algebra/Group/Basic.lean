module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Rat.Floor
public import Mathlib.Topology.Algebra.Group.Defs

/-! # Topological groups
-/

@[expose] public section

theorem coe_addSubgroupClosure_one_eq_range_intCast {R : Type*} [Ring R] :
    AddSubgroup.closure ({1} : Set R) = (Set.range (Int.cast : ℤ → R)) := by
  convert congr(($(((Int.castAddHom R).map_closure {1}).symm) : Set R)) <;> simp

open Filter Topology Pointwise

@[to_additive]
theorem inv_mem_nhds_one' {α : Type*} [InvOneClass α] [TopologicalSpace α] [ContinuousInv α]
    {U : Set α} (hU : U ∈ 𝓝 1) : U⁻¹ ∈ 𝓝 1 :=
  continuous_inv.continuousAt.preimage_mem_nhds (by simpa)
