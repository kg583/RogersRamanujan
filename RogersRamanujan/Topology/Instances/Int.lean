module

public import Mathlib.Order.Filter.Cofinite
import Mathlib.Topology.Instances.Int

/-! # Topology on `ℤ`

`Int.natAbs` tends to `atTop` along `cofinite`, `atTop`, and `atBot`.
-/

@[expose] public section

open Filter

namespace Int

theorem tendsto_natAbs_atBot_atTop :
    Tendsto Int.natAbs atBot atTop := by
  rw [tendsto_atBot_atTop]
  exact fun n ↦ ⟨-n, fun i hi ↦ by rwa [← Nat.cast_le (α := ℤ), ← neg_le_neg_iff, Nat.cast_natAbs,
    abs_eq_neg_self.mpr (by linarith), Int.cast_id, neg_neg]⟩

theorem tendsto_natAbs_atTop_atTop :
    Tendsto Int.natAbs atTop atTop := by
  rw [tendsto_atTop_atTop]
  exact fun n ↦ ⟨n, fun i hi ↦ by rwa [← Nat.cast_le (α := ℤ), Nat.cast_natAbs, Int.cast_id,
    abs_eq_self.mpr (by linarith)]⟩

theorem tendsto_natAbs_cofinite_atTop :
    Tendsto Int.natAbs cofinite atTop := by
  rw [Int.cofinite_eq, tendsto_sup]
  exact ⟨tendsto_natAbs_atBot_atTop, tendsto_natAbs_atTop_atTop⟩

theorem tendsto_add_const_cofinite_cofinite (c : ℤ) :
    Tendsto (fun m : ℤ ↦ m + c) cofinite cofinite := by
  rw [Int.cofinite_eq]
  exact .sup_sup (tendsto_atBot_add_const_right _ _ tendsto_id)
    (tendsto_atTop_add_const_right _ _ tendsto_id)

theorem cofinite_eq' :
    cofinite = atTop.map (fun n : ℕ ↦ (n : ℤ)) ⊔ atTop.map (fun n : ℕ ↦ (-n : ℤ)) := by
  rw [cofinite_eq, ← map_neg_atTop, ← Nat.map_cast_int_atTop, sup_comm, Filter.map_map]
  rfl

theorem tendsto_cofinite_iff {α : Type*} {s : Filter α} {f : ℤ → α} :
    Tendsto f cofinite s ↔ Tendsto (fun n : ℕ ↦ f n) atTop s ∧
      Tendsto (fun n : ℕ ↦ f (-n)) atTop s := by
  rw [cofinite_eq', tendsto_sup, tendsto_map'_iff, tendsto_map'_iff]
  rfl

theorem tendsto_toNat_atTop : Tendsto toNat atTop atTop := tendsto_atTop_atTop.mpr fun n ↦
  ⟨n, fun i hi ↦ by omega⟩

end Int
