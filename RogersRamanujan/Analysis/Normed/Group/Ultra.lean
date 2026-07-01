module

public import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Topology.MetricSpace.Ultra.Basic

/-! # Norms of differences in ultrametric groups
-/

@[expose] public section

namespace IsUltrametricDist

theorem norm_sub_of_gt {S : Type*} [SeminormedAddGroup S] [IsUltrametricDist S]
    {x y : S} (h : ‖y‖ < ‖x‖) : ‖x - y‖ = ‖x‖ := by
  rw [sub_eq_add_neg, norm_add_eq_max_of_norm_ne_norm (by simp; grind)]
  simp [h.le]

theorem norm_sub_of_lt {S : Type*} [SeminormedAddGroup S] [IsUltrametricDist S]
    {x y : S} (h : ‖x‖ < ‖y‖) : ‖x - y‖ = ‖y‖ := by
  rw [← neg_sub, norm_neg, norm_sub_of_gt h]

end IsUltrametricDist
