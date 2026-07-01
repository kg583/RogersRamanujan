module

public import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs

/-! # `Filter.atTop` and `Finset`

Decomposing `atTop` on `ℕ` as a sup of arithmetic progressions.
-/

@[expose] public section

open Filter Finset

namespace Filter

theorem atTop_eq_sup {n : ℕ} (hn : n ≠ 0) :
    (atTop : Filter ℕ) = (range n).sup fun i ↦ atTop.map (n * · + i) := by
  ext s
  suffices (∃ a, ∀ b, a ≤ b → b ∈ s) ↔ ∀ i < n, ∃ a, ∀ b, a ≤ b → n * b + i ∈ s by
    simpa [Finset.sup_eq_iSup]
  refine ⟨fun ⟨a, ha⟩ i hi ↦ ?_, fun h ↦ ?_⟩
  · exact ⟨a, fun b hb ↦ ha _ <| hb.trans <|
      (Nat.le_mul_of_pos_left _ (by omega)).trans (Nat.le_add_right _ _)⟩
  · choose a ha using h
    refine ⟨(univ : Finset (Fin n)).sup fun j ↦ n * a j.1 j.2 + j.1, fun b hb ↦ ?_⟩
    have hbn : b % n < n := b.mod_lt (by grind)
    replace hb := Finset.sup_le_iff.mp hb ⟨b % n, hbn⟩ (mem_univ _)
    refine Nat.div_add_mod b n ▸ ha _ hbn _ ?_
    rw [Nat.le_div_iff_mul_le (by omega : 0 < n), mul_comm]
    exact (Nat.le_add_right _ _).trans hb

end Filter
