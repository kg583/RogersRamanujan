module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Combinatorics.Young.YoungDiagram

@[expose] public section

namespace YoungDiagram

@[simp]
lemma card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  simp [transpose, YoungDiagram.card]

@[simp]
lemma sum_rowLens_eq_card (μ : YoungDiagram) : μ.rowLens.sum = μ.card := by
  have hf : ∀ c ∈ μ.cells, c.1 ∈ Finset.range (μ.colLen 0) := by
    intro c hc
    rw [Finset.mem_range, ← YoungDiagram.mem_iff_lt_colLen]
    exact μ.up_left_mem (le_refl _) (Nat.zero_le _) hc
  have hr : ∀ i ∈ Finset.range (μ.colLen 0), ({c ∈ μ.cells | c.1 = i}).card = μ.rowLen i := by
    intro i _hi
    rw [YoungDiagram.rowLen_eq_card, row]
  rw [YoungDiagram.card, Finset.card_eq_sum_card_fiberwise hf, Finset.sum_congr rfl hr,
    YoungDiagram.rowLens, ← List.sum_toFinset, List.toFinset_range]
  exact List.nodup_range

/-- Convert a Young diagram to a partition. -/
def toPartition {n : ℕ} (μ : YoungDiagram) (h : μ.card = n) : Nat.Partition n where
  parts := μ.rowLens
  parts_pos := μ.pos_of_mem_rowLens _
  parts_sum := by simp [sum_rowLens_eq_card, h]

/-- Convert a partition to a Young diagram. -/
def ofPartition {n : ℕ} (p : Nat.Partition n) : YoungDiagram :=
  ofRowLens
    (p.parts.sort (· ≥ ·))
    (Multiset.pairwise_sort p.parts (· ≥ ·)).sortedGE

@[simp]
theorem rowLens_ofPartition_eq_sort_parts {n : ℕ} (p : Nat.Partition n) :
    (ofPartition p).rowLens = p.parts.sort (· ≥ ·) := by
  grind [ofPartition, rowLens_ofRowLens_eq_self, Multiset.mem_sort]

@[simp]
theorem card_ofPartition {n : ℕ} (p : Nat.Partition n) :
    (ofPartition p).card = n := by
  rw [← sum_rowLens_eq_card, rowLens_ofPartition_eq_sort_parts]
  calc
    (p.parts.sort (· ≥ ·)).sum
      = (↑(p.parts.sort (· ≥ ·)) : Multiset ℕ).sum := Multiset.sum_coe _
    _ = p.parts.sum := by rw [Multiset.sort_eq]
    _ = n := p.parts_sum

@[simp]
theorem ofPartition_toPartition {n : ℕ} {μ : YoungDiagram} (h : μ.card = n) :
    ofPartition (μ.toPartition h) = μ := by
  simp [ofPartition, toPartition, List.mergeSort_eq_self (· ≥ ·) μ.rowLens_sorted.pairwise,
    ofRowLens_to_rowLens_eq_self]

@[simp]
theorem toPartition_ofPartition {n : ℕ} {p : Nat.Partition n} :
    (ofPartition p).toPartition (card_ofPartition p) = p := by
  ext
  simp [toPartition]

/-- Equivalence between Young diagrams of cardinality `n` and partitions of `n`. -/
def equivPartition {n : ℕ} : { μ : YoungDiagram // μ.card = n } ≃ Nat.Partition n where
  toFun μ := toPartition μ μ.2
  invFun p := ⟨ofPartition p, card_ofPartition p⟩
  left_inv := fun ⟨_, h⟩ => Subtype.mk_eq_mk.mpr (ofPartition_toPartition h)
  right_inv := fun _ => toPartition_ofPartition

end YoungDiagram
