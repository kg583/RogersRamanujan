module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Combinatorics.Young.YoungDiagram

public import RogersRamanujan.NumberTheory.Partitions.PR

@[expose] public section

namespace Multiset

theorem fold_max_eq_of_mem_of_forall_le {α : Type*} [LinearOrder α] [OrderBot α]
    {s : Multiset α} {m : α} (hm : m ∈ s) (hmax : ∀ x ∈ s, x ≤ m) :
    s.fold max ⊥ = m := by
  obtain ⟨l⟩ := s
  simp only [Multiset.quot_mk_to_coe'', Multiset.mem_coe] at hm hmax
  exact le_antisymm (List.max_le_of_forall_le _ _ hmax) (List.le_max_of_le hm le_rfl)

end Multiset

namespace Nat.Partition
open Finset

/-- Conjugate a partition (equivalent to transposing its Young diagram). -/
def conjugate {n : ℕ} (p : Partition n) : Partition n :=
  (YoungDiagram.ofPartition p).transpose.toPartition (by
    rw [YoungDiagram.card_transpose, YoungDiagram.card_ofPartition]
  )

/-- Conjugation is an involution. -/
@[simp]
theorem conjugate_conjugate {n : ℕ} (p : Partition n) : p.conjugate.conjugate = p := by
  ext
  simp [conjugate]

theorem conjugate_eq_iff_eq_conjugate {n : ℕ} {p q : Partition n}
    : p.conjugate = q ↔ p = q.conjugate := by
  constructor <;>
    · rintro rfl
      simp

@[simp]
theorem conjugate_eq_iff {n : ℕ} {p q : Partition n} : p.conjugate = q.conjugate ↔ p = q := by
  simp [conjugate_eq_iff_eq_conjugate]

protected abbrev length {n : ℕ} (p : Partition n) := p.parts.card

protected abbrev maxPart {n : ℕ} (p : Partition n) := Multiset.fold max 0 p.parts

@[simp]
theorem conjugate_length_eq_maxPart {n : ℕ} (p : Partition n) :
    p.conjugate.length = p.maxPart := by
  set μ := YoungDiagram.ofPartition p with hμ
  have hparts : p.parts = (μ.rowLens : Multiset ℕ) := by
    rw [YoungDiagram.rowLens_ofPartition_eq_sort_parts p, Multiset.sort_eq]
  have hlen : p.conjugate.length = μ.transpose.rowLens.length := rfl
  rw [hlen, YoungDiagram.length_rowLens, YoungDiagram.colLen_transpose]
  by_cases h0 : μ.colLen 0 = 0
  · have hrl : μ.rowLens = [] := by
      rw [← List.length_eq_zero_iff, YoungDiagram.length_rowLens, h0]
    have hnotmem : (0, 0) ∉ μ := by
      rw [YoungDiagram.mem_iff_lt_colLen, h0]
      simp
    have hrow0 : μ.rowLen 0 = 0 := by
      by_contra hcon
      exact hnotmem (YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero hcon))
    simp [Nat.Partition.maxPart, hparts, hrl, hrow0]
  · have hmem : μ.rowLen 0 ∈ p.parts := by
      rw [hparts, Multiset.mem_coe, YoungDiagram.rowLens, List.mem_map]
      exact ⟨0, List.mem_range.mpr (Nat.pos_of_ne_zero h0), rfl⟩
    have hub : ∀ x ∈ p.parts, x ≤ μ.rowLen 0 := by
      intro x hx
      rw [hparts, Multiset.mem_coe, YoungDiagram.rowLens, List.mem_map] at hx
      obtain ⟨i, _, rfl⟩ := hx
      exact μ.rowLen_anti 0 i (Nat.zero_le i)
    change μ.rowLen 0 = Multiset.fold max 0 p.parts
    rw [← Nat.bot_eq_zero]
    exact (Multiset.fold_max_eq_of_mem_of_forall_le hmem hub).symm

protected abbrev rank {n : ℕ} (p : Partition n) := p.maxPart - p.length

end Nat.Partition
