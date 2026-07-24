module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Combinatorics.Young.YoungDiagram
public import Mathlib.Data.ZMod.Basic

public import RogersRamanujan.NumberTheory.Partitions.Defs

@[expose] public section

namespace Multiset

theorem fold_max_eq_of_mem_of_forall_le {α : Type*} [LinearOrder α] [OrderBot α]
    {s : Multiset α} {m : α} (hm : m ∈ s) (hmax : ∀ x ∈ s, x ≤ m) :
    s.fold max ⊥ = m := by
  obtain ⟨l⟩ := s
  simp only [Multiset.quot_mk_to_coe'', Multiset.mem_coe] at hm hmax
  exact le_antisymm (List.max_le_of_forall_le _ _ hmax) (List.le_max_of_le hm le_rfl)

theorem fold_max_le_iff {α : Type*} [LinearOrder α] [OrderBot α]
    {s : Multiset α} {m : α} : s.fold max ⊥ ≤ m ↔ ∀ x ∈ s, x ≤ m := by
  obtain ⟨l⟩ := s
  simp only [Multiset.quot_mk_to_coe'', Multiset.mem_coe]
  exact ⟨fun h x hx => (List.le_max_of_le hx le_rfl).trans h, List.max_le_of_forall_le _ _⟩

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

@[simp]
theorem conjugate_length_eq_maxPart {n : ℕ} (p : Partition n) : p.conjugate.length = p.maxPart := by
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

@[simp]
theorem conjugate_maxPart_eq_length {n : ℕ} (p : Partition n) : p.conjugate.maxPart = p.length := by
  rw [← conjugate_conjugate p, conjugate_length_eq_maxPart, conjugate_conjugate p]

theorem maxPart_le_iff {n : ℕ} {p : Partition n} {k : ℕ} :
    p.maxPart ≤ k ↔ ∀ i ∈ p.parts, i ≤ k := by
  change Multiset.fold max 0 p.parts ≤ k ↔ _
  rw [← Nat.bot_eq_zero]
  exact Multiset.fold_max_le_iff

theorem mem_sizeRestricted_iff {n k : ℕ} {p : Partition n} :
    p ∈ Partition.sizeRestricted n k ↔ ∀ i ∈ p.parts, i ≤ k := by
  simp [Partition.sizeRestricted, Partition.restricted]

def equiv_maxPart_length (n k : ℕ) :
    Partition.lengthRestricted n k ≃ Partition.sizeRestricted n k where
  toFun p := ⟨p.val.conjugate, by
    rw [mem_sizeRestricted_iff, ← maxPart_le_iff, conjugate_maxPart_eq_length]
    exact p.2⟩
  invFun q := ⟨q.val.conjugate, by
    show q.val.conjugate.length ≤ k
    rw [conjugate_length_eq_maxPart, maxPart_le_iff, ← mem_sizeRestricted_iff]
    exact q.2⟩
  left_inv p := Subtype.ext (conjugate_conjugate p.val)
  right_inv q := Subtype.ext (conjugate_conjugate q.val)

@[simp]
theorem conjugate_rank_eq_neg_rank {n : ℕ} (p : Partition n) : p.conjugate.rank = -p.rank := by
  simp [Partition.rank]

def equiv_rankFiber (m : ℤ) (n : ℕ) : rankFiber (-m) n ≃ rankFiber m n where
  toFun p := ⟨p.val.conjugate, by
    change p.val.conjugate.rank = m
    rw [conjugate_rank_eq_neg_rank, p.2, neg_neg]⟩
  invFun q := ⟨q.val.conjugate, by
    change q.val.conjugate.rank = -m
    rw [conjugate_rank_eq_neg_rank, q.2]⟩
  left_inv p := Subtype.ext (conjugate_conjugate p.val)
  right_inv q := Subtype.ext (conjugate_conjugate q.val)

end Nat.Partition
