module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Tactic

@[expose] public section

open Finset
open scoped BigOperators

def subsetSum {k : ℕ} (S : Finset (Icc 1 k)) : ℕ := ∑ i ∈ S, i

namespace Nat.Partition

private lemma sum_Icc_one_eq_tri (k : ℕ) : ∑ i ∈ Finset.Icc 1 k, i = k * (k + 1) / 2 := by
  have hset : Finset.range (k + 1) = insert 0 (Finset.Icc 1 k) := by
    ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  have hsum := Finset.sum_range_id (k + 1)
  simp only [Nat.add_sub_cancel] at hsum
  rwa [hset, Finset.sum_insert (by simp), zero_add, mul_comm] at hsum

private lemma subset_sum_le_tri {k : ℕ} (S : Finset (Icc 1 k)) :
    subsetSum S ≤ k * (k + 1) / 2 := by
  unfold subsetSum
  calc
    (∑ i ∈ S, (i : ℕ)) ≤ ∑ i ∈ (Finset.univ : Finset (Icc 1 k)), (i : ℕ) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ S)
    _ = ∑ i ∈ Finset.Icc 1 k, i := Finset.sum_coe_sort (Finset.Icc 1 k) id
    _ = k * (k + 1) / 2 := sum_Icc_one_eq_tri k

private lemma tri_lt_square {k : ℕ} (hk : 1 < k) :
    k * (k + 1) / 2 < k * k := by
  rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 2)]
  nlinarith

private lemma tri_sqrt_lt_self {n : ℕ} (hn : 2 ≤ n) :
    Nat.sqrt n * (Nat.sqrt n + 1) / 2 < n := by
  by_cases hk : Nat.sqrt n = 1
  · rw [hk]; norm_num; exact hn
  · have hkgt : 1 < Nat.sqrt n :=
      lt_of_le_of_ne (Nat.sqrt_pos.2 (by omega)) (Ne.symm hk)
    exact lt_of_lt_of_le (tri_lt_square hkgt) (Nat.sqrt_le n)

private lemma subsetSum_le {n : ℕ} (hn : 2 ≤ n) (S : Finset (Icc 1 (Nat.sqrt n))) :
    subsetSum S ≤ n :=
  le_of_lt (lt_of_le_of_lt (subset_sum_le_tri S) (tri_sqrt_lt_self hn))

noncomputable def subsetToPartition (n : ℕ) (hn : 2 ≤ n) (S : Finset (Icc 1 (Nat.sqrt n))) :
    Nat.Partition n :=
  { parts := ({n - subsetSum S} : Multiset ℕ) + S.val.map (fun i : Icc 1 (Nat.sqrt n) => (i : ℕ))
    parts_pos := by
      intro i hi
      rw [Multiset.mem_add] at hi
      rcases hi with hi | hi
      · simp only [Multiset.mem_singleton] at hi
        subst i
        have hlt : subsetSum S < n :=
          lt_of_le_of_lt (subset_sum_le_tri S) (tri_sqrt_lt_self hn)
        exact Nat.sub_pos_of_lt hlt
      · rcases Multiset.mem_map.1 hi with ⟨j, hjS, rfl⟩
        exact (Finset.mem_Icc.mp j.2).1
    parts_sum := by
      rw [Multiset.sum_add, Multiset.sum_singleton]
      have hsum : (S.val.map fun i : Icc 1 (Nat.sqrt n) ↦ (i : ℕ)).sum = subsetSum S := by
        unfold subsetSum
        rfl
      rw [hsum]
      rw [Nat.sub_add_cancel (subsetSum_le hn S)] }

private lemma leftover_eq_small_mem {n : ℕ} (hn : 2 ≤ n) (S : Finset (Icc 1 (Nat.sqrt n)))
    (j : Icc 1 (Nat.sqrt n)) (hleft : n - subsetSum S = (j : ℕ)) : j ∈ S := by
  by_contra hj
  refine not_lt_of_ge ?_ (tri_sqrt_lt_self hn)
  calc
    n = subsetSum S + (n - subsetSum S) := (Nat.add_sub_of_le (subsetSum_le hn S)).symm
    _ = subsetSum S + (j : ℕ) := by rw [hleft]
    _ = subsetSum (insert j S) := by unfold subsetSum; rw [Finset.sum_insert hj, add_comm]
    _ ≤ Nat.sqrt n * (Nat.sqrt n + 1) / 2 := subset_sum_le_tri (insert j S)

private lemma small_mem_subsetToPartition_iff {n : ℕ} (hn : 2 ≤ n)
    (S : Finset (Icc 1 (Nat.sqrt n))) (j : Icc 1 (Nat.sqrt n)) :
    (j : ℕ) ∈ (subsetToPartition n hn S).parts ↔ j ∈ S := by
  constructor
  · intro h
    change (j : ℕ) ∈ ({n - subsetSum S} : Multiset ℕ) +
        (S.val.map fun i : Icc 1 (Nat.sqrt n) ↦ (i : ℕ)) at h
    rw [Multiset.mem_add] at h
    rcases h with h | h
    · simp only [Multiset.mem_singleton] at h
      exact leftover_eq_small_mem hn S j h.symm
    · rcases Multiset.mem_map.1 h with ⟨i, hi, hij⟩
      have hij' : i = j := Subtype.ext hij
      simpa [hij'] using hi
  · intro hj
    change (j : ℕ) ∈ ({n - subsetSum S} : Multiset ℕ) +
        (S.val.map fun i : Icc 1 (Nat.sqrt n) ↦ (i : ℕ))
    rw [Multiset.mem_add]
    right
    exact Multiset.mem_map.2 ⟨j, hj, rfl⟩

private lemma subsetToPartition_injective (n : ℕ) (hn : 2 ≤ n) :
    Function.Injective (subsetToPartition n hn) := by
  intro S T hST
  ext j
  calc
    j ∈ S ↔ (j : ℕ) ∈ (subsetToPartition n hn S).parts :=
      (small_mem_subsetToPartition_iff hn S j).symm
    _ ↔ (j : ℕ) ∈ (subsetToPartition n hn T).parts := by rw [congrArg Nat.Partition.parts hST]
    _ ↔ j ∈ T := small_mem_subsetToPartition_iff hn T j

/-- The number of partitions of `n` is at least `2 ^ Nat.sqrt n` for `n ≥ 2`. -/
theorem partition_lower_bound_two_pow_sqrt (n : ℕ) (hn : 2 ≤ n) :
    2 ^ Nat.sqrt n ≤ Fintype.card (Nat.Partition n) := by
  have hcard : Fintype.card (Finset (Icc 1 (Nat.sqrt n))) ≤ Fintype.card (Nat.Partition n) :=
    Fintype.card_le_of_injective (subsetToPartition n hn) (subsetToPartition_injective n hn)
  simpa [Fintype.card_coe, Nat.card_Icc] using hcard

end Nat.Partition
