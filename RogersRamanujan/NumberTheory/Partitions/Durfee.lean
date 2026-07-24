module

public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
public import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.RingTheory.PowerSeries.PiTopology

import RogersRamanujan.Algebra.BigOperators.Group.Finset.Basic
import RogersRamanujan.Algebra.Group.Units.Basic
import RogersRamanujan.Algebra.Group.Units.Hom
public import RogersRamanujan.NumberTheory.Partitions.Conjugate
public import RogersRamanujan.NumberTheory.Partitions.Defs
public import RogersRamanujan.NumberTheory.QTheory.Basic
public import RogersRamanujan.NumberTheory.QTheory.BinomialTheorem
import RogersRamanujan.NumberTheory.QTheory.Nonarchimedean
public import RogersRamanujan.NumberTheory.QTheory.Pentagonal
import RogersRamanujan.NumberTheory.QTheory.StrongNonarchimedean
public import RogersRamanujan.RingTheory.PowerSeries.DiscreteTopology
public import RogersRamanujan.RingTheory.PowerSeries.Evaluation
public import RogersRamanujan.Topology.Algebra.TopologicallyNilpotent


@[expose] public section

def squares {n : ℕ} (p : Nat.Partition n) : Finset ℕ :=
    {s ∈ Finset.Icc 0 n | s ≤ (YoungDiagram.ofPartition p).rowLens.length ∧
      ∀ x ∈ (YoungDiagram.ofPartition p).rowLens.take s, x ≥ s}

lemma zero_square {n : ℕ} (p : Nat.Partition n) : 0 ∈ squares p := by
  rw [squares]
  simp

namespace List

private lemma take_forall_ge_of_card_filter_ge :
    ∀ (L : List ℕ), L.Pairwise (· ≥ ·) → ∀ (k v : ℕ), k ≤ (L.filter (v ≤ ·)).length →
      ∀ x ∈ L.take k, v ≤ x := by
  intro L
  induction L with
  | nil => simp
  | cons a t ih =>
    intro hpw k v hk x hx
    rw [List.pairwise_cons] at hpw
    obtain ⟨hage, hpwt⟩ := hpw
    cases k with
    | zero => simp at hx
    | succ k' =>
      rw [List.take_succ_cons, List.mem_cons] at hx
      by_cases hva : v ≤ a
      · rw [List.filter_cons_of_pos (by simpa using hva), List.length_cons] at hk
        rcases hx with rfl | hx
        · exact hva
        · exact ih hpwt k' v (by omega) x hx
      · exfalso
        have hzero : (t.filter (v ≤ ·)).length = 0 := by
          rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
          intro b hb
          have := hage b hb
          simp only [decide_eq_true_eq]
          omega
        rw [List.filter_cons_of_neg (by simpa using hva), hzero] at hk
        omega

private lemma take_le_coe (L : List ℕ) (k : ℕ) :
    (L.take k : Multiset ℕ) ≤ (L : Multiset ℕ) :=
  Multiset.coe_le.mpr (List.take_sublist k L).subperm

private lemma take_le_take' (L : List ℕ) {a b : ℕ} (h : a ≤ b) :
    (L.take a : Multiset ℕ) ≤ (L.take b : Multiset ℕ) := by
  have h1 := List.take_sublist a (L.take b)
  rw [List.take_take, min_eq_left h] at h1
  exact Multiset.coe_le.mpr h1.subperm

private lemma all_eq_of_ge_of_le (s : Multiset ℕ) (d : ℕ) (h1 : ∀ x ∈ s, d ≤ x)
    (h2 : ∀ x ∈ s, x ≤ d) : s = Multiset.replicate (Multiset.card s) d := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    have ha : a = d := le_antisymm (h2 a (Multiset.mem_cons_self a s))
      (h1 a (Multiset.mem_cons_self a s))
    have hih := ih (fun x hx => h1 x (Multiset.mem_cons_of_mem hx))
      (fun x hx => h2 x (Multiset.mem_cons_of_mem hx))
    rw [Multiset.card_cons, Multiset.replicate_succ, ha, hih, Multiset.card_replicate]

private lemma take_card_filter_eq (L : List ℕ) (hpw : L.Pairwise (· ≥ ·)) (v k : ℕ)
    (hklen : k ≤ L.length) (hkeq : (L.filter (v < · : ℕ → Bool)).length = k) :
    (L.take k : Multiset ℕ) = Multiset.filter (v < ·) (L : Multiset ℕ) := by
  apply Multiset.eq_of_le_of_card_le
  · rw [Multiset.le_filter]
    refine ⟨take_le_coe L k, fun a ha => ?_⟩
    rw [Multiset.mem_coe] at ha
    have hge : k ≤ (L.filter (v + 1 ≤ · : ℕ → Bool)).length := by
      have heq : (v + 1 ≤ · : ℕ → Bool) = (v < · : ℕ → Bool) := by funext x; simp
      rw [heq, hkeq]
    have := take_forall_ge_of_card_filter_ge L hpw k (v + 1) hge a ha
    omega
  · have h1 : Multiset.card (Multiset.filter (v < ·) (L : Multiset ℕ)) = k := hkeq
    have h2 : Multiset.card (L.take k : Multiset ℕ) = k := by
      change (L.take k).length = k
      rw [List.length_take]; omega
    omega

private lemma take_split (L : List ℕ) (hpw : L.Pairwise (· ≥ ·)) (d k : ℕ) (hk : k ≤ d)
    (hdlen : d ≤ L.length) (hAlen : (L.filter (d < · : ℕ → Bool)).length = k)
    (hdge : d ≤ (L.filter (d ≤ · : ℕ → Bool)).length) :
    (L.take d : Multiset ℕ) = (L.take k : Multiset ℕ) + Multiset.replicate (d - k) d := by
  have hklen : k ≤ L.length := by omega
  have hAforall : ∀ x ∈ L.take k, d < x := by
    have hAge : k ≤ (L.filter (d + 1 ≤ · : ℕ → Bool)).length := by
      have heq : (d + 1 ≤ · : ℕ → Bool) = (d < · : ℕ → Bool) := by funext x; simp
      rw [heq, hAlen]
    intro x hx
    have := take_forall_ge_of_card_filter_ge L hpw k (d + 1) hAge x hx
    omega
  have hAeq : (L.take k : Multiset ℕ) = Multiset.filter (d < ·) (L.take d : Multiset ℕ) := by
    apply Multiset.eq_of_le_of_card_le
    · rw [Multiset.le_filter]
      exact ⟨take_le_take' L hk, fun a ha => by rw [Multiset.mem_coe] at ha; exact hAforall a ha⟩
    · have h1 : Multiset.filter (d < ·) (L.take d : Multiset ℕ)
          ≤ Multiset.filter (d < ·) (L : Multiset ℕ) :=
        Multiset.filter_le_filter (d < ·) (take_le_coe L d)
      have h2 : Multiset.card (Multiset.filter (d < ·) (L : Multiset ℕ)) = k := by
        change (L.filter (d < · : ℕ → Bool)).length = k
        exact hAlen
      have h3 := Multiset.card_le_card h1
      rw [h2] at h3
      have h4 : Multiset.card (L.take k : Multiset ℕ) = k := by
        change (L.take k).length = k
        rw [List.length_take]; omega
      omega
  have hrest : Multiset.filter (¬ d < ·) (L.take d : Multiset ℕ)
      = Multiset.replicate (d - k) d := by
    have hforallge : ∀ x ∈ Multiset.filter (¬ d < ·) (L.take d : Multiset ℕ), d ≤ x := by
      intro x hx
      exact take_forall_ge_of_card_filter_ge L hpw d d hdge x
        (Multiset.mem_coe.mp (Multiset.mem_of_mem_filter hx))
    have hforallle : ∀ x ∈ Multiset.filter (¬ d < ·) (L.take d : Multiset ℕ), x ≤ d := by
      intro x hx
      have := (Multiset.mem_filter.mp hx).2
      omega
    have hcard : Multiset.card (Multiset.filter (¬ d < ·) (L.take d : Multiset ℕ)) = d - k := by
      have hsplit : Multiset.card (Multiset.filter (d < ·) (L.take d : Multiset ℕ))
          + Multiset.card (Multiset.filter (¬ d < ·) (L.take d : Multiset ℕ))
          = Multiset.card (L.take d : Multiset ℕ) := by
        rw [← Multiset.card_add, Multiset.filter_add_not]
      have htdcard : Multiset.card (L.take d : Multiset ℕ) = d := by
        change (L.take d).length = d
        rw [List.length_take]; omega
      rw [← hAeq, htdcard] at hsplit
      have hkcard : Multiset.card (L.take k : Multiset ℕ) = k := by
        change (L.take k).length = k
        rw [List.length_take]; omega
      omega
    rw [all_eq_of_ge_of_le _ d hforallge hforallle, hcard]
  conv_lhs => rw [← Multiset.filter_add_not (d < ·) (L.take d : Multiset ℕ)]
  rw [← hAeq, hrest]

private lemma drop_forall_le_of_card_filter_le :
    ∀ (L : List ℕ), L.Pairwise (· ≥ ·) → ∀ (k v : ℕ), (L.filter (v < ·)).length ≤ k →
      ∀ x ∈ L.drop k, x ≤ v := by
  intro L
  induction L with
  | nil => simp
  | cons a t ih =>
    intro hpw k v hk x hx
    rw [List.pairwise_cons] at hpw
    obtain ⟨hage, hpwt⟩ := hpw
    cases k with
    | zero =>
      simp only [List.drop_zero] at hx
      have hz : ((a :: t).filter (v < ·)).length = 0 := Nat.le_zero.mp hk
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at hz
      have := hz x hx
      simp only [decide_eq_true_eq] at this
      omega
    | succ k' =>
      rw [List.drop_succ_cons] at hx
      by_cases hva : v < a
      · rw [List.filter_cons_of_pos (by simpa using hva), List.length_cons] at hk
        exact ih hpwt k' v (by omega) x hx
      · have hxt : x ∈ t := List.mem_of_mem_drop hx
        have := hage x hxt
        omega

private lemma filter_gt_length_le (L : List ℕ) (d : ℕ)
    (h : ∀ i, (hi : i < L.length) → d ≤ i → L[i] ≤ d) :
    (L.filter (· > d)).length ≤ d := by
  have hdrop : (L.drop d).filter (· > d) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx
    rw [List.mem_drop_iff_getElem] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    simp only [decide_eq_true_eq, not_lt]
    exact h (d + j) (by omega) (by omega)
  have heq : L.filter (· > d) = (L.take d).filter (· > d) := by
    conv_lhs => rw [← List.take_append_drop d L]
    rw [List.filter_append, hdrop, List.append_nil]
  rw [heq]
  calc ((L.take d).filter (· > d)).length ≤ (L.take d).length := List.length_filter_le _ _
    _ ≤ d := by simp

end List

namespace YoungDiagram

@[simp]
theorem rowLens_take_eq {μ : YoungDiagram} {s : ℕ} (hs : s ≤ μ.rowLens.length) :
    μ.rowLens.take s = (List.range s).map μ.rowLen := by
  have hs' : s ≤ μ.colLen 0 := by rwa [YoungDiagram.length_rowLens] at hs
  rw [YoungDiagram.rowLens]
  apply List.ext_getElem
  · simp [Nat.min_eq_left hs']
  · intro i h1 h2
    simp only [List.getElem_take, List.getElem_map, List.getElem_range]

lemma forall_lt_rowLen_ge_iff {μ : YoungDiagram} {s : ℕ} :
    (∀ i < s, s ≤ μ.rowLen i) ↔ s = 0 ∨ s ≤ μ.rowLen (s - 1) := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp
  · simp only [hs.ne', false_or]
    constructor
    · intro h; exact h (s - 1) (by omega)
    · intro h i hi
      exact h.trans (μ.rowLen_anti i (s - 1) (by omega))

private lemma rowLen_ge_iff_colLen_ge {μ : YoungDiagram} {s : ℕ} (hs : 1 ≤ s) :
    s ≤ μ.rowLen (s - 1) ↔ s ≤ μ.colLen (s - 1) := by
  have h1 : s ≤ μ.rowLen (s - 1) ↔ (s - 1, s - 1) ∈ μ := by
    rw [YoungDiagram.mem_iff_lt_rowLen]; omega
  have h2 : s ≤ μ.colLen (s - 1) ↔ (s - 1, s - 1) ∈ μ := by
    rw [YoungDiagram.mem_iff_lt_colLen]; omega
  rw [h1, h2]

private lemma rowLens_parts_eq {n : ℕ} (p : Nat.Partition n) :
    p.parts = ((YoungDiagram.ofPartition p).rowLens : Multiset ℕ) := by
  rw [YoungDiagram.rowLens_ofPartition_eq_sort_parts, Multiset.sort_eq]

end YoungDiagram

private lemma sum_map_add_const (s : Multiset ℕ) (d : ℕ) :
    (s.map (· + d)).sum = s.sum + d * Multiset.card s := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, Nat.mul_succ]
    omega

private lemma max'_eq_of_downward_closed {S : Finset ℕ}
    (hS : ∀ a b, a ≤ b → b ∈ S → a ∈ S) {d : ℕ} (hd : d ∈ S) (hd1 : d + 1 ∉ S) :
    S.max' ⟨d, hd⟩ = d := by
  refine le_antisymm (Finset.max'_le S ⟨d, hd⟩ d fun y hy => ?_) (Finset.le_max' S d hd)
  by_contra hc
  push Not at hc
  exact hd1 (hS (d + 1) y hc hy)

private lemma sum_sub_add_mul_length_eq (l : List ℕ) (d : ℕ) (h : ∀ x ∈ l, d ≤ x) :
    (l.map (· - d)).sum + d * l.length = l.sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ]
    have hd : d ≤ a := h a List.mem_cons_self
    have hih := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    omega

private lemma sum_sub_eq_zero_of_forall_le (l : List ℕ) (d : ℕ) (h : ∀ x ∈ l, x ≤ d) :
    (l.map (· - d)).sum = 0 := by
  rw [List.sum_eq_zero_iff]
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have := h y hy
  omega

private lemma mem_squares_iff {n : ℕ} (p : Nat.Partition n) (s : ℕ) :
    s ∈ squares p ↔ s ≤ n ∧ s ≤ (YoungDiagram.ofPartition p).rowLens.length ∧
      (s = 0 ∨ s ≤ (YoungDiagram.ofPartition p).rowLen (s - 1)) := by
  simp only [squares, Finset.mem_filter, Finset.mem_Icc, Nat.zero_le, true_and]
  refine and_congr_right fun _ => and_congr_right fun hlen => ?_
  rw [YoungDiagram.rowLens_take_eq hlen, ← YoungDiagram.forall_lt_rowLen_ge_iff]
  simp [List.mem_map, List.mem_range]

private lemma squares_downward_closed {n : ℕ} (p : Nat.Partition n) :
    ∀ a b, a ≤ b → b ∈ squares p → a ∈ squares p := by
  intro a b hab hb
  rw [mem_squares_iff] at hb ⊢
  obtain ⟨hbn, hblen, hbval⟩ := hb
  refine ⟨by omega, by omega, ?_⟩
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · left; rfl
  · right
    rcases hbval with hb0 | hbval
    · omega
    · exact hab.trans (hbval.trans ((YoungDiagram.ofPartition p).rowLen_anti (a - 1) (b - 1)
        (by omega)))

namespace Nat.Partition

/-- Transport a partition of `n` along a proof `n = m` to a partition of `m`, keeping the same
underlying multiset of parts. -/
def reindex {n : ℕ} (p : Partition n) (m : ℕ) (h : n = m) : Partition m where
  parts := p.parts
  parts_pos := p.parts_pos
  parts_sum := h ▸ p.parts_sum

@[simp]
theorem reindex_parts {n : ℕ} (p : Partition n) (m : ℕ) (h : n = m) :
    (reindex p m h).parts = p.parts := rfl

@[simp]
theorem map_parts_sum_eq {n : ℕ} (p : Partition n) (f : ℕ → ℕ) :
    (Multiset.map f p.parts).sum = ((p.parts.sort (· ≥ ·)).map f).sum := by
  conv_lhs => rw [← Multiset.sort_eq p.parts (· ≥ ·), Multiset.map_coe]
  rfl

@[simp]
theorem conjugate_squares_eq_squares {n : ℕ} (p : Partition n) :
    (squares p.conjugate) = (squares p) := by
  set μ := YoungDiagram.ofPartition p
  have hμc : YoungDiagram.ofPartition p.conjugate = μ.transpose := by
    rw [conjugate, YoungDiagram.ofPartition_toPartition]
  ext s
  rw [mem_squares_iff, mem_squares_iff, hμc]
  simp only [YoungDiagram.length_rowLens, YoungDiagram.colLen_transpose,
    YoungDiagram.rowLen_transpose]
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp
  · simp only [hs.ne', false_or]
    constructor
    · rintro ⟨hsn, -, hcol⟩
      exact ⟨hsn, hcol.trans (μ.colLen_anti 0 (s - 1) (Nat.zero_le _)),
        (YoungDiagram.rowLen_ge_iff_colLen_ge hs).mpr hcol⟩
    · rintro ⟨hsn, -, hrow⟩
      exact ⟨hsn, hrow.trans (μ.rowLen_anti 0 (s - 1) (Nat.zero_le _)),
        (YoungDiagram.rowLen_ge_iff_colLen_ge hs).mp hrow⟩

instance {n k : ℕ} : Fintype (lengthRestricted n k) :=
  inferInstanceAs (Fintype {p : Partition n // p.length ≤ k})

open PowerSeries PowerSeries.WithPiTopology PowerSeries.DiscreteTopology
open scoped QTheory

/-- The generating function of `sizeRestricted _ d` (partitions with parts at most `d`). -/
noncomputable def powerSeriesSizeRestricted (d : ℕ) : ℤ⟦X⟧ :=
  PowerSeries.mk fun m ↦ Fintype.card (sizeRestricted m d)

theorem hasProd_powerSeriesSizeRestricted (d : ℕ) :
    HasProd (fun i ↦ if i + 1 ≤ d then ∑' j : ℕ, (X : ℤ⟦X⟧) ^ ((i + 1) * j) else 1)
      (powerSeriesSizeRestricted d) := by
  have := hasProd_powerSeriesMk_card_restricted ℤ (· ≤ d)
  simpa [sizeRestricted, powerSeriesSizeRestricted] using this

/-- The generating function of the partitions of size at most `d` is `bInv (X; X)_d`. -/
theorem powerSeriesSizeRestricted_eq_bInv_qPochhammer (d : ℕ) :
    powerSeriesSizeRestricted d = bInv (X; X)_d := by
  have hfin : HasProd (fun i ↦ if i + 1 ≤ d then ∑' j : ℕ, (X : ℤ⟦X⟧) ^ ((i + 1) * j) else 1)
      (∏ i ∈ Finset.range d, if i + 1 ≤ d then ∑' j : ℕ, (X : ℤ⟦X⟧) ^ ((i + 1) * j) else 1) :=
    hasProd_prod_of_ne_finset_one fun i hi => by
      rw [Finset.mem_range] at hi; simp [show ¬ i + 1 ≤ d by omega]
  rw [(hasProd_powerSeriesSizeRestricted d).unique hfin]
  have hq : IsTopologicallyNilpotent (X : ℤ⟦X⟧) := by simp
  have hprod_eq : ∏ i ∈ Finset.range d,
      (if i + 1 ≤ d then ∑' j : ℕ, (X : ℤ⟦X⟧) ^ ((i + 1) * j) else 1)
      = ∏ i ∈ Finset.range d, ∑' j : ℕ, (X : ℤ⟦X⟧) ^ ((i + 1) * j) :=
    Finset.prod_congr rfl fun i hi => by
      rw [Finset.mem_range] at hi; simp [show i + 1 ≤ d by omega]
  rw [hprod_eq]
  have hterm : ∀ i, ∑' j : ℕ, (X : ℤ⟦X⟧) ^ ((i + 1) * j) = bInv (1 - (X : ℤ⟦X⟧) ^ (i + 1)) := by
    intro i
    have hzero : ((X : ℤ⟦X⟧) ^ (i + 1)).constantCoeff = 0 := by simp
    have hmul := tsum_pow_mul_one_sub_of_constantCoeff_eq_zero hzero
    simp_rw [← pow_mul] at hmul
    exact (hq.pow (Nat.succ_ne_zero i)).isUnit_one_sub.eq_bInv_of_mul_eq_one hmul
  simp_rw [hterm]
  rw [← bInv_prod fun i _ => (hq.pow (Nat.succ_ne_zero i)).isUnit_one_sub]
  congr 1
  rw [qPochhammer]
  exact Finset.prod_congr rfl fun i _ => by rw [pow_succ, mul_comm]

/-- The generating function of `lengthRestricted _ d` is also `bInv (X; X)_d`,
via the length/size conjugation equivalence. -/
theorem powerSeriesLengthRestricted_eq_bInv_qPochhammer (d : ℕ) :
    PowerSeries.mk (fun m ↦ (Fintype.card (lengthRestricted m d) : ℤ)) = bInv (X; X)_d := by
  rw [← powerSeriesSizeRestricted_eq_bInv_qPochhammer, powerSeriesSizeRestricted]
  congr 1
  funext m
  exact congrArg _ (Fintype.card_congr (equiv_maxPart_length m d))

namespace Durfee

def rank {n : ℕ} (p : Partition n) : ℕ :=
    (squares p).max' (Set.nonempty_of_mem (zero_square p))

def right {n : ℕ} (p : Partition n) :=
  Partition.ofMultiset (Multiset.filter (· > 0) (Multiset.map (· - rank p) p.parts))

def bottom {n : ℕ} (p : Partition n) :=
  Partition.ofMultiset ((p.parts.sort (· ≥ ·)).drop (rank p) : Multiset ℕ)

def symbol {n : ℕ} (p : Partition n) := ((right p), (bottom p))

theorem conjugate_rank_eq_rank {n : ℕ} (p : Partition n) :
    rank p.conjugate = rank p := by
  rw [rank, rank]
  conv_lhs =>
    congr
    rw [conjugate_squares_eq_squares]

private lemma not_mem_squares_succ_rank {n : ℕ} (p : Partition n) :
    rank p + 1 ∉ squares p := fun hmem => by
  have hle : rank p + 1 ≤ rank p := Finset.le_max' (squares p) _ hmem
  omega

private lemma rowLens_get_le_rank_of_ge {n : ℕ} (p : Partition n) {i : ℕ}
    (hi : i < (YoungDiagram.ofPartition p).rowLens.length) (hdi : rank p ≤ i) :
    (YoungDiagram.ofPartition p).rowLens[i] ≤ rank p := by
  by_cases hdn :rank p + 1 ≤ n
  · have hnm := (mem_squares_iff p (rank p + 1)).not.mp (not_mem_squares_succ_rank p)
    simp only [hdn, true_and, not_and_or, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      false_or] at hnm
    rcases hnm with h1 | h2
    · omega
    · simp only [Nat.add_sub_cancel] at h2
      rw [YoungDiagram.get_rowLens]
      exact ((YoungDiagram.ofPartition p).rowLen_anti (rank p) i hdi).trans (by omega)
  · have hmem : (YoungDiagram.ofPartition p).rowLens[i] ∈ p.parts :=
      (YoungDiagram.rowLens_parts_eq p) ▸ List.getElem_mem hi
    have hxn : (YoungDiagram.ofPartition p).rowLens[i] ≤ n := by
      calc (YoungDiagram.ofPartition p).rowLens[i] ≤ p.parts.sum := by
            conv_rhs => rw [← Multiset.cons_erase hmem, Multiset.sum_cons]
            omega
        _ = n := p.parts_sum
    omega

theorem rank_le_rowLens_length {n : ℕ} (p : Partition n) :
    rank p ≤ (YoungDiagram.ofPartition p).rowLens.length :=
  ((mem_squares_iff p (rank p)).mp (Finset.max'_mem (squares p) _)).2.1

private lemma rowLen_ge_rank_of_lt {n : ℕ} (p : Partition n) {i : ℕ}
    (hi : i < rank p) : rank p ≤ (YoungDiagram.ofPartition p).rowLen i := by
  obtain ⟨-, -, hd⟩ := (mem_squares_iff p (rank p)).mp (Finset.max'_mem (squares p) _)
  rcases hd with hd0 | hd
  · omega
  · exact hd.trans ((YoungDiagram.ofPartition p).rowLen_anti i (rank p - 1) (by omega))

private lemma card_parts_gt_rank_le {n : ℕ} (p : Partition n) :
    (p.parts.filter (· > rank p)).card ≤ rank p := by
  set μ := YoungDiagram.ofPartition p with hμ
  rw [YoungDiagram.rowLens_parts_eq p, ← hμ,
      show (Multiset.filter (· > rank p) (μ.rowLens : Multiset ℕ)).card
      = (μ.rowLens.filter (· > rank p : ℕ → Bool)).length from rfl]
  exact List.filter_gt_length_le _ (rank p)
    fun i hi hdi => rowLens_get_le_rank_of_ge p (hμ ▸ hi) hdi

@[simp]
theorem right_length_le {n : ℕ} (p : Partition n) : (right p).length ≤ rank p := by
  have heq : Multiset.filter (· > 0) (Multiset.map (· - rank p) p.parts)
      = Multiset.map (· - rank p) (p.parts.filter (· > rank p)) := by
    rw [Multiset.filter_map]
    congr 1
    exact Multiset.filter_congr fun x _ => by simp only [Function.comp_apply]; omega
  have hpos : ∀ x ∈ Multiset.filter (· > 0) (Multiset.map (· - rank p) p.parts), x ≠ 0 :=
    fun x hx => (Multiset.mem_filter.mp hx).2.ne'
  change ((Multiset.filter (· > 0) (Multiset.map (· - rank p) p.parts)).filter (· ≠ 0)).card
      ≤ rank p
  rw [Multiset.filter_eq_self.mpr hpos, heq, Multiset.card_map]
  exact card_parts_gt_rank_le p

@[simp]
theorem bottom_maxPart_le {n : ℕ} (p : Partition n) :
    (bottom p).maxPart ≤ rank p := by
  rw [maxPart_le_iff]
  intro i hi
  have hi' : i ∈ ((p.parts.sort (· ≥ ·)).drop (rank p) : Multiset ℕ) :=
    Multiset.mem_of_le (Multiset.filter_le _ _) hi
  rw [← YoungDiagram.rowLens_ofPartition_eq_sort_parts p, Multiset.mem_coe,
    List.mem_drop_iff_getElem] at hi'
  obtain ⟨j, hj, rfl⟩ := hi'
  exact rowLens_get_le_rank_of_ge p (by omega) (by omega)

@[simp]
theorem right_parts_eq {n : ℕ} (p : Partition n) :
    (right p).parts = Multiset.filter (· > 0) (Multiset.map (· - rank p) p.parts) :=
  Multiset.filter_eq_self.mpr fun _ hx => (Multiset.mem_filter.mp hx).2.ne'

@[simp]
theorem bottom_parts_eq {n : ℕ} (p : Partition n) :
    (bottom p).parts = ((p.parts.sort (· ≥ ·)).drop (rank p) : Multiset ℕ) := by
  change (((p.parts.sort (· ≥ ·)).drop (rank p) : Multiset ℕ)).filter (· ≠ 0)
      = ((p.parts.sort (· ≥ ·)).drop (rank p) : Multiset ℕ)
  refine Multiset.filter_eq_self.mpr fun x hx => ?_
  rw [Multiset.mem_coe] at hx
  have hxmem : x ∈ p.parts.sort (· ≥ ·) := List.mem_of_mem_drop hx
  have hxp : x ∈ p.parts := by
    rw [← Multiset.sort_eq p.parts (· ≥ ·), Multiset.mem_coe]; exact hxmem
  exact (p.parts_pos hxp).ne'

theorem rank_sq_add_size_eq {n : ℕ} (p : Partition n) :
    (rank p) ^ 2 + (right p).parts.sum + (bottom p).parts.sum = n := by
  have hsorteq : p.parts.sort (· ≥ ·) = (YoungDiagram.ofPartition p).rowLens :=
    (YoungDiagram.rowLens_ofPartition_eq_sort_parts p).symm
  have hLlen : rank p ≤ (YoungDiagram.ofPartition p).rowLens.length :=
    rank_le_rowLens_length p
  have hLsum : (YoungDiagram.ofPartition p).rowLens.sum = n := by
    have h := map_parts_sum_eq p id
    simp only [Multiset.map_id, List.map_id] at h
    rw [← hsorteq, ← h, p.parts_sum]
  have hrsum : (right p).parts.sum = (Multiset.map (· - rank p) p.parts).sum := by
    rw [right_parts_eq p]
    conv_rhs => rw [← Multiset.filter_add_not (· > 0) (Multiset.map (· - rank p) p.parts)]
    rw [Multiset.sum_add]
    have hz : (Multiset.filter (fun a => ¬ a > 0)
        (Multiset.map (· - rank p) p.parts)).sum = 0 := by
      rw [Multiset.sum_eq_zero_iff]
      exact fun x hx => by have := (Multiset.mem_filter.mp hx).2; omega
    omega
  have hbsum : (bottom p).parts.sum
      = ((YoungDiagram.ofPartition p).rowLens.drop (rank p)).sum := by
    rw [bottom_parts_eq p, hsorteq]; rfl
  have hdropzero : (((YoungDiagram.ofPartition p).rowLens.drop (rank p)).map
      (· - rank p)).sum = 0 :=
    sum_sub_eq_zero_of_forall_le _ (rank p) fun x hx => by
      obtain ⟨j, hj, rfl⟩ := List.mem_drop_iff_getElem.mp hx
      exact rowLens_get_le_rank_of_ge p (by omega) (by omega)
  have htakelen : ((YoungDiagram.ofPartition p).rowLens.take (rank p)).length = rank p := by
    rw [List.length_take]; omega
  have htakeforall : ∀ x ∈ (YoungDiagram.ofPartition p).rowLens.take (rank p), rank p ≤ x := by
    intro x hx
    rw [List.mem_take_iff_getElem] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    rw [YoungDiagram.get_rowLens]
    exact rowLen_ge_rank_of_lt p (by omega)
  have htakesum := sum_sub_add_mul_length_eq _ (rank p) htakeforall
  rw [htakelen] at htakesum
  have htakesplit : (YoungDiagram.ofPartition p).rowLens.map (· - rank p)
      = ((YoungDiagram.ofPartition p).rowLens.take (rank p)).map (· - rank p)
        ++ ((YoungDiagram.ofPartition p).rowLens.drop (rank p)).map (· - rank p) := by
    rw [← List.map_append, List.take_append_drop]
  have hsumsplit : (YoungDiagram.ofPartition p).rowLens.sum
      = ((YoungDiagram.ofPartition p).rowLens.take (rank p)).sum
        + ((YoungDiagram.ofPartition p).rowLens.drop (rank p)).sum :=
    (List.sum_take_add_sum_drop _ (rank p)).symm
  rw [hrsum, hbsum, map_parts_sum_eq p (· - rank p), hsorteq,
    htakesplit, List.sum_append, hdropzero]
  have := sq (rank p)
  omega

/-- Reconstruct a partition of `d ^ 2 + m1 + m2` from a Durfee square of size `d`, a partition
`α` of `m1` with at most `d` parts (the right side), and a partition `β` of `m2` with parts at
most `d` (the bottom). -/
def merge {d m1 m2 : ℕ} (α : lengthRestricted m1 d) (β : sizeRestricted m2 d) :
    Partition (d ^ 2 + m1 + m2) :=
  Partition.ofSums (d ^ 2 + m1 + m2)
    (α.val.parts.map (· + d) + Multiset.replicate (d - α.val.length) d + β.val.parts)
    (by
      have hcard : Multiset.card α.val.parts = α.val.length := rfl
      rw [Multiset.sum_add, Multiset.sum_add, sum_map_add_const, hcard, Multiset.sum_replicate,
        smul_eq_mul, α.val.parts_sum, β.val.parts_sum, mul_comm d α.val.length,
        Nat.sub_mul, sq]
      have hle : α.val.length * d ≤ d * d := Nat.mul_le_mul_right d α.2
      omega)

theorem merge_parts_eq {d m1 m2 : ℕ} (α : lengthRestricted m1 d) (β : sizeRestricted m2 d) :
    (merge α β).parts
      = α.val.parts.map (· + d) + Multiset.replicate (d - α.val.length) d + β.val.parts := by
  change (α.val.parts.map (· + d) + Multiset.replicate (d - α.val.length) d + β.val.parts).filter
      (· ≠ 0) = _
  refine Multiset.filter_eq_self.mpr fun x hx => ?_
  rw [Multiset.mem_add, Multiset.mem_add] at hx
  rcases hx with (hx | hx) | hx
  · rw [Multiset.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have := α.val.parts_pos hy
    omega
  · obtain ⟨hn, hxd⟩ := Multiset.mem_replicate.mp hx
    rw [hxd]
    omega
  · exact (β.val.parts_pos hx).ne'

theorem merge_filter_gt_eq {d m1 m2 : ℕ} (α : lengthRestricted m1 d)
    (β : sizeRestricted m2 d) :
    (merge α β).parts.filter (d < ·) = α.val.parts.map (· + d) := by
  rw [merge_parts_eq, Multiset.filter_add, Multiset.filter_add]
  have h1 : Multiset.filter (d < ·) (α.val.parts.map (· + d)) = α.val.parts.map (· + d) := by
    refine Multiset.filter_eq_self.mpr fun x hx => ?_
    rw [Multiset.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have := α.val.parts_pos hy
    omega
  have h2 : Multiset.filter (d < ·) (Multiset.replicate (d - α.val.length) d) = 0 := by
    rw [Multiset.filter_eq_nil]
    intro x hx
    obtain ⟨-, hxd⟩ := Multiset.mem_replicate.mp hx
    rw [hxd]
    simp
  have h3 : Multiset.filter (d < ·) β.val.parts = 0 := by
    rw [Multiset.filter_eq_nil]
    intro x hx
    have := mem_sizeRestricted_iff.mp β.2 x hx
    omega
  rw [h1, h2, h3, add_zero, add_zero]

lemma merge_card_filter_gt_le {d m1 m2 : ℕ} (α : lengthRestricted m1 d) (β : sizeRestricted m2 d) :
    ((merge α β).parts.filter (d < ·)).card ≤ d := by
  rw [merge_filter_gt_eq, Multiset.card_map]
  exact α.2

theorem merge_card_filter_ge_le {d m1 m2 : ℕ}
    (α : lengthRestricted m1 d) (β : sizeRestricted m2 d) :
    d ≤ ((merge α β).parts.filter (d ≤ ·)).card := by
  rw [merge_parts_eq]
  have hAB : α.val.parts.map (· + d) + Multiset.replicate (d - α.val.length) d
      ≤ α.val.parts.map (· + d) + Multiset.replicate (d - α.val.length) d + β.val.parts :=
    Multiset.le_add_right _ _
  have hall : ∀ x ∈ α.val.parts.map (· + d) + Multiset.replicate (d - α.val.length) d, d ≤ x := by
    intro x hx
    rw [Multiset.mem_add] at hx
    rcases hx with hx | hx
    · rw [Multiset.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      omega
    · obtain ⟨-, hxd⟩ := Multiset.mem_replicate.mp hx
      rw [hxd]
  have heq : Multiset.filter (d ≤ ·)
      (α.val.parts.map (· + d) + Multiset.replicate (d - α.val.length) d)
      = α.val.parts.map (· + d) + Multiset.replicate (d - α.val.length) d :=
    Multiset.filter_eq_self.mpr hall
  have hcard : Multiset.card (α.val.parts.map (· + d)
      + Multiset.replicate (d - α.val.length) d) = d := by
    rw [Multiset.card_add, Multiset.card_map, Multiset.card_replicate]
    have hlen : Multiset.card α.val.parts = α.val.length := rfl
    have := α.2
    omega
  calc d = Multiset.card (α.val.parts.map (· + d)
        + Multiset.replicate (d - α.val.length) d) := hcard.symm
    _ = (Multiset.filter (d ≤ ·) (α.val.parts.map (· + d)
        + Multiset.replicate (d - α.val.length) d)).card := by rw [heq]
    _ ≤ _ := Multiset.card_le_card (Multiset.filter_le_filter (d ≤ ·) hAB)

theorem merge_mem_squares {d m1 m2 : ℕ} (α : lengthRestricted m1 d) (β : sizeRestricted m2 d) :
    d ∈ squares (merge α β) := by
  set q := merge α β with hq
  have hcardeq : Multiset.card q.parts = (YoungDiagram.ofPartition q).rowLens.length := by
    rw [YoungDiagram.rowLens_parts_eq]; rfl
  have hlen : d ≤ (YoungDiagram.ofPartition q).rowLens.length := by
    have h1 : d ≤ Multiset.card (q.parts.filter (d ≤ ·)) := merge_card_filter_ge_le α β
    have h2 : Multiset.card (q.parts.filter (d ≤ ·)) ≤ Multiset.card q.parts :=
      Multiset.card_le_card (Multiset.filter_le _ _)
    omega
  rw [mem_squares_iff]
  refine ⟨?_, hlen, ?_⟩
  · rcases Nat.eq_zero_or_pos d with rfl | hd
    · omega
    · have hh : d * 1 ≤ d * d := Nat.mul_le_mul_left d hd
      have hsq : d ^ 2 = d * d := sq d
      omega
  · rcases Nat.eq_zero_or_pos d with rfl | hd
    · left; rfl
    · right
      have hfilterle : d ≤ (((YoungDiagram.ofPartition q).rowLens).filter
          (d ≤ · : ℕ → Bool)).length := by
        have h1 := merge_card_filter_ge_le α β
        rwa [show (Multiset.filter (d ≤ ·) q.parts).card
            = (((YoungDiagram.ofPartition q).rowLens).filter (d ≤ · : ℕ → Bool)).length from by
          rw [YoungDiagram.rowLens_parts_eq]; rfl] at h1
      have hpw : (YoungDiagram.ofPartition q).rowLens.Pairwise (· ≥ ·) :=
        List.sortedGE_iff_pairwise.mp (YoungDiagram.ofPartition q).rowLens_sorted
      have hidx : d - 1 < (YoungDiagram.ofPartition q).rowLens.length := by omega
      rw [← YoungDiagram.get_rowLens (h := hidx)]
      exact List.take_forall_ge_of_card_filter_ge _ hpw d d hfilterle _
        (List.mem_take_iff_getElem.mpr ⟨d - 1, by omega, rfl⟩)

private lemma merge_not_mem_succ_squares {d m1 m2 : ℕ} (α : lengthRestricted m1 d)
    (β : sizeRestricted m2 d) : d + 1 ∉ squares (merge α β) := by
  set q := merge α β with hq
  intro hmem
  rw [mem_squares_iff] at hmem
  obtain ⟨hn, hlen, hval⟩ := hmem
  have hidx : d < (YoungDiagram.ofPartition q).rowLens.length := by omega
  have hval' : d + 1 ≤ (YoungDiagram.ofPartition q).rowLens[d] := by
    rw [YoungDiagram.get_rowLens]
    rcases hval with h | h
    · omega
    · simpa using h
  have hfilterle : (((YoungDiagram.ofPartition q).rowLens).filter (d < · : ℕ → Bool)).length
      ≤ d := by
    have h1 := merge_card_filter_gt_le α β
    rwa [show (Multiset.filter (d < ·) q.parts).card
        = (((YoungDiagram.ofPartition q).rowLens).filter (d < · : ℕ → Bool)).length from by
      rw [YoungDiagram.rowLens_parts_eq]; rfl] at h1
  have hpw : (YoungDiagram.ofPartition q).rowLens.Pairwise (· ≥ ·) :=
    List.sortedGE_iff_pairwise.mp (YoungDiagram.ofPartition q).rowLens_sorted
  have hmemdrop : (YoungDiagram.ofPartition q).rowLens[d] ∈
      (YoungDiagram.ofPartition q).rowLens.drop d := by
    rw [List.mem_drop_iff_getElem]
    exact ⟨0, by omega, by simp⟩
  have := List.drop_forall_le_of_card_filter_le _ hpw d d hfilterle _ hmemdrop
  omega

theorem merge_rank {d m1 m2 : ℕ} (α : lengthRestricted m1 d) (β : sizeRestricted m2 d) :
    (rank (merge α β)) = d :=
  max'_eq_of_downward_closed (squares_downward_closed _)
    (merge_mem_squares α β) (merge_not_mem_succ_squares α β)

theorem merge_right_parts_eq {d m1 m2 : ℕ} (α : lengthRestricted m1 d)
    (β : sizeRestricted m2 d) : (right (merge α β)).parts = α.val.parts := by
  set q := merge α β with hq
  have hstep1 : Multiset.filter (· > 0) (Multiset.map (· - rank q) q.parts)
      = Multiset.map (· - rank q) (q.parts.filter (· > rank q)) := by
    rw [Multiset.filter_map]
    congr 1
    exact Multiset.filter_congr fun x _ => by simp only [Function.comp_apply]; omega
  have hpos : ∀ x ∈ Multiset.filter (· > 0) (Multiset.map (· - rank q) q.parts), x ≠ 0 :=
    fun x hx => (Multiset.mem_filter.mp hx).2.ne'
  have hpartseq : (right q).parts
      = Multiset.filter (· > 0) (Multiset.map (· - rank q) q.parts) := by
    change ((Multiset.filter (· > 0) (Multiset.map (· - rank q) q.parts)).filter (· ≠ 0)) = _
    exact Multiset.filter_eq_self.mpr hpos
  rw [hpartseq, hstep1, merge_rank α β]
  have hfg : q.parts.filter (· > d) = q.parts.filter (d < ·) := rfl
  rw [hfg, merge_filter_gt_eq, Multiset.map_map]
  refine (Multiset.map_congr rfl fun x _ => ?_).trans (Multiset.map_id' α.val.parts)
  simp only [Function.comp_apply]
  omega

theorem merge_bottom_parts_eq {d m1 m2 : ℕ} (α : lengthRestricted m1 d)
    (β : sizeRestricted m2 d) : (bottom (merge α β)).parts = β.val.parts := by
  set q := merge α β with hq
  have hpartseq : (bottom q).parts
      = ((q.parts.sort (· ≥ ·)).drop (rank q) : Multiset ℕ) := by
    change (((q.parts.sort (· ≥ ·)).drop (rank q) : Multiset ℕ)).filter (· ≠ 0) = _
    refine Multiset.filter_eq_self.mpr fun x hx => ?_
    rw [Multiset.mem_coe] at hx
    have hxmem : x ∈ q.parts.sort (· ≥ ·) := List.mem_of_mem_drop hx
    have hxp : x ∈ q.parts := by
      rw [← Multiset.sort_eq q.parts (· ≥ ·), Multiset.mem_coe]; exact hxmem
    exact (q.parts_pos hxp).ne'
  rw [hpartseq, merge_rank α β, (YoungDiagram.rowLens_ofPartition_eq_sort_parts q).symm]
  set L := (YoungDiagram.ofPartition q).rowLens with hL
  have hpw : L.Pairwise (· ≥ ·) :=
    List.sortedGE_iff_pairwise.mp (YoungDiagram.ofPartition q).rowLens_sorted
  have hLparts := YoungDiagram.rowLens_parts_eq q
  have hAeq2 : Multiset.filter (d < ·) (L : Multiset ℕ) = α.val.parts.map (· + d) := by
    rw [← hLparts]; exact merge_filter_gt_eq α β
  have hAlen : (L.filter (d < · : ℕ → Bool)).length = α.val.length := by
    have heq : (Multiset.filter (d < ·) (L : Multiset ℕ)).card
        = (L.filter (d < · : ℕ → Bool)).length := rfl
    rw [← heq, hAeq2, Multiset.card_map]
  have hdlen : d ≤ L.length := by
    have h1 : d ≤ Multiset.card (q.parts.filter (d ≤ ·)) := merge_card_filter_ge_le α β
    have h2 : Multiset.card (q.parts.filter (d ≤ ·)) ≤ Multiset.card q.parts :=
      Multiset.card_le_card (Multiset.filter_le _ _)
    have h3 : Multiset.card q.parts = L.length := by rw [hLparts]; rfl
    omega
  have hdge : d ≤ (L.filter (d ≤ · : ℕ → Bool)).length := by
    have h1 := merge_card_filter_ge_le α β
    rwa [show (Multiset.filter (d ≤ ·) q.parts).card
        = (L.filter (d ≤ · : ℕ → Bool)).length from by rw [hLparts]; rfl] at h1
  have : α.val.length ≤ d := α.2
  have htake : (L.take d : Multiset ℕ)
      = (L.take α.val.length : Multiset ℕ) + Multiset.replicate (d - α.val.length) d :=
    List.take_split L hpw d α.val.length this hdlen hAlen hdge
  have htakeAeq : (L.take α.val.length : Multiset ℕ) = α.val.parts.map (· + d) := by
    rw [List.take_card_filter_eq L hpw d α.val.length (by omega) hAlen, hAeq2]
  rw [htakeAeq] at htake
  have hLtd : (L.take d : Multiset ℕ) + (L.drop d : Multiset ℕ) = (L : Multiset ℕ) := by
    calc (L.take d : Multiset ℕ) + (L.drop d : Multiset ℕ)
        = ((L.take d ++ L.drop d : List ℕ) : Multiset ℕ) := by rw [Multiset.coe_add]
      _ = (L : Multiset ℕ) := by rw [List.take_append_drop]
  rw [← hLparts, merge_parts_eq, htake] at hLtd
  exact add_left_cancel hLtd

@[simp]
theorem reindex_rank {n : ℕ} (p : Partition n) (m : ℕ) (h : n = m) :
    rank (reindex p m h) = rank p := by
  subst h; rfl

theorem merge_decompose_parts_eq {n : ℕ} (p : Partition n) :
    (right p).parts.map (· + rank p) + Multiset.replicate (rank p - (right p).length) (rank p)
      + (bottom p).parts = p.parts := by
  set d := rank p
  have hAstep : Multiset.filter (· > 0) (Multiset.map (· - d) p.parts)
        = Multiset.map (· - d) (p.parts.filter (· > d)) := by
      rw [Multiset.filter_map]
      congr 1
      exact Multiset.filter_congr fun x _ => by simp only [Function.comp_apply]; omega
  have hrmap : (right p).parts.map (· + d) = p.parts.filter (· > d) := by
    rw [right_parts_eq p, hAstep, Multiset.map_map]
    refine (Multiset.map_congr rfl fun x hx => ?_).trans (Multiset.map_id' _)
    simp only [Function.comp_apply]
    have := (Multiset.mem_filter.mp hx).2
    omega
  have hrlen : (right p).length = (p.parts.filter (· > d)).card := by
    change (right p).parts.card = _
    rw [right_parts_eq p, hAstep, Multiset.card_map]
  rw [hrmap, hrlen, bottom_parts_eq p]
  rw [(YoungDiagram.rowLens_ofPartition_eq_sort_parts p).symm]
  set L := (YoungDiagram.ofPartition p).rowLens with hL
  have hpw : L.Pairwise (· ≥ ·) :=
    List.sortedGE_iff_pairwise.mp (YoungDiagram.ofPartition p).rowLens_sorted
  have hLparts : p.parts = (L : Multiset ℕ) := YoungDiagram.rowLens_parts_eq p
  set k := (p.parts.filter (· > d)).card with hk
  have hAlen : (L.filter (d < · : ℕ → Bool)).length = k := by
    have heq2 : (Multiset.filter (d < ·) (L : Multiset ℕ)).card
        = (L.filter (d < · : ℕ → Bool)).length := rfl
    have hfg : p.parts.filter (· > d) = p.parts.filter (d < ·) := rfl
    rw [← heq2, ← hLparts, ← hfg]
  have hdlen : d ≤ L.length := rank_le_rowLens_length p
  have hkled : k ≤ d := by rw [hk]; exact card_parts_gt_rank_le p
  have hdge : d ≤ (L.filter (d ≤ · : ℕ → Bool)).length := by
    have htakeforall : ∀ x ∈ L.take d, d ≤ x := by
      intro x hx
      rw [List.mem_take_iff_getElem] at hx
      obtain ⟨j, hj, rfl⟩ := hx
      have hjd : j < d := by omega
      have := rowLen_ge_rank_of_lt p hjd
      rwa [← YoungDiagram.get_rowLens] at this
    have hsub : (L.take d : Multiset ℕ) ≤ Multiset.filter (d ≤ ·) (L : Multiset ℕ) :=
      Multiset.le_filter.mpr ⟨List.take_le_coe L d,
                              fun a ha => htakeforall a (Multiset.mem_coe.mp ha)⟩
    have := Multiset.card_le_card hsub
    have h2 : Multiset.card (L.take d : Multiset ℕ) = d := by
      change (L.take d).length = d
      rw [List.length_take]; omega
    have h3 : Multiset.card (Multiset.filter (d ≤ ·) (L : Multiset ℕ))
        = (L.filter (d ≤ · : ℕ → Bool)).length := rfl
    omega
  have htake : (L.take d : Multiset ℕ) = (L.take k : Multiset ℕ) + Multiset.replicate (d - k) d :=
    List.take_split L hpw d k hkled hdlen hAlen hdge
  have htakekeq : (L.take k : Multiset ℕ) = p.parts.filter (· > d) := by
    rw [List.take_card_filter_eq L hpw d k (by omega) hAlen, ← hLparts]
  rw [htakekeq] at htake
  have hLtd : (L.take d : Multiset ℕ) + (L.drop d : Multiset ℕ) = (L : Multiset ℕ) := by
    calc (L.take d : Multiset ℕ) + (L.drop d : Multiset ℕ)
        = ((L.take d ++ L.drop d : List ℕ) : Multiset ℕ) := by rw [Multiset.coe_add]
      _ = (L : Multiset ℕ) := by rw [List.take_append_drop]
  rw [htake] at hLtd
  rwa [← hLparts] at hLtd

def fiberToFun {n d m1 m2 : ℕ} (hsum : d ^ 2 + m1 + m2 = n) (p : Partition n)
    (hd : rank p = d) (hm1 : (right p).parts.sum = m1) :
    lengthRestricted m1 d × sizeRestricted m2 d :=
  have hm2 : (bottom p).parts.sum = m2 := by
    have hsize := rank_sq_add_size_eq p
    have hd2 : (rank p) ^ 2 = d ^ 2 := by rw [hd]
    omega
  ⟨⟨reindex (right p) m1 ((right p).parts_sum.symm.trans hm1), by
      subst hd; exact right_length_le p⟩,
    ⟨reindex (bottom p) m2 ((bottom p).parts_sum.symm.trans hm2), by
      subst hd
      rw [mem_sizeRestricted_iff]
      intro i hi
      rw [reindex_parts] at hi
      exact maxPart_le_iff.mp (bottom_maxPart_le p) i hi⟩⟩

def fiberInvFun {n d m1 m2 : ℕ} (hsum : d ^ 2 + m1 + m2 = n)
    (αβ : lengthRestricted m1 d × sizeRestricted m2 d) :
    {p : Partition n // rank p = d ∧ (right p).parts.sum = m1} :=
  ⟨reindex (merge αβ.1 αβ.2) n hsum, by
    refine ⟨?_, ?_⟩
    · rw [reindex_rank]; exact merge_rank αβ.1 αβ.2
    · show (right (reindex (merge αβ.1 αβ.2) n hsum)).parts.sum = m1
      have hrparts : (right (reindex (merge αβ.1 αβ.2) n hsum)).parts
          = (right (merge αβ.1 αβ.2)).parts := by
        rw [right_parts_eq, right_parts_eq, reindex_rank, reindex_parts]
      rw [hrparts, merge_right_parts_eq]
      exact αβ.1.val.parts_sum⟩

theorem merge_decompose_parts_eq' {n d : ℕ} (p : Partition n) (hd : rank p = d) :
    (right p).parts.map (· + d) + Multiset.replicate (d - (right p).length) d
      + (bottom p).parts = p.parts := by
  subst hd; exact merge_decompose_parts_eq p

/-- The Durfee-square bijection: a partition `n` with Durfee rank `d` and right-side size `m1`
corresponds to a pair of a length-restricted partition of `m1` (the right side) and a
size-restricted partition of `m2` (the bottom), where `d ^ 2 + m1 + m2 = n`. -/
def fiberEquiv {n d m1 m2 : ℕ} (hsum : d ^ 2 + m1 + m2 = n) :
    {p : Partition n // rank p = d ∧ (right p).parts.sum = m1} ≃
      lengthRestricted m1 d × sizeRestricted m2 d where
  toFun p := fiberToFun hsum p.val p.2.1 p.2.2
  invFun := fiberInvFun hsum
  left_inv p := by
    refine Subtype.ext (Partition.ext ?_)
    change (reindex (merge _ _) n hsum).parts = p.val.parts
    rw [reindex_parts, merge_parts_eq]
    exact merge_decompose_parts_eq' p.val p.2.1
  right_inv αβ := by
    obtain ⟨α, β⟩ := αβ
    refine Prod.ext (Subtype.ext (Partition.ext ?_)) (Subtype.ext (Partition.ext ?_))
    · change (right (reindex (merge α β) n hsum)).parts = α.val.parts
      rw [right_parts_eq, reindex_rank, reindex_parts,
        ← right_parts_eq, merge_right_parts_eq]
    · change (bottom (reindex (merge α β) n hsum)).parts = β.val.parts
      rw [bottom_parts_eq, reindex_rank, reindex_parts,
        ← bottom_parts_eq, merge_bottom_parts_eq]

/-- Counting partitions of `n` with Durfee rank `d`: split the remaining size `n - d ^ 2` between
the right side (a length-restricted partition) and the bottom (a size-restricted partition). -/
theorem card_rankFiber {n d : ℕ} (hd : d ^ 2 ≤ n) :
    Fintype.card {p : Partition n // rank p = d} =
      ∑ mm ∈ Finset.antidiagonal (n - d ^ 2),
        Fintype.card (lengthRestricted mm.1 d) * Fintype.card (sizeRestricted mm.2 d) := by
  rw [Fintype.card_subtype]
  let rankFilter := fun p : Partition n => rank p = d
  have hstep1 : (Finset.univ.filter rankFilter).card
      = ∑ m1 ∈ Finset.range (n - d ^ 2 + 1),
        ((Finset.univ.filter rankFilter).filter (fun p => (right p).parts.sum = m1)).card := by
    refine Finset.card_eq_sum_card_fiberwise (fun p hp => ?_)
    rw [Finset.mem_coe, Finset.mem_filter] at hp
    have hsize := rank_sq_add_size_eq p
    have hd2 : (rank p) ^ 2 = d ^ 2 := by rw [hp.2]
    rw [Finset.mem_coe, Finset.mem_range]
    omega
  rw [hstep1, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun m1 m2 => Fintype.card (lengthRestricted m1 d) * Fintype.card (sizeRestricted m2 d))]
  refine Finset.sum_congr rfl fun m1 hm1 => ?_
  rw [Finset.mem_range] at hm1
  have hsum : d ^ 2 + m1 + (n - d ^ 2 - m1) = n := by omega
  rw [Finset.filter_filter, ← Fintype.card_subtype, ← Fintype.card_prod]
  exact Fintype.card_congr (fiberEquiv hsum)

/-- Every partition of `n` has Durfee rank at most `Nat.sqrt n`, so the partitions of `n` split
into fibers over the possible Durfee ranks `d ≤ Nat.sqrt n`. -/
theorem card_eq_sum_rankFiber (n : ℕ) :
    Fintype.card (Partition n) =
      ∑ d ∈ Finset.range (Nat.sqrt n + 1), Fintype.card {p : Partition n // rank p = d} := by
  simp_rw [Fintype.card_subtype]
  refine Finset.card_eq_sum_card_fiberwise (fun p _ => ?_)
  rw [Finset.mem_coe, Finset.mem_range]
  have h2 : (rank p) ^ 2 ≤ n := (have := rank_sq_add_size_eq p; by omega)
  exact Nat.lt_succ_of_le (Nat.le_sqrt'.mpr h2)

/-- **Durfee square identity** (cardinality form): the number of partitions of `n` equals the sum
over Durfee square sizes `d` of the number of ways to split the remaining `n - d ^ 2` between a
length-restricted right side and a size-restricted bottom. -/
theorem card_eq_sum_sq_add_antidiagonal (n : ℕ) :
    Fintype.card (Partition n) =
      ∑ d ∈ Finset.range (Nat.sqrt n + 1), ∑ mm ∈ Finset.antidiagonal (n - d ^ 2),
        Fintype.card (lengthRestricted mm.1 d) * Fintype.card (sizeRestricted mm.2 d) := by
  rw [card_eq_sum_rankFiber]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.mem_range] at hd
  exact card_rankFiber (Nat.le_sqrt'.mp (Nat.lt_succ_iff.mp hd))

/-- **Durfee square generating function identity** (strong form, in `ℤ⟦X⟧`): the generating
function for the number of partitions of `n` decomposes as a sum over Durfee square sizes `d`,
each term being `X ^ (d ^ 2)` times the generating functions of the right side and the bottom of
the Durfee symbol. -/
theorem hasSum_card_powerSeries :
    HasSum (fun d : ℕ ↦ (X : ℤ⟦X⟧) ^ d ^ 2 * bInv (X; X)_d * bInv (X; X)_d) powerSeriesCard := by
  rw [hasSum_iff_hasSum_coeff]
  intro n
  rw [coeff_powerSeriesCard]
  have hzero : ∀ d ∉ Finset.range (Nat.sqrt n + 1),
      ((X : ℤ⟦X⟧) ^ d ^ 2 * bInv (X; X)_d * bInv (X; X)_d).coeff n = 0 := by
    intro d hd
    rw [Finset.mem_range, not_lt] at hd
    have hd2 : n < d ^ 2 := Nat.sqrt_lt'.mp (by omega)
    rw [mul_assoc, coeff_X_pow_mul', if_neg (by omega)]
  have hsum : HasSum (fun d ↦ ((X : ℤ⟦X⟧) ^ d ^ 2 * bInv (X; X)_d * bInv (X; X)_d).coeff n)
      (∑ d ∈ Finset.range (Nat.sqrt n + 1),
        ((X : ℤ⟦X⟧) ^ d ^ 2 * bInv (X; X)_d * bInv (X; X)_d).coeff n) :=
    hasSum_sum_of_ne_finset_zero hzero
  have hSeq : (∑ d ∈ Finset.range (Nat.sqrt n + 1),
      ((X : ℤ⟦X⟧) ^ d ^ 2 * bInv (X; X)_d * bInv (X; X)_d).coeff n)
      = (Fintype.card (Partition n) : ℤ) := by
    rw [card_eq_sum_sq_add_antidiagonal]
    push_cast
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Finset.mem_range] at hd
    have hd2 : d ^ 2 ≤ n := Nat.le_sqrt'.mp (Nat.lt_succ_iff.mp hd)
    rw [mul_assoc, coeff_X_pow_mul', if_pos hd2, coeff_mul]
    refine Finset.sum_congr rfl fun mm hmm => ?_
    nth_rewrite 2 [← powerSeriesSizeRestricted_eq_bInv_qPochhammer d]
    rw [← powerSeriesLengthRestricted_eq_bInv_qPochhammer d, powerSeriesSizeRestricted]
    simp [PowerSeries.coeff_mk]
  rwa [hSeq] at hsum

/-- **Durfee square generating function identity**: for a topologically nilpotent `q` in a
complete nonarchimedean ring, the generating function for the partition-counting sequence
decomposes over Durfee square sizes `d` as `∑ q ^ (d ^ 2) * bInv (q; q)_d * bInv (q; q)_d`. -/
theorem hasSum_card {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
    [NonarchimedeanRing R] [CompleteSpace R] [T2Space R]
    {q : R} (hq : IsTopologicallyNilpotent q := by simp) :
    HasSum (fun d : ℕ ↦ q ^ d ^ 2 * bInv (q; q)_d * bInv (q; q)_d) (bInv (q; q)_∞) := by
  have hxn : IsTopologicallyNilpotent (X : ℤ⟦X⟧) := by simp
  have h1 : HasSum (fun n ↦ Partition.card n • (X : ℤ⟦X⟧) ^ n) powerSeriesCard := by
    simpa [monomial_eq_C_mul_X_pow] using hasSum_of_monomials_self powerSeriesCard
  have htsum : intEval q powerSeriesCard = bInv (q; q)_∞ :=
    (h1.map (intEval q) (by fun_prop)).unique <|
      (Nat.Partition.hasSum_card hq).congr_fun fun n => by simp [hq]
  convert hasSum_card_powerSeries.map (intEval q) (by fun_prop) using 1 <;>
    simp [funext_iff, hq, htsum, isUnit_qPochhammer hxn hxn, IsUnit.map_bInv, map_qPochhammer]

/-- For the version with `HasSum`, see `hasSum_card`. -/
theorem tsum_card {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
    [NonarchimedeanRing R] [CompleteSpace R] [T2Space R]
    {q : R} (hq : IsTopologicallyNilpotent q := by simp) :
    ∑' d : ℕ, q ^ d ^ 2 * bInv (q; q)_d * bInv (q; q)_d = bInv (q; q)_∞ :=
  (hasSum_card hq).tsum_eq

end Durfee

end Nat.Partition
