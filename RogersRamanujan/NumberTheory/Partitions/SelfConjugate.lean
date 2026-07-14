module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Combinatorics.Young.YoungDiagram
public import Mathlib.Data.List.GetD
import Mathlib.GroupTheory.PGroup

public import RogersRamanujan.NumberTheory.Partitions.Conjugate

@[expose] public section

/-!
# Self-conjugate partitions and partitions into distinct odd parts

This file proves that the number of self-conjugate partitions of `n` equals the number of
partitions of `n` into distinct odd parts, via an explicit hook-wrapping bijection on Young
diagrams.

## Main definitions

* `YoungDiagram.IsSelfConjList`: a row-length list represents a self-conjugate Young diagram
* `List.wrapHook`, `List.hookRowLens`, `List.peelHooks`: the hook-wrapping/peeling operations
  underlying the bijection
* `Nat.Partition.selfConjugate`: the finset of partitions equal to their own conjugate
* `Nat.Partition.toSelfConj`, `Nat.Partition.fromSelfConj`: the two directions of the bijection
* `Nat.Partition.selfConjEquivOddDistinct`: the bijection as an `Equiv`

## Main results

* `Nat.Partition.card_parity_eq_selfConjugate_card_parity`: conjugation is an involution, so the
  total number of partitions of `n` and the number of self-conjugate partitions of `n` agree
  mod 2
* `Nat.Partition.card_selfConjugate_eq_card_oddDistincts`: self-conjugate partitions of `n`
  biject with partitions of `n` into distinct odd parts
-/

namespace YoungDiagram

/-- Unconditional version of `rowLen_ofRowLens`, using `List.getI` (default `0`) instead of
requiring the index to be within bounds. -/
theorem rowLen_ofRowLens_getI {w : List ℕ} {hw : w.SortedGE} (i : ℕ) :
    (ofRowLens w hw).rowLen i = w.getI i := by
  rcases lt_or_ge i w.length with h | h
  · exact (rowLen_ofRowLens ⟨i, h⟩).trans (List.getI_eq_getElem w h).symm
  · rw [List.getI_eq_default w h]
    by_contra hne
    exact absurd (mem_ofRowLens.mp (mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero hne))).1
      (not_lt.mpr h)

/-- A row-length list represents a self-conjugate Young diagram: cell membership (via row
lengths, with out-of-bounds treated as `0`) is symmetric in the two coordinates. -/
def IsSelfConjList (L : List ℕ) : Prop := ∀ i j, i < L.getI j ↔ j < L.getI i

/-- The transpose of the Young diagram with row-length list `w` equals itself iff `w`
represents a self-conjugate shape. -/
theorem transpose_ofRowLens_eq_self_iff {w : List ℕ} {hw : w.SortedGE} :
    (ofRowLens w hw).transpose = ofRowLens w hw ↔ IsSelfConjList w :=
  SetLike.ext_iff.trans <| Prod.forall.trans <| forall_congr' fun i => forall_congr' fun j => by
    rw [mem_transpose, Prod.swap_prod_mk, mem_iff_lt_rowLen, mem_iff_lt_rowLen,
      rowLen_ofRowLens_getI, rowLen_ofRowLens_getI]

end YoungDiagram

namespace List

/-- Wrap an odd hook of arm-length `a` around the row-length list `r` of a smaller
self-conjugate shape, producing the row-length list of the larger self-conjugate shape obtained
by adding a border hook of size `2 * a + 1`. -/
def wrapHook (a : ℕ) (r : List ℕ) : List ℕ :=
  (a + 1) :: (r.map (· + 1) ++ List.replicate (a - r.length) 1)

@[simp]
theorem wrapHook_getI_zero (a : ℕ) (r : List ℕ) : (wrapHook a r).getI 0 = a + 1 := rfl

theorem wrapHook_length {a : ℕ} {r : List ℕ} (h : r.length ≤ a) :
    (wrapHook a r).length = a + 1 := by
  grind [wrapHook]

theorem wrapHook_pos (a : ℕ) (r : List ℕ) : ∀ x ∈ wrapHook a r, 0 < x := by grind [wrapHook]

theorem sum_map_add_one (r : List ℕ) : (r.map (· + 1)).sum = r.sum + r.length := by
  induction r with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

theorem wrapHook_sum {a : ℕ} {r : List ℕ} (h : r.length ≤ a) :
    (wrapHook a r).sum = (2 * a + 1) + r.sum := by
  simp only [wrapHook, List.sum_cons, List.sum_append, List.sum_replicate, smul_eq_mul, mul_one,
    sum_map_add_one]
  omega

theorem wrapHook_getI_succ {a : ℕ} {r : List ℕ} (h : r.length ≤ a) (m : ℕ) :
    (wrapHook a r).getI (m + 1) =
      if m < r.length then r.getI m + 1 else if m < a then 1 else 0 := by
  unfold wrapHook
  rw [List.getI_cons_succ]
  split_ifs with h1 h2
  · rw [List.getI_append _ _ _ (by simpa using h1),
      List.getI_eq_getElem _ (show m < (r.map (· + 1)).length by simpa using h1),
      List.getElem_map, List.getI_eq_getElem _ h1]
  · rw [List.getI_append_right _ _ _ (by simpa using h1), List.length_map,
      List.getI_eq_getElem _ (show m - r.length < (List.replicate (a - r.length) 1).length by
        simp; omega),
      List.getElem_replicate]
  · rw [List.getI_append_right _ _ _ (by simpa using h1), List.length_map,
      List.getI_eq_default _ (show (List.replicate (a - r.length) 1).length ≤ m - r.length by
        simp; omega)]
    rfl

theorem SortedGE.getI_antitone {r : List ℕ} (hr : r.SortedGE) {i j : ℕ} (hij : i ≤ j) :
    r.getI j ≤ r.getI i := by
  rcases lt_or_ge j r.length with hj | hj
  · have hi : i < r.length := lt_of_le_of_lt hij hj
    rw [List.getI_eq_getElem r hi, List.getI_eq_getElem r hj]
    exact hr.getElem_ge_getElem_of_le hij
  · rw [List.getI_eq_default r hj]
    exact Nat.zero_le _

theorem wrapHook_sortedGE {a : ℕ} {r : List ℕ} (hr : r.SortedGE) (h : r.length ≤ a)
    (hh : r.getI 0 ≤ a) : (wrapHook a r).SortedGE := by
  rw [sortedGE_iff_getElem_ge_getElem_of_le]
  intro i j _ _ hji
  rw [← List.getI_eq_getElem _ (by omega), ← List.getI_eq_getElem _ (by omega)]
  rcases i with _ | m
  · interval_cases j
    simp
  · rcases j with _ | k
    · rw [wrapHook_getI_zero, wrapHook_getI_succ h]
      have hanti : r.getI m ≤ r.getI 0 := hr.getI_antitone (Nat.zero_le m)
      split_ifs <;> omega
    · rw [wrapHook_getI_succ h, wrapHook_getI_succ h]
      have hkm : k ≤ m := by omega
      have hanti : r.getI m ≤ r.getI k := hr.getI_antitone hkm
      split_ifs <;> omega

theorem wrapHook_isSelfConj {a : ℕ} {r : List ℕ} (hrs : r.SortedGE)
    (hsc : YoungDiagram.IsSelfConjList r) (hlen : r.getI 0 = r.length) (h : r.length ≤ a) :
    YoungDiagram.IsSelfConjList (wrapHook a r) := by
  have key : ∀ i j : ℕ, i < (wrapHook a r).getI j → j < (wrapHook a r).getI i := by
    intro i j hij
    rcases j with _ | k
    · rw [wrapHook_getI_zero] at hij
      rcases i with _ | m
      · simp
      · rw [wrapHook_getI_succ h]
        have hma : m < a := by omega
        split_ifs <;> omega
    · rw [wrapHook_getI_succ h] at hij
      rcases i with _ | m
      · rw [wrapHook_getI_zero]
        split_ifs at hij <;> omega
      · rw [wrapHook_getI_succ h]
        have hsym := hsc m k
        have hanti : r.getI k ≤ r.getI 0 := hrs.getI_antitone (Nat.zero_le k)
        split_ifs at hij ⊢ <;> omega
  intro i j
  exact ⟨key i j, key j i⟩

/-- Build the row-length list of a self-conjugate Young diagram from a strictly decreasing
list of odd positive parts, by wrapping successive hooks (largest outermost). -/
def hookRowLens : List ℕ → List ℕ
  | [] => []
  | μ :: rest => wrapHook ((μ - 1) / 2) (hookRowLens rest)

theorem hookRowLens_spec (l : List ℕ) (hl : l.SortedGT) (hodd : ∀ x ∈ l, Odd x) :
    (hookRowLens l).SortedGE ∧ (∀ x ∈ hookRowLens l, 0 < x) ∧
    (hookRowLens l).getI 0 = (hookRowLens l).length ∧
    (hookRowLens l).sum = l.sum ∧ YoungDiagram.IsSelfConjList (hookRowLens l) := by
  induction l with
  | nil => simp [hookRowLens, YoungDiagram.IsSelfConjList, List.sortedGE_iff_pairwise]
  | cons μ rest ih =>
    have hrest_sorted : rest.SortedGT :=
      Pairwise.sortedGT (List.pairwise_cons.mp hl.pairwise).2
    have hrest_odd : ∀ x ∈ rest, Odd x := fun x hx => hodd x (List.mem_cons_of_mem μ hx)
    obtain ⟨ihs, ihp, ihg, ihsum, ihsc⟩ := ih hrest_sorted hrest_odd
    have hμodd : Odd μ := hodd μ List.mem_cons_self
    have hlen_le : (hookRowLens rest).length ≤ (μ - 1) / 2 := by
      rw [← ihg]
      rcases rest with _ | ⟨ν, rest'⟩
      · simp [hookRowLens]
      · have hμν : ν < μ :=
          (List.pairwise_cons.mp hl.pairwise).1 ν List.mem_cons_self
        have hνodd : Odd ν := hrest_odd ν List.mem_cons_self
        obtain ⟨p, hp⟩ := hμodd
        obtain ⟨q, hq⟩ := hνodd
        simp only [hookRowLens, wrapHook_getI_zero]
        omega
    refine ⟨wrapHook_sortedGE ihs hlen_le (ihg ▸ hlen_le), wrapHook_pos _ _, ?_, ?_,
      wrapHook_isSelfConj ihs ihsc ihg hlen_le⟩
    · change (wrapHook _ _).getI 0 = (wrapHook _ _).length
      rw [wrapHook_getI_zero, wrapHook_length hlen_le]
    · change (wrapHook _ _).sum = _
      rw [wrapHook_sum hlen_le, ihsum, List.sum_cons]
      obtain ⟨p, hp⟩ := hμodd
      omega

/-- Peel the outer diagonal hook off the row-length list of a self-conjugate Young diagram,
producing the list of odd hook lengths (largest outermost). Inverse to `hookRowLens`. -/
def peelHooks : List ℕ → List ℕ
  | [] => []
  | a :: rest => (2 * (a - 1) + 1) :: peelHooks ((rest.map (· - 1)).filter (· ≠ 0))
termination_by l => l.length
decreasing_by
  simp_wf
  refine le_trans (List.length_filter_le _ _) ?_
  simp

theorem peelHooks_hookRowLens (l : List ℕ) (hl : l.SortedGT) (hodd : ∀ x ∈ l, Odd x) :
    peelHooks (hookRowLens l) = l := by
  induction l with
  | nil => simp [hookRowLens, peelHooks]
  | cons μ rest ih =>
    have hrest_sorted : rest.SortedGT := Pairwise.sortedGT (List.pairwise_cons.mp hl.pairwise).2
    have hrest_odd : ∀ x ∈ rest, Odd x := fun x hx => hodd x (List.mem_cons_of_mem μ hx)
    have hμodd : Odd μ := hodd μ List.mem_cons_self
    obtain ⟨-, ihp, -, -, -⟩ := List.hookRowLens_spec rest hrest_sorted hrest_odd
    have hfilter : (hookRowLens rest).filter (· ≠ 0) = hookRowLens rest :=
      List.filter_eq_self.mpr (fun x hx => by simp [(ihp x hx).ne'])
    change peelHooks (wrapHook ((μ - 1) / 2) (hookRowLens rest)) = μ :: rest
    unfold wrapHook
    rw [peelHooks]
    obtain ⟨p, hp⟩ := hμodd
    have harg : (((hookRowLens rest).map (· + 1) ++
        List.replicate (((μ - 1) / 2) - (hookRowLens rest).length) 1).map (· - 1)).filter
        (· ≠ 0) = hookRowLens rest := by
      rw [List.map_append, List.map_map]
      have hcomp : ((· - 1) ∘ (· + 1) : ℕ → ℕ) = id := by ext x; change x + 1 - 1 = x; omega
      rw [hcomp, List.map_id, List.map_replicate]
      rw [List.filter_append, hfilter]
      simp
    rw [harg]
    refine List.cons.injEq .. |>.mpr ⟨by omega, ih hrest_sorted hrest_odd⟩

/-- Dual of `wrapHook_getI_succ`: for a weakly decreasing list of positive naturals, its
values are recovered from the "unwrapped" list `(rest.map (·-1)).filter (·≠0)` by adding back
the peeled hook (or `1`/`0` beyond that shape's rows). -/
theorem filter_ne_zero_cons (a : ℕ) (l : List ℕ) :
    (a :: l).filter (· ≠ 0) = if a = 0 then l.filter (· ≠ 0) else a :: l.filter (· ≠ 0) := by
  by_cases h : a = 0 <;> simp [h]

theorem unwrap_getI {rest : List ℕ} (hrs : rest.SortedGE) (hrp : ∀ x ∈ rest, 0 < x) (m : ℕ) :
    rest.getI m = if m < ((rest.map (· - 1)).filter (· ≠ 0)).length then
        ((rest.map (· - 1)).filter (· ≠ 0)).getI m + 1
      else if m < rest.length then 1 else 0 := by
  induction rest generalizing m with
  | nil => simp
  | cons b rest' ih =>
    have hrest'_sorted : rest'.SortedGE := Pairwise.sortedGE (List.pairwise_cons.mp hrs.pairwise).2
    have hrest'_pos : ∀ x ∈ rest', 0 < x := fun x hx => hrp x (List.mem_cons_of_mem b hx)
    have hb_pos : 0 < b := hrp b List.mem_cons_self
    have hb_ge : ∀ y ∈ rest', b ≥ y := (List.pairwise_cons.mp hrs.pairwise).1
    by_cases hb1 : b = 1
    · have hr''_nil : (rest'.map (· - 1)).filter (· ≠ 0) = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        have h1 := hb_ge y hy
        have h2 := hrest'_pos y hy
        simp only [ne_eq, decide_eq_true_eq, not_not]
        omega
      have hlhs : ((b :: rest').map (· - 1)).filter (· ≠ 0) = [] := by
        rw [List.map_cons, filter_ne_zero_cons, if_pos (by omega), hr''_nil]
      rw [hlhs]
      rcases m with _ | k
      · simp [hb1]
      · rw [List.getI_cons_succ]
        have hik := ih hrest'_sorted hrest'_pos k
        rw [hr''_nil] at hik
        simpa using hik
    · have hlhs : ((b :: rest').map (· - 1)).filter (· ≠ 0) =
          (b - 1) :: (rest'.map (· - 1)).filter (· ≠ 0) := by
        rw [List.map_cons, filter_ne_zero_cons, if_neg (by omega)]
      rw [hlhs]
      rcases m with _ | k
      · rw [List.getI_cons_zero, if_pos (by simp), List.getI_cons_zero]
        omega
      · rw [List.getI_cons_succ, List.length_cons, List.getI_cons_succ, List.length_cons]
        have hik := ih hrest'_sorted hrest'_pos k
        by_cases hk : k < ((rest'.map (· - 1)).filter (· ≠ 0)).length
        · rw [if_pos hk] at hik
          rw [if_pos (by omega), hik]
        · rw [if_neg hk] at hik
          rw [if_neg (by omega), hik]
          simp only [Nat.add_lt_add_iff_right]

theorem eq_of_getI_eq_of_pos {l1 l2 : List ℕ} (h : ∀ i, l1.getI i = l2.getI i)
    (h1 : ∀ x ∈ l1, 0 < x) (h2 : ∀ x ∈ l2, 0 < x) : l1 = l2 := by
  have key : ∀ {l1 l2 : List ℕ}, (∀ i, l1.getI i = l2.getI i) → (∀ x ∈ l2, 0 < x) →
      l2.length ≤ l1.length := by
    intro l1 l2 h h2
    by_contra hlt
    push Not at hlt
    have hmem : l2.getI l1.length ∈ l2 := List.getI_eq_getElem l2 hlt ▸ List.getElem_mem _
    have hpos := h2 _ hmem
    have hgi := h l1.length
    rw [List.getI_eq_default l1 le_rfl] at hgi
    simp only [show (default : ℕ) = 0 from rfl] at hgi
    omega
  have hlen : l1.length = l2.length :=
    le_antisymm (key (fun i => (h i).symm) h1) (key h h2)
  apply List.ext_getElem hlen
  intro i hi1 hi2
  have hgi := h i
  rwa [List.getI_eq_getElem l1 hi1, List.getI_eq_getElem l2 hi2] at hgi

theorem _root_.YoungDiagram.IsSelfConjList.getI_zero_eq_length {r : List ℕ}
    (hsc : YoungDiagram.IsSelfConjList r) (hrp : ∀ x ∈ r, 0 < x) :
    r.getI 0 = r.length := by
  rcases Nat.eq_zero_or_pos r.length with hz | hz
  · simp [List.length_eq_zero_iff.mp hz]
  · have h1 : r.length - 1 < r.getI 0 := by
      have hmem : r.getI (r.length - 1) ∈ r := by
        rw [List.getI_eq_getElem r (by omega)]
        exact List.getElem_mem _
      exact (hsc (r.length - 1) 0).mpr (hrp _ hmem)
    have h2 : ¬ r.length < r.getI 0 := by
      intro hcon
      have hc := (hsc r.length 0).mp hcon
      rw [List.getI_eq_default r le_rfl] at hc
      simp only [show (default : ℕ) = 0 from rfl] at hc
      omega
    omega

theorem selfConj_decomp_step {L : List ℕ} (hL : L ≠ []) (hs : L.SortedGE) (hp : ∀ x ∈ L, 0 < x)
    (hsc : YoungDiagram.IsSelfConjList L) (hg : L.getI 0 = L.length) :
    ∃ r' : List ℕ, r'.SortedGE ∧ (∀ x ∈ r', 0 < x) ∧ YoungDiagram.IsSelfConjList r' ∧
      r'.getI 0 = r'.length ∧ r'.length < L.length ∧ L = wrapHook (L.getI 0 - 1) r' := by
  obtain ⟨a, rest, rfl⟩ := List.exists_cons_of_ne_nil hL
  simp only [List.getI_cons_zero] at hg ⊢
  have ha_pos : 0 < a := by rw [hg]; simp
  have hrest_sorted : rest.SortedGE := Pairwise.sortedGE (List.pairwise_cons.mp hs.pairwise).2
  have hrest_pos : ∀ x ∈ rest, 0 < x := fun x hx => hp x (List.mem_cons_of_mem a hx)
  have hunwrap := unwrap_getI hrest_sorted hrest_pos
  have hlen_eq : rest.length = a - 1 := by rw [hg]; simp
  have hr'_len_le : ((rest.map (· - 1)).filter (· ≠ 0)).length ≤ rest.length := by
    simpa using List.length_filter_le (· ≠ (0 : ℕ)) (rest.map (· - 1))
  have hr'_pos : ∀ x ∈ (rest.map (· - 1)).filter (· ≠ 0), 0 < x := by
    intro x hx
    rw [List.mem_filter] at hx
    simp only [ne_eq, decide_eq_true_eq] at hx
    omega
  have key : ∀ i j : ℕ, i < ((rest.map (· - 1)).filter (· ≠ 0)).getI j →
      j < ((rest.map (· - 1)).filter (· ≠ 0)).getI i := by
    intro i j hij
    by_cases hj : j < ((rest.map (· - 1)).filter (· ≠ 0)).length
    · have e1 : rest.getI j = ((rest.map (· - 1)).filter (· ≠ 0)).getI j + 1 := by
        have := hunwrap j; rwa [if_pos hj] at this
      have step1 : i + 1 < (a :: rest).getI (j + 1) := by
        rw [List.getI_cons_succ, e1]; omega
      have step2 := (hsc (i + 1) (j + 1)).mp step1
      rw [List.getI_cons_succ] at step2
      by_cases hi : i < ((rest.map (· - 1)).filter (· ≠ 0)).length
      · have e2 : rest.getI i = ((rest.map (· - 1)).filter (· ≠ 0)).getI i + 1 := by
          have := hunwrap i; rwa [if_pos hi] at this
        rw [e2] at step2; omega
      · have e2 := hunwrap i
        rw [if_neg hi] at e2
        rw [e2] at step2
        split_ifs at step2 <;> omega
    · exfalso
      rw [List.getI_eq_default _ (not_lt.mp hj)] at hij
      simp only [show (default : ℕ) = 0 from rfl] at hij
      omega
  have hr'_sc : YoungDiagram.IsSelfConjList ((rest.map (· - 1)).filter (· ≠ 0)) :=
    fun i j => ⟨key i j, key j i⟩
  refine ⟨(rest.map (· - 1)).filter (· ≠ 0), ?_, hr'_pos, hr'_sc,
    hr'_sc.getI_zero_eq_length hr'_pos, by omega, ?_⟩
  · rw [List.sortedGE_iff_pairwise]
    exact (hrest_sorted.pairwise.map (· - 1)
      (fun x y hxy => by omega : ∀ x y, x ≥ y → x - 1 ≥ y - 1)).filter _
  · apply eq_of_getI_eq_of_pos _ hp (wrapHook_pos _ _)
    intro k
    rcases k with _ | m
    · rw [List.getI_cons_zero, wrapHook_getI_zero]; omega
    · rw [List.getI_cons_succ, hunwrap m, wrapHook_getI_succ (hlen_eq ▸ hr'_len_le), hlen_eq]

theorem peelHooks_wrapHook (a : ℕ) (r : List ℕ) (hrp : ∀ x ∈ r, 0 < x) :
    peelHooks (wrapHook a r) = (2 * a + 1) :: peelHooks r := by
  unfold wrapHook
  rw [peelHooks]
  have hcomp : ((· - 1) ∘ (· + 1) : ℕ → ℕ) = id := by ext x; change x + 1 - 1 = x; omega
  have hrfilter : r.filter (· ≠ 0) = r :=
    List.filter_eq_self.mpr (fun x hx => by simp [(hrp x hx).ne'])
  have harg : (((r.map (· + 1) ++ List.replicate (a - r.length) 1)).map (· - 1)).filter
      (· ≠ 0) = r := by
    rw [List.map_append, List.map_map, hcomp, List.map_id, List.map_replicate]
    rw [List.filter_append, hrfilter]
    simp
  rw [harg]
  refine List.cons.injEq .. |>.mpr ⟨by omega, rfl⟩

theorem peelHooks_getI_zero {L : List ℕ} (hL : L ≠ []) :
    (peelHooks L).getI 0 = 2 * (L.getI 0 - 1) + 1 := by
  obtain ⟨a, rest, rfl⟩ := List.exists_cons_of_ne_nil hL
  simp [peelHooks, List.getI_cons_zero]

theorem SortedGT.le_getI_zero {l : List ℕ} (hl : l.SortedGT) {x : ℕ} (hx : x ∈ l) :
    x ≤ l.getI 0 := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  rw [List.getI_eq_getElem l (n := 0) (by omega)]
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · exact le_refl _
  · exact le_of_lt (hl.getElem_gt_getElem_of_lt hipos)

theorem peelHooks_spec (L : List ℕ) (hs : L.SortedGE) (hp : ∀ x ∈ L, 0 < x)
    (hsc : YoungDiagram.IsSelfConjList L) (hg : L.getI 0 = L.length) :
    (peelHooks L).SortedGT ∧ (∀ x ∈ peelHooks L, Odd x) ∧ hookRowLens (peelHooks L) = L := by
  induction hn : L.length using Nat.strong_induction_on generalizing L with
  | _ n ih =>
    subst hn
    rcases eq_or_ne L [] with hL | hL
    · subst hL
      refine ⟨?_, ?_, ?_⟩ <;> simp [peelHooks, hookRowLens, List.sortedGT_iff_pairwise]
    · obtain ⟨r', hr's, hr'p, hr'sc, hr'g, hr'lt, hLeq⟩ := selfConj_decomp_step hL hs hp hsc hg
      obtain ⟨ih1, ih2, ih3⟩ := ih r'.length hr'lt r' hr's hr'p hr'sc hr'g rfl
      rw [hLeq, peelHooks_wrapHook _ _ hr'p]
      refine ⟨?_, ?_, ?_⟩
      · rw [List.sortedGT_iff_pairwise, List.pairwise_cons]
        refine ⟨fun y hy => ?_, ih1.pairwise⟩
        rcases eq_or_ne r' [] with hr'nil | hr'nil
        · simp [hr'nil, peelHooks] at hy
        · have hybound := ih1.le_getI_zero hy
          rw [peelHooks_getI_zero hr'nil, hr'g] at hybound
          have step1 : r'.length < L.length := hr'lt
          have step2 : L.getI 0 = L.length := hg
          have step3 : y ≤ 2 * (r'.length - 1) + 1 := hybound
          have step4 : 0 < r'.length := List.length_pos_of_ne_nil hr'nil
          omega
      · intro x hx
        rw [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ⟨L.getI 0 - 1, rfl⟩
        · exact ih2 x hx
      · change wrapHook (((2 * (L.getI 0 - 1) + 1) - 1) / 2) (hookRowLens (peelHooks r')) =
          wrapHook (L.getI 0 - 1) r'
        rw [ih3, show ((2 * (L.getI 0 - 1) + 1) - 1) / 2 = L.getI 0 - 1 from by omega]

end List

namespace Nat.Partition
open Finset

/-- The finset of those partitions which are their own conjugate. -/
def selfConjugate (n : ℕ) : Finset n.Partition :=
  Finset.univ.filter fun p => p = p.conjugate

theorem card_parity_eq_selfConjugate_card_parity (n : ℕ) :
    #(Finset.univ : Finset n.Partition) % 2 = #(selfConjugate n) % 2 := by
  set e : Equiv.Perm n.Partition := Function.Involutive.toPerm conjugate conjugate_conjugate
    with he_def
  have he2 : e ^ 2 = 1 :=
    Equiv.ext fun x => by simp [pow_two, Equiv.Perm.mul_apply, he_def, conjugate_conjugate]
  have hIsP : IsPGroup 2 (Subgroup.zpowers e) := by
    have hdvd : orderOf e ∣ 2 := orderOf_dvd_of_pow_eq_one he2
    rcases Nat.prime_two.eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h1, pow_one])
  have hfix : MulAction.fixedPoints (Subgroup.zpowers e) n.Partition = ↑(selfConjugate n) := by
    ext x
    simp only [MulAction.mem_fixedPoints, selfConjugate, Finset.coe_filter, Finset.mem_univ,
      true_and, Set.mem_setOf_eq]
    constructor
    · intro h
      have hex := h ⟨e, Subgroup.mem_zpowers e⟩
      rwa [Subgroup.mk_smul, Equiv.Perm.smul_def, he_def, Function.Involutive.coe_toPerm,
        eq_comm] at hex
    · intro hx m
      have hstab : (e : Equiv.Perm n.Partition) ∈ MulAction.stabilizer (Equiv.Perm n.Partition) x :=
        MulAction.mem_stabilizer_iff.mpr (by
          rw [Equiv.Perm.smul_def, he_def, Function.Involutive.coe_toPerm]; exact hx.symm)
      rw [Subgroup.smul_def]
      exact MulAction.mem_stabilizer_iff.mp (Subgroup.zpowers_le.mpr hstab m.2)
  simpa [Nat.ModEq, hfix, Nat.card_coe_set_eq, Set.ncard_coe_finset, Nat.card_eq_fintype_card]
    using hIsP.card_modEq_card_fixedPoints n.Partition

theorem mem_oddDistincts_iff {n : ℕ} (p : n.Partition) : p ∈ oddDistincts n ↔
    (∀ i ∈ p.parts, Odd i) ∧ p.parts.Nodup := by
  simp only [oddDistincts, Finset.mem_inter, odds, restricted, distincts, Finset.mem_filter,
    Finset.mem_univ, true_and, ← Nat.not_even_iff_odd]

theorem sort_sortedGT_of_mem_oddDistincts {n : ℕ} {p : n.Partition} (hp : p ∈ oddDistincts n) :
    (p.parts.sort (· ≥ ·)).SortedGT := by
  obtain ⟨-, hnodup⟩ := (mem_oddDistincts_iff p).mp hp
  have hsE : (p.parts.sort (· ≥ ·)).SortedGE := List.Pairwise.sortedGE (Multiset.pairwise_sort _ _)
  have hLnodup : (p.parts.sort (· ≥ ·)).Nodup := by
    rw [← Multiset.coe_nodup, Multiset.sort_eq]; exact hnodup
  exact hsE.sortedGT_of_nodup hLnodup

theorem sort_odd_of_mem_oddDistincts {n : ℕ} {p : n.Partition} (hp : p ∈ oddDistincts n) :
    ∀ x ∈ p.parts.sort (· ≥ ·), Odd x := by
  obtain ⟨hodd, -⟩ := (mem_oddDistincts_iff p).mp hp
  exact fun x hx => hodd x (Multiset.mem_sort _ |>.mp hx)

theorem hookRowLens_sort_card {n : ℕ} {p : n.Partition} (hp : p ∈ oddDistincts n) :
    (YoungDiagram.ofRowLens (List.hookRowLens (p.parts.sort (· ≥ ·)))
      (List.hookRowLens_spec _ (sort_sortedGT_of_mem_oddDistincts hp)
        (sort_odd_of_mem_oddDistincts hp)).1).card = n := by
  rw [← YoungDiagram.sum_rowLens_eq_card,
    YoungDiagram.rowLens_ofRowLens_eq_self
      (List.hookRowLens_spec _ (sort_sortedGT_of_mem_oddDistincts hp)
        (sort_odd_of_mem_oddDistincts hp)).2.1,
    (List.hookRowLens_spec _ (sort_sortedGT_of_mem_oddDistincts hp)
      (sort_odd_of_mem_oddDistincts hp)).2.2.2.1, ← Multiset.sum_coe, Multiset.sort_eq]
  exact p.parts_sum

theorem sort_sortedGE_of_mem_selfConjugate {n : ℕ} {q : n.Partition} (_hq : q ∈ selfConjugate n) :
    (q.parts.sort (· ≥ ·)).SortedGE := List.Pairwise.sortedGE (Multiset.pairwise_sort _ _)

theorem sort_pos_of_mem_selfConjugate {n : ℕ} {q : n.Partition} (_hq : q ∈ selfConjugate n) :
    ∀ x ∈ q.parts.sort (· ≥ ·), 0 < x := fun _x hx =>
  q.parts_pos (Multiset.mem_sort _ |>.mp hx)

theorem sort_selfConjList_of_mem_selfConjugate {n : ℕ} {q : n.Partition}
    (hq : q ∈ selfConjugate n) : YoungDiagram.IsSelfConjList (q.parts.sort (· ≥ ·)) := by
  simp only [selfConjugate, Finset.mem_filter, Finset.mem_univ, true_and] at hq
  apply YoungDiagram.transpose_ofRowLens_eq_self_iff.mp
  show (YoungDiagram.ofPartition q).transpose = YoungDiagram.ofPartition q
  have : YoungDiagram.ofPartition q = (YoungDiagram.ofPartition q).transpose := by
    conv_lhs => rw [hq]
    exact YoungDiagram.ofPartition_toPartition _
  exact this.symm

theorem sort_getI_zero_eq_length_of_mem_selfConjugate {n : ℕ} {q : n.Partition}
    (hq : q ∈ selfConjugate n) :
    (q.parts.sort (· ≥ ·)).getI 0 = (q.parts.sort (· ≥ ·)).length :=
  (sort_selfConjList_of_mem_selfConjugate hq).getI_zero_eq_length
    (sort_pos_of_mem_selfConjugate hq)

theorem peelHooks_sort_sum {n : ℕ} {q : n.Partition} (hq : q ∈ selfConjugate n) :
    (List.peelHooks (q.parts.sort (· ≥ ·))).sum = n := by
  have hspec := List.peelHooks_spec _ (sort_sortedGE_of_mem_selfConjugate hq)
    (sort_pos_of_mem_selfConjugate hq) (sort_selfConjList_of_mem_selfConjugate hq)
    (sort_getI_zero_eq_length_of_mem_selfConjugate hq)
  have hsum := (List.hookRowLens_spec _ hspec.1 hspec.2.1).2.2.2.1
  rw [hspec.2.2] at hsum
  rw [← hsum]
  exact (Multiset.sum_coe _).symm.trans (by rw [Multiset.sort_eq]; exact q.parts_sum)

/-- The forward direction of the bijection: fold the diagram of an odd-distinct partition
along its diagonal to obtain a self-conjugate partition of the same size. -/
noncomputable def toSelfConj {n : ℕ} (p : n.Partition) (hp : p ∈ oddDistincts n) : n.Partition :=
  (YoungDiagram.ofRowLens (List.hookRowLens (p.parts.sort (· ≥ ·)))
    (List.hookRowLens_spec _ (sort_sortedGT_of_mem_oddDistincts hp)
      (sort_odd_of_mem_oddDistincts hp)).1).toPartition (hookRowLens_sort_card hp)

theorem ofPartition_toSelfConj {n : ℕ} {p : n.Partition} (hp : p ∈ oddDistincts n) :
    YoungDiagram.ofPartition (toSelfConj p hp) =
      YoungDiagram.ofRowLens (List.hookRowLens (p.parts.sort (· ≥ ·)))
        (List.hookRowLens_spec _ (sort_sortedGT_of_mem_oddDistincts hp)
          (sort_odd_of_mem_oddDistincts hp)).1 :=
  YoungDiagram.ofPartition_toPartition _

theorem toSelfConj_parts {n : ℕ} {p : n.Partition} (hp : p ∈ oddDistincts n) :
    (toSelfConj p hp).parts = (List.hookRowLens (p.parts.sort (· ≥ ·)) : Multiset ℕ) := by
  change (↑(YoungDiagram.ofRowLens (List.hookRowLens (p.parts.sort (· ≥ ·)))
    (List.hookRowLens_spec _ (sort_sortedGT_of_mem_oddDistincts hp)
      (sort_odd_of_mem_oddDistincts hp)).1).rowLens : Multiset ℕ) = _
  rw [YoungDiagram.rowLens_ofRowLens_eq_self
    (List.hookRowLens_spec _ (sort_sortedGT_of_mem_oddDistincts hp)
      (sort_odd_of_mem_oddDistincts hp)).2.1]

theorem toSelfConj_parts_sort {n : ℕ} {p : n.Partition} (hp : p ∈ oddDistincts n) :
    (toSelfConj p hp).parts.sort (· ≥ ·) = List.hookRowLens (p.parts.sort (· ≥ ·)) := by
  rw [toSelfConj_parts]
  exact List.mergeSort_eq_self _
    (List.hookRowLens_spec _ (sort_sortedGT_of_mem_oddDistincts hp)
      (sort_odd_of_mem_oddDistincts hp)).1.pairwise

theorem toSelfConj_mem {n : ℕ} {p : n.Partition} (hp : p ∈ oddDistincts n) :
    toSelfConj p hp ∈ selfConjugate n := by
  simp only [selfConjugate, Finset.mem_filter, Finset.mem_univ, true_and]
  have hself : (YoungDiagram.ofPartition (toSelfConj p hp)).transpose =
      YoungDiagram.ofPartition (toSelfConj p hp) := by
    rw [ofPartition_toSelfConj]
    exact YoungDiagram.transpose_ofRowLens_eq_self_iff.mpr
      (List.hookRowLens_spec _ (sort_sortedGT_of_mem_oddDistincts hp)
        (sort_odd_of_mem_oddDistincts hp)).2.2.2.2
  change toSelfConj p hp = conjugate (toSelfConj p hp)
  apply Nat.Partition.ext
  show (toSelfConj p hp).parts = (conjugate (toSelfConj p hp)).parts
  calc (toSelfConj p hp).parts
      = (YoungDiagram.ofRowLens (List.hookRowLens (p.parts.sort (· ≥ ·)))
          (List.hookRowLens_spec _ (sort_sortedGT_of_mem_oddDistincts hp)
            (sort_odd_of_mem_oddDistincts hp)).1).rowLens := rfl
    _ = (YoungDiagram.ofPartition (toSelfConj p hp)).rowLens := by rw [ofPartition_toSelfConj]
    _ = (YoungDiagram.ofPartition (toSelfConj p hp)).transpose.rowLens := by rw [hself]
    _ = (conjugate (toSelfConj p hp)).parts := rfl

/-- The backward direction of the bijection: peel the outer diagonal hooks off a
self-conjugate partition to recover an odd-distinct partition of the same size. -/
def fromSelfConj {n : ℕ} (q : n.Partition) (hq : q ∈ selfConjugate n) : n.Partition where
  parts := (List.peelHooks (q.parts.sort (· ≥ ·)) : Multiset ℕ)
  parts_pos {x} hx := by
    have hspec := List.peelHooks_spec _ (sort_sortedGE_of_mem_selfConjugate hq)
      (sort_pos_of_mem_selfConjugate hq) (sort_selfConjList_of_mem_selfConjugate hq)
      (sort_getI_zero_eq_length_of_mem_selfConjugate hq)
    exact (hspec.2.1 x (by simpa using hx)).pos
  parts_sum := peelHooks_sort_sum hq

theorem fromSelfConj_mem {n : ℕ} {q : n.Partition} (hq : q ∈ selfConjugate n) :
    fromSelfConj q hq ∈ oddDistincts n := by
  rw [mem_oddDistincts_iff]
  have hspec := List.peelHooks_spec _ (sort_sortedGE_of_mem_selfConjugate hq)
    (sort_pos_of_mem_selfConjugate hq) (sort_selfConjList_of_mem_selfConjugate hq)
    (sort_getI_zero_eq_length_of_mem_selfConjugate hq)
  refine ⟨fun i hi => hspec.2.1 i hi, ?_⟩
  change (↑(List.peelHooks (q.parts.sort (· ≥ ·))) : Multiset ℕ).Nodup
  rw [Multiset.coe_nodup]
  exact hspec.1.nodup

theorem fromSelfConj_parts_sort {n : ℕ} {q : n.Partition} (hq : q ∈ selfConjugate n) :
    (fromSelfConj q hq).parts.sort (· ≥ ·) = List.peelHooks (q.parts.sort (· ≥ ·)) := by
  change (↑(List.peelHooks (q.parts.sort (· ≥ ·))) : Multiset ℕ).sort (· ≥ ·) = _
  exact List.mergeSort_eq_self _ ((List.peelHooks_spec _ (sort_sortedGE_of_mem_selfConjugate hq)
    (sort_pos_of_mem_selfConjugate hq) (sort_selfConjList_of_mem_selfConjugate hq)
    (sort_getI_zero_eq_length_of_mem_selfConjugate hq)).1.pairwise.imp le_of_lt)

theorem fromSelfConj_toSelfConj {n : ℕ} {p : n.Partition} (hp : p ∈ oddDistincts n) :
    fromSelfConj (toSelfConj p hp) (toSelfConj_mem hp) = p := by
  apply Nat.Partition.ext
  change (List.peelHooks ((toSelfConj p hp).parts.sort (· ≥ ·)) : Multiset ℕ) = p.parts
  rw [toSelfConj_parts_sort hp, List.peelHooks_hookRowLens _
    (sort_sortedGT_of_mem_oddDistincts hp) (sort_odd_of_mem_oddDistincts hp), Multiset.sort_eq]

theorem toSelfConj_fromSelfConj {n : ℕ} {q : n.Partition} (hq : q ∈ selfConjugate n) :
    toSelfConj (fromSelfConj q hq) (fromSelfConj_mem hq) = q := by
  apply Nat.Partition.ext
  rw [toSelfConj_parts]
  show (↑(List.hookRowLens ((fromSelfConj q hq).parts.sort (· ≥ ·))) : Multiset ℕ) = q.parts
  have hspec := List.peelHooks_spec _ (sort_sortedGE_of_mem_selfConjugate hq)
    (sort_pos_of_mem_selfConjugate hq) (sort_selfConjList_of_mem_selfConjugate hq)
    (sort_getI_zero_eq_length_of_mem_selfConjugate hq)
  rw [fromSelfConj_parts_sort hq]
  rw [hspec.2.2, Multiset.sort_eq]

/-- The bijection between partitions of `n` into distinct odd parts and self-conjugate
partitions of `n`, given explicitly by folding (resp. unfolding) the Young diagram along its
main diagonal, one hook at a time. -/
noncomputable def selfConjEquivOddDistinct (n : ℕ) : ↥(oddDistincts n) ≃ ↥(selfConjugate n) where
  toFun p := ⟨toSelfConj p.1 p.2, toSelfConj_mem p.2⟩
  invFun q := ⟨fromSelfConj q.1 q.2, fromSelfConj_mem q.2⟩
  left_inv p := Subtype.ext (fromSelfConj_toSelfConj p.2)
  right_inv q := Subtype.ext (toSelfConj_fromSelfConj q.2)

theorem card_selfConjugate_eq_card_oddDistincts (n : ℕ) :
    #(selfConjugate n) = #(oddDistincts n) := by
  rw [← Fintype.card_coe (selfConjugate n), ← Fintype.card_coe (oddDistincts n)]
  exact (Fintype.card_congr (selfConjEquivOddDistinct n)).symm

end Nat.Partition
