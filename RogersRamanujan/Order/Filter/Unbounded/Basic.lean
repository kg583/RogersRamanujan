module

import RogersRamanujan.Data.Nat.Choose.Basic
import RogersRamanujan.Topology.Instances.Int
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Tactic.Continuity
import Mathlib.Topology.MetricSpace.Bounded

/-! # Filter.Unbounded

A function `n : α → β` is *unbounded* if `n` tends to `∞` along the cofinite filter. For
`β = ℕ`, this means `n(a) → ∞` as `a` ranges over all but finitely many elements, which is the
condition that ensures `∑ f a * q ^ n a` is summable in a power series ring with discrete topology.
-/

@[expose] public section

open Filter

/-- A function `n : α → β` is unbounded if `n(a) → ∞` as `a` ranges over cofinitely many
elements. -/
def Filter.Unbounded {α β : Type*} [Preorder β] (n : α → β) : Prop :=
  Tendsto n cofinite atTop

namespace Filter.Unbounded

@[grind .]
protected theorem id : Unbounded (· : ℕ → ℕ) := by
  rw [Unbounded, Nat.cofinite_eq_atTop]; exact tendsto_id

theorem comp_atTop {α β γ : Type*} [Preorder β] [Preorder γ] {m : β → γ} {n : α → β}
    (hm : Tendsto m atTop atTop) (hn : Unbounded n) : Unbounded (m ∘ n) := hm.comp hn

@[grind .]
protected theorem comp {α : Type*} {m : ℕ → ℕ} {n : α → ℕ}
    (hm : Unbounded m) (hn : Unbounded n) : Unbounded (m ∘ n) :=
  comp_atTop (by rwa [Unbounded, Nat.cofinite_eq_atTop] at hm) hn

theorem of_injective {α : Type*} {f : α → ℕ} (hf : Function.Injective f) : Unbounded f := by
  rw [Unbounded, ← Nat.cofinite_eq_atTop]
  exact hf.tendsto_cofinite

theorem comp_injective {α β γ : Type*} [Preorder β] {n : α → β} (h : Unbounded n)
    {f : γ → α} (hf : Function.Injective f) : Unbounded (n ∘ f) :=
  Tendsto.comp h hf.tendsto_cofinite

/-- `n : α → ℕ` is unbounded if and only if `n` tends to `∞` along the cofinite filter. -/
@[grind =]
theorem nat_def {α : Type*} {n : α → ℕ} : Unbounded n ↔ Tendsto n cofinite atTop := Iff.rfl

/-- `f : ℤ → β` is unbounded if and only if `f` is unbounded on both `n : ℕ` and `-(n : ℕ)`. -/
@[grind =]
theorem int_domain_def {β : Type*} [Preorder β] {f : ℤ → β} :
    Unbounded f ↔ Unbounded (fun n : ℕ ↦ f n) ∧ Unbounded (fun n : ℕ ↦ f (-n)) := by
  unfold Unbounded
  rw [Int.tendsto_cofinite_iff, Nat.cofinite_eq_atTop]

theorem mono {α β : Type*} [Preorder β] {n m : α → β}
    (h : Unbounded n) (hle : ∀ a, n a ≤ m a) : Unbounded m := tendsto_atTop_mono hle h

theorem tendsto_prodMap_cofinite_cofinite {α β : Type*}
    {m : α → ℕ} {n : β → ℕ} (hm : Unbounded m) (hn : Unbounded n) :
    Tendsto (Prod.map m n) cofinite cofinite := by
  simpa [← coprod_cofinite, Nat.cofinite_eq_atTop] using hm.prodMap_coprod hn

@[grind =] theorem comp_subtypeVal_iff {α β : Type*} [Preorder β] {n : α → β} {s : Set α} :
    Unbounded (n ∘ Subtype.val (p := s)) ↔ ∀ y, {x | x ∈ s ∧ ¬y ≤ n x}.Finite := by
  rw [Unbounded, ← tendsto_map'_iff, tendsto_atTop]
  simp [← Set.finite_image_iff Subtype.val_injective.injOn, Subtype.coe_image,
    show ∀ x, s x = (x ∈ s) by intro; rfl]

section Nat

theorem pow {k : ℕ} (hk : k ≠ 0) : Unbounded (· ^ k : ℕ → ℕ) := mono .id <| Nat.le_self_pow hk

@[grind .]
theorem sq : Unbounded (· ^ 2 : ℕ → ℕ) := pow <| by grind

@[grind .]
theorem natAdd : Unbounded fun n : ℕ × ℕ ↦ n.1 + n.2 := by
  rw [Unbounded, ← coprod_cofinite, Nat.cofinite_eq_atTop, Filter.coprod, tendsto_sup]
  exact ⟨tendsto_atTop_mono (by grind) tendsto_comap, tendsto_atTop_mono (by grind) tendsto_comap⟩

@[grind .]
theorem add {α β : Type*} {p : α → ℕ} {q : β → ℕ} (hp : Unbounded p) (hq : Unbounded q) :
    Unbounded fun i : α × β ↦ p i.1 + q i.2 :=
  Tendsto.comp natAdd <| hp.tendsto_prodMap_cofinite_cofinite hq

theorem choose {r : ℕ} (hr : r ≠ 0) : Unbounded (Nat.choose · r) := by
  rw [Unbounded, Nat.cofinite_eq_atTop]
  exact Nat.tendsto_choose_atTop_atTop hr

@[grind .]
theorem choose_two : Unbounded (Nat.choose · 2) := choose <| by grind

theorem choose_two' : Unbounded fun k : ℕ ↦ k * (k - 1) / 2 := by
  simp_rw [← Nat.choose_two_right]
  exact choose_two

/-- `(m + k)² + k` is unbounded on `ℕ × ℕ`. Restriction of `natAbsSq_add_snd` to `ℕ`. -/
theorem add_sq_add_snd : Unbounded fun p : ℕ × ℕ ↦ (p.1 + p.2) ^ 2 + p.2 :=
  mono (sq.comp natAdd) (by simp)

/-- `(m + k)² + m` is unbounded on `ℕ × ℕ`. -/
theorem add_sq_add_fst : Unbounded fun p : ℕ × ℕ ↦ (p.1 + p.2) ^ 2 + p.1 :=
  mono (sq.comp natAdd) (by simp)

/-- `(k + m)² + k` is unbounded on `ℕ × ℕ`. -/
theorem add_rev_sq_add_snd : Unbounded fun p : ℕ × ℕ ↦ (p.2 + p.1) ^ 2 + p.2 := by
  convert add_sq_add_snd using 4; ring

/-- `m ↦ m * (m + 1) / 2` is unbounded on `ℕ`. -/
theorem triangular : Unbounded fun m : ℕ ↦ m * (m + 1) / 2 :=
  mono choose_two fun n ↦ n.choose_succ_two' ▸ Nat.choose_mono _ n.le_succ

end Nat

section IntNat

@[grind .]
theorem natAbs : Unbounded fun m : ℤ ↦ m.natAbs := Int.tendsto_natAbs_cofinite_atTop

@[grind .]
theorem natAbs_sq : Unbounded fun m : ℤ ↦ m.natAbs ^ 2 := sq.comp natAbs

/-- `(m, k) ↦ (m + k).natAbs² + k` is unbounded on `ℤ × ℕ`. -/
@[grind .]
theorem natAbs_add_sq_add_snd : Unbounded fun p : ℤ × ℕ ↦ (p.1 + p.2).natAbs ^ 2 + p.2 :=
  (add natAbs_sq .id).comp_injective (f := fun p : ℤ × ℕ ↦ (p.1 + p.2, p.2)) fun _ ↦ by grind

/-- `(k, m) ↦ (k + m).natAbs² + k` is unbounded on `ℤ × ℕ`. -/
@[grind .]
theorem natAbs_add_rev_sq_add_snd :
    Unbounded fun p : ℤ × ℕ ↦ (p.2 + p.1).natAbs ^ 2 + p.2 := by
  convert natAbs_add_sq_add_snd using 5; abel

/-- `k ↦ (k + m).natAbs² + k` is unbounded in `k : ℕ` for fixed `m : ℤ`. -/
theorem natAbs_add_const_sq_add (m : ℤ) :
    Unbounded fun k : ℕ ↦ (k + m).natAbs ^ 2 + k := mono .id <| by grind

/-- `m ↦ (m * (m - 1) / 2).toNat` is unbounded on `ℤ`. -/
@[grind .]
theorem int_triangular : Unbounded fun m : ℤ ↦ (m * (m - 1) / 2).toNat := by
  have key₁ (n : ℕ) : (↑n * (↑n - 1) / 2 : ℤ).toNat = n * (n - 1) / 2 := by grind
  have key₂ (n : ℕ) : (-↑n * (-↑n - 1) / 2 : ℤ).toNat = n * (n + 1) / 2 := by
    rw [show (_ * _) = n * (n + 1) by ring]
    grind
  simp_rw [int_domain_def, key₁, key₂]
  exact ⟨choose_two', triangular⟩

/-- `m ↦ m.natAbs * (m.natAbs - 1) / 2` is unbounded on `ℤ`. -/
@[grind .]
theorem natAbs_triangular : Unbounded fun m : ℤ ↦ m.natAbs * (m.natAbs - 1) / 2 :=
  choose_two'.comp natAbs

end IntNat

end Filter.Unbounded
