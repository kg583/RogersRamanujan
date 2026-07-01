module

public import Mathlib.Topology.Algebra.Nonarchimedean.Bases

/-! # Nonarchimedean topology from a subgroup basis
-/

@[expose] public section

open scoped Pointwise
open Filter Topology

namespace AddGroupFilterBasis

@[simp] theorem mem_toFilterBasis {A : Type*} [AddGroup A]
    {i : AddGroupFilterBasis A} {x : Set A} : x ∈ i.toFilterBasis ↔ x ∈ i := Iff.rfl

end AddGroupFilterBasis

namespace RingFilterBasis

@[simp] theorem mem_toAddGroupFilterBasis {A : Type*} [Ring A]
    {i : RingFilterBasis A} {x : Set A} : x ∈ i.toAddGroupFilterBasis ↔ x ∈ i := Iff.rfl

end RingFilterBasis

namespace RingSubgroupsBasis

@[simp] theorem mem_toRingFilterBasis {A ι : Type*} [Ring A] [Nonempty ι]
    {B : ι → AddSubgroup A} {i : RingSubgroupsBasis B} {x : Set A} :
    x ∈ i.toRingFilterBasis ↔ ∃ n, x = B n := Iff.rfl

end RingSubgroupsBasis

/-- A `BoundedRingSubgroupsBasis` is a family of additive subgroups forming a ring topology
basis with the bounded cross-multiplication property: for any `B k` and target `B i`, there
exists `B j` with `B k * B j ⊆ B i`. This implies the `mul` field of `RingSubgroupsBasis`
(take `k = j` via `inter`), so the structure does not extend `RingSubgroupsBasis`. -/
structure BoundedRingSubgroupsBasis {A ι : Type*} [Ring A] (B : ι → AddSubgroup A) : Prop where
  inter (i j) : ∃ k, B k ≤ B i ⊓ B j
  mul_bounded_left (k i) : ∃ j, (B k : Set A) * B j ⊆ B i
  mul_bounded_right (k i) : ∃ j, (B j : Set A) * B k ⊆ B i
  leftMul (x i) : ∃ j, (B j : Set A) ⊆ (x * ·) ⁻¹' B i
  rightMul (x i) : ∃ j, (B j : Set A) ⊆ (· * x) ⁻¹' B i

namespace BoundedRingSubgroupsBasis

variable {A ι : Type*} [Ring A] {B : ι → AddSubgroup A}

theorem mul (hB : BoundedRingSubgroupsBasis B) :
    ∀ i, ∃ j, (B j : Set A) * B j ⊆ B i := fun i ↦ by
  obtain ⟨j, hj⟩ := hB.mul_bounded_left i i
  obtain ⟨m, hm⟩ := hB.inter i j
  exact ⟨m, (Set.mul_subset_mul (show (B m : Set A) ⊆ B i from le_inf_iff.mp hm |>.1)
    (show (B m : Set A) ⊆ B j from le_inf_iff.mp hm |>.2)).trans hj⟩

theorem toRingSubgroupsBasis (hB : BoundedRingSubgroupsBasis B) :
    RingSubgroupsBasis B where
  inter := hB.inter
  mul := hB.mul
  leftMul := hB.leftMul
  rightMul := hB.rightMul

/-- Build a `BoundedRingSubgroupsBasis` for a commutative ring. The `rightMul` field is
derived from `leftMul` by commutativity. -/
theorem of_comm {A ι : Type*} [CommRing A] {B : ι → AddSubgroup A}
    (inter : ∀ i j, ∃ k, B k ≤ B i ⊓ B j)
    (mul_bounded : ∀ k i, ∃ j, (B k : Set A) * B j ⊆ B i)
    (leftMul : ∀ x : A, ∀ i, ∃ j, (B j : Set A) ⊆ (x * ·) ⁻¹' B i) :
    BoundedRingSubgroupsBasis B where
  inter := inter
  mul_bounded_left := mul_bounded
  mul_bounded_right k i := by simpa [mul_comm] using mul_bounded k i
  leftMul := leftMul
  rightMul x i := by simpa [mul_comm] using leftMul x i

theorem of_covers {A ι : Type*} [Ring A] {B : ι → AddSubgroup A}
    (inter : ∀ i j, ∃ k, B k ≤ B i ⊓ B j)
    (mul_bounded_left : ∀ k i, ∃ j, (B k : Set A) * B j ⊆ B i)
    (mul_bounded_right : ∀ k i, ∃ j, (B j : Set A) * B k ⊆ B i)
    (covers : ∀ x : A, ∃ k, x ∈ B k) :
    BoundedRingSubgroupsBasis B where
  inter := inter
  mul_bounded_left := mul_bounded_left
  mul_bounded_right := mul_bounded_right
  leftMul x i := by
    obtain ⟨k, hk⟩ := covers x
    obtain ⟨j, hj⟩ := mul_bounded_left k i
    exact ⟨j, fun _ hy ↦ hj <| Set.mul_mem_mul hk hy⟩
  rightMul x i := by
    obtain ⟨k, hk⟩ := covers x
    obtain ⟨j, hj⟩ := mul_bounded_right k i
    exact ⟨j, fun _ hy ↦ hj <| Set.mul_mem_mul hy hk⟩

/-- Build a `BoundedRingSubgroupsBasis` for a commutative ring when every element is in some
basis element (`covers`). In this case `leftMul` is derivable from `mul_bounded`. -/
theorem of_comm_covers {A ι : Type*} [CommRing A] {B : ι → AddSubgroup A}
    (inter : ∀ i j, ∃ k, B k ≤ B i ⊓ B j)
    (mul_bounded : ∀ k i, ∃ j, (B k : Set A) * B j ⊆ B i)
    (covers : ∀ x : A, ∃ k, x ∈ B k) :
    BoundedRingSubgroupsBasis B :=
  .of_comm inter mul_bounded fun x i => by
    obtain ⟨k, hk⟩ := covers x
    obtain ⟨j, hj⟩ := mul_bounded k i
    exact ⟨j, fun _ hy ↦ hj <| Set.mul_mem_mul hk hy⟩

end BoundedRingSubgroupsBasis
