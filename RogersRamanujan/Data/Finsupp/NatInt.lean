module

public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Order.Preorder.Finsupp

/-! # `Finsupp` valued in `ℕ` or `ℤ`
-/

@[expose] public section

namespace Finsupp
variable (σ : Type*)

/-- The additive monoid hom from `σ →₀ ℕ` to `σ →₀ ℤ` given by casting each coefficient. -/
noncomputable def natInt : (σ →₀ ℕ) →+ (σ →₀ ℤ) where
  toFun n := n.mapRange (↑) rfl
  map_zero' := ext fun _ ↦ rfl
  map_add' _ _ := mapRange_add (fun _ _ ↦ rfl) _ _

/-- The zero-preserving map from `σ →₀ ℤ` to `σ →₀ ℕ` given by `Int.toNat` on each coefficient. -/
noncomputable def intNat : ZeroHom (σ →₀ ℤ) (σ →₀ ℕ) where
  toFun n := n.mapRange Int.toNat rfl
  map_zero' := ext fun _ ↦ rfl

variable {σ}

@[simp] theorem natInt_apply (f : σ →₀ ℕ) (i : σ) : f.natInt σ i = f i := rfl
@[simp] theorem intNat_apply (f : σ →₀ ℤ) (i : σ) : f.intNat σ i = (f i).toNat := rfl

@[simp] theorem natInt_intNat (f : σ →₀ ℤ) (hf : 0 ≤ f) : natInt σ (intNat σ f) = f :=
  ext fun i ↦ by simpa using hf i

@[simp] theorem intNat_natInt (f : σ →₀ ℕ) : intNat σ (natInt σ f) = f := ext fun i ↦ by simp

@[simp] theorem intNat_add {f g : σ →₀ ℤ} (hf : 0 ≤ f) (hg : 0 ≤ g) :
    intNat σ (f + g) = intNat σ f + intNat σ g :=
  ext fun i ↦ Int.toNat_add (hf i) (hg i)

instance : CanLift (σ →₀ ℤ) (σ →₀ ℕ) (natInt σ) (0 ≤ ·) where
  prf f hf := ⟨f.intNat _, f.natInt_intNat hf⟩

@[simp] theorem natInt_nonneg (f : σ →₀ ℕ) : 0 ≤ f.natInt σ := fun _ ↦ Int.natCast_nonneg _

theorem natInt_injective : Function.Injective (natInt σ) :=
  Function.LeftInverse.injective intNat_natInt

@[simp] theorem natInt_inj {f g : σ →₀ ℕ} : f.natInt σ = g.natInt σ ↔ f = g :=
  natInt_injective.eq_iff

@[simp] theorem natInt_eq_zero_iff (f : σ →₀ ℕ) : f.natInt σ = 0 ↔ f = 0 := by simp [← natInt_inj]

@[simp] theorem natInt_single (i : σ) (n : ℕ) : (single i n).natInt σ = single i (n : ℤ) := by
  ext
  classical simp [single_apply]

@[simp] theorem intNat_single (i : σ) (n : ℤ) : (single i n).intNat σ = single i n.toNat := by
  ext
  classical simp +contextual [single_apply, apply_ite]

end Finsupp
