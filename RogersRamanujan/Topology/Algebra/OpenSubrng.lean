module

public import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Open non-unital subrings

`OpenSubrng R` is the type of open non-unital subrings of a topological (non-unital) ring `R`,
i.e. a `NonUnitalSubring R` whose carrier is open. It is the non-unital-subring analogue of
`OpenAddSubgroup`, and is used to phrase neighbourhood bases of `0` in strongly nonarchimedean
rings: an open non-unital subring bundles "open", "contains `0`", and "closed under
multiplication" (`V * V ⊆ V`) into a single object.
-/

@[expose] public section

open scoped Topology

/-- The type of open non-unital subrings of a topological (non-unital) ring. -/
structure OpenSubrng (R : Type*) [NonUnitalNonAssocRing R] [TopologicalSpace R] extends
    NonUnitalSubring R where
  isOpen' : IsOpen carrier

/-- Reinterpret an `OpenSubrng` as a `NonUnitalSubring`. -/
add_decl_doc OpenSubrng.toNonUnitalSubring

attribute [coe] OpenSubrng.toNonUnitalSubring

namespace OpenSubrng

variable {R : Type*} [NonUnitalNonAssocRing R] [TopologicalSpace R]
variable {U V : OpenSubrng R} {g : R}

instance hasCoeNonUnitalSubring : CoeTC (OpenSubrng R) (NonUnitalSubring R) := ⟨toNonUnitalSubring⟩

theorem toNonUnitalSubring_injective :
    Function.Injective ((↑) : OpenSubrng R → NonUnitalSubring R)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

instance : SetLike (OpenSubrng R) R where
  coe U := U.1
  coe_injective _ _ h := toNonUnitalSubring_injective <| SetLike.ext' h

instance : NonUnitalSubringClass (OpenSubrng R) R where
  add_mem := add_mem (S := NonUnitalSubring R)
  zero_mem U := zero_mem (S := NonUnitalSubring R) U.toNonUnitalSubring
  mul_mem := mul_mem (S := NonUnitalSubring R)
  neg_mem := neg_mem (S := NonUnitalSubring R)

instance : PartialOrder (OpenSubrng R) := .ofSetLike (OpenSubrng R) R

@[simp, norm_cast] theorem coe_toNonUnitalSubring : ((U : NonUnitalSubring R) : Set R) = U := rfl

@[simp, norm_cast] theorem mem_toNonUnitalSubring : g ∈ (U : NonUnitalSubring R) ↔ g ∈ U := Iff.rfl

@[ext] theorem ext (h : ∀ x, x ∈ U ↔ x ∈ V) : U = V := SetLike.ext h

/-- Reinterpret an `OpenSubrng` as an `OpenAddSubgroup`. -/
def toOpenAddSubgroup (U : OpenSubrng R) : OpenAddSubgroup R where
  toAddSubgroup := U.toNonUnitalSubring.toAddSubgroup
  isOpen' := U.isOpen'

@[simp]
theorem coe_toOpenAddSubgroup : (U.toOpenAddSubgroup : Set R) = U := rfl

variable (U)

protected theorem isOpen : IsOpen (U : Set R) := U.isOpen'

theorem mem_nhds_zero : (U : Set R) ∈ 𝓝 (0 : R) := U.isOpen.mem_nhds U.zero_mem

protected theorem isClosed [SeparatelyContinuousAdd R] : IsClosed (U : Set R) :=
  U.toOpenAddSubgroup.isClosed

variable {U}

@[simp] theorem coe_mk (s : NonUnitalSubring R) (h) : ((⟨s, h⟩ : OpenSubrng R) : Set R) = s := rfl

/-- A version of `Set.pi` for `OpenSubrng`. Given a finite index set `I` and a family of open
non-unital subrings `s : Π i, OpenSubrng (R i)`, `pi hI s` is the open non-unital subring of
dependent functions `f` such that `f i` belongs to `s i` whenever `i ∈ I`. -/
def pi {ι : Type*} {R : ι → Type*}
    [∀ i, NonUnitalNonAssocRing (R i)] [∀ i, TopologicalSpace (R i)]
    {I : Set ι} (hI : I.Finite) (s : ∀ i, OpenSubrng (R i)) :
    OpenSubrng ((i : ι) → R i) where
  carrier := I.pi fun i ↦ s i
  zero_mem' _ _ := zero_mem _
  add_mem' ha hb i hi := add_mem (ha i hi) (hb i hi)
  neg_mem' ha i hi := neg_mem (ha i hi)
  mul_mem' ha hb i hi := mul_mem (ha i hi) (hb i hi)
  isOpen' := isOpen_set_pi hI fun i _ ↦ (s i).isOpen

@[simp] theorem coe_pi {ι : Type*} {R : ι → Type*}
    [∀ i, NonUnitalNonAssocRing (R i)] [∀ i, TopologicalSpace (R i)]
    {I : Set ι} (hI : I.Finite) (s : ∀ i, OpenSubrng (R i)) :
    (pi hI s : Set ((i : ι) → R i)) = I.pi fun i ↦ s i := rfl

end OpenSubrng
