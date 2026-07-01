module

public import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Open subgroups

Construction of `OpenAddSubgroup.pi` and basic coercion lemmas.
-/

@[expose] public section

@[simp] theorem AddSubsemigroup.carrier_eq_coe {A : Type*} [Add A] {S : AddSubsemigroup A} :
    S.carrier = S := rfl

@[simp] theorem AddSubmonoid.coe_toAddSubsemigroup_eq_coe
    {A : Type*} [AddZeroClass A] {S : AddSubmonoid A} :
    (S.toAddSubsemigroup : Set A) = S := rfl

attribute [simp] OpenAddSubgroup.isOpen

@[simp] theorem OpenAddSubgroup.coe_mk
    {G : Type*} [AddGroup G] [TopologicalSpace G] {U : AddSubgroup G} (hU : IsOpen (U : Set G)) :
    ((⟨U, hU⟩ : OpenAddSubgroup G) : Set G) = U := rfl

/-- A version of `Set.pi` for `OpenAddSubgroup`. Given a finite index set `I` and a family of open
subgroup `s : Π i, OpenAddSubgroup f i`, `pi I s` is the `OpenAddSubgroup` of dependent functions
`f : Π i, f i` such that `f i` belongs to `pi I s` whenever `i ∈ I`. -/
def OpenAddSubgroup.pi {ι : Type*} {R : ι → Type*}
    [∀ i, AddGroup (R i)] [∀ i, TopologicalSpace (R i)]
    {I : Set ι} (hI : I.Finite) (s : ∀ i, OpenAddSubgroup (R i)) :
    OpenAddSubgroup ((i : ι) → R i) where
  toAddSubgroup := .pi I (s ·)
  isOpen' := isOpen_set_pi hI fun i _ ↦ (s i).isOpen

@[simp] theorem OpenAddSubgroup.coe_finset_inf
    {G ι : Type*} [AddGroup G] [TopologicalSpace G] {s : Finset ι} {f : ι → OpenAddSubgroup G} :
    ((s.inf f : OpenAddSubgroup G) : Set G) = s.inf fun i ↦ (f i : Set G) := by
  classical induction s using Finset.induction with
  | empty => simp
  | insert i s hi hI => simp [hI]
