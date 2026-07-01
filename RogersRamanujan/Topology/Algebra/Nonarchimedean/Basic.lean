module

import RogersRamanujan.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-! # Nonarchimedean instances for pi types -/

@[expose] public section

open scoped Pointwise
open Filter Topology

theorem hasBasis_nhds_zero_openAddSubgroup
    {G : Type*} [AddGroup G] [TopologicalSpace G] [NonarchimedeanAddGroup G] :
    (𝓝 (0 : G)).HasBasis (fun _ : OpenAddSubgroup G ↦ True) (↑) :=
  (nhds_basis_opens 0).to_hasBasis (fun s hs ↦
    NonarchimedeanAddGroup.is_nonarchimedean _ (hs.2.mem_nhds hs.1) |>.elim
      (by grind)) fun s _ ↦ ⟨s, ⟨by simp, s.2⟩, by rfl⟩

instance {ι : Type*} {R : ι → Type*}
    [∀ i, AddGroup (R i)] [∀ i, TopologicalSpace (R i)] [∀ i, NonarchimedeanAddGroup (R i)] :
    NonarchimedeanAddGroup ((i : ι) → R i) where
  is_nonarchimedean _U hU :=
    let ⟨(_I, s), ⟨hif, _⟩, hiu⟩ := (nhds_pi (A := R) ▸ Filter.hasBasis_pi fun i ↦
      hasBasis_nhds_zero_openAddSubgroup (G := R i)).mem_iff.mp hU
    ⟨.pi hif s, hiu⟩

instance {ι : Type*} {R : ι → Type*}
    [∀ i, Ring (R i)] [∀ i, TopologicalSpace (R i)] [∀ i, NonarchimedeanRing (R i)] :
    NonarchimedeanRing ((i : ι) → R i) where
  __ := (inferInstance : NonarchimedeanAddGroup ((i : ι) → R i))
