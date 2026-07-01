module

import RogersRamanujan.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-! # Open maps from a nonarchimedean group
-/

@[expose] public section

theorem IsOpenMap.nonarchimedeanAddGroup
    {A B : Type*} [AddGroup A] [AddGroup B] [TopologicalSpace A] [TopologicalSpace B]
    {F : Type*} [FunLike F A B] [AddMonoidHomClass F A B] (f : F)
    (hfo : IsOpenMap f) (hfc : Continuous f)
    [NonarchimedeanAddGroup A] [IsTopologicalAddGroup B] :
    NonarchimedeanAddGroup B where
  is_nonarchimedean U hU :=
    let ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean (f ⁻¹' U) <|
      hfc.continuousAt.preimage_mem_nhds <| by simpa
    ⟨⟨V.map f, by simpa using hfo _ V.isOpen⟩, by simpa⟩

theorem IsOpenMap.nonarchimedeanRing
    {A B : Type*} [Ring A] [Ring B] [TopologicalSpace A] [TopologicalSpace B]
    {F : Type*} [FunLike F A B] [RingHomClass F A B] (f : F)
    (hfo : IsOpenMap f) (hfc : Continuous f)
    [NonarchimedeanAddGroup A] [IsTopologicalRing B] :
    NonarchimedeanRing B where
  __ := hfo.nonarchimedeanAddGroup (f := f) hfc
