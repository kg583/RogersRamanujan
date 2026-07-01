module

import RogersRamanujan.Order.Filter.Prod
public import Mathlib.Topology.Separation.Regular

/-! # Regular spaces
-/

@[expose] public section

open Filter Topology

theorem Filter.Tendsto.of_prod {α β γ : Type*}
    {fa : Filter α} {fb : Filter β} [fb.NeBot] [TopologicalSpace γ] [RegularSpace γ]
    {f : α → β → γ} {l : α → γ} {c : γ}
    (hf : Tendsto f.uncurry (fa ×ˢ fb) (𝓝 c))
    (hfl : ∀ᶠ x in fa, Tendsto (f x) fb (𝓝 <| l x)) :
    Tendsto l fa (𝓝 c) := by
  refine (hasBasis_nhds_closure c).tendsto_right_iff.mpr fun U hU ↦ ?_
  obtain ⟨sa, hsa, sb, hsb, hsu⟩ := mem_prod_iff'.mp (hf hU)
  filter_upwards [hfl, hsa] with x hxb hxsa
  refine by_contra fun hlxv ↦ eventually_const (f := fb) |>.mp ?_
  filter_upwards [hsb, hxb (isClosed_closure.compl_mem_nhds hlxv)] with y hysb hycu
  exact hycu <| subset_closure <| hsu _ hxsa _ hysb

theorem Filter.Tendsto.of_prod' {α β γ : Type*}
    {fa : Filter α} {fb : Filter β} [fb.NeBot] [TopologicalSpace γ] [RegularSpace γ]
    {f : α × β → γ} {l : α → γ} {c : γ}
    (hf : Tendsto f (fa ×ˢ fb) (𝓝 c))
    (hfl : ∀ᶠ x in fa, Tendsto (fun y ↦ f (x, y)) fb (𝓝 <| l x)) :
    Tendsto l fa (𝓝 c) := hf.of_prod (f := f.curry) hfl
