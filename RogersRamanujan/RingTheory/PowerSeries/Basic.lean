module

public import Mathlib.RingTheory.PowerSeries.Basic

/-! # Basic power series lemmas
-/

@[expose] public section

open Finset

open PowerSeries

namespace Polynomial
variable {R : Type*}

@[simp] theorem coe_natCast [Semiring R] {k : ℕ} : ((k : R[X]) : R⟦X⟧) = k :=
  map_natCast coeToPowerSeries.ringHom k

@[simp] theorem coe_intCast [Ring R] {k : ℤ} : ((k : R[X]) : R⟦X⟧) = k :=
  map_intCast (coeToPowerSeries.ringHom (R := R)) k

theorem coe_zsmul [Ring R] {k : ℤ} {f : R[X]} : ((k • f : R[X]) : R⟦X⟧) = k • (f : R⟦X⟧) := by simp

@[simp] theorem coe_sum [Semiring R] {ι : Type*} {f : ι → R[X]} {s : Finset ι} :
    ((∑ i ∈ s, f i : R[X]) : R⟦X⟧) = ∑ i ∈ s, (f i : R⟦X⟧) :=
  map_sum coeToPowerSeries.ringHom f s

@[simp] theorem coe_finsuppSum [Semiring R] {ι α : Type*} [Zero α] {f : ι →₀ α} {g : ι → α → R[X]} :
    (↑(f.sum g) : R⟦X⟧) = f.sum fun i r ↦ (g i r : R⟦X⟧) :=
  map_finsuppSum coeToPowerSeries.ringHom f g

end Polynomial
