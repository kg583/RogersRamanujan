module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.ZMod.Basic

public import RogersRamanujan.NumberTheory.Partitions.PR

@[expose] public section

namespace Nat.Partition

protected abbrev card (n : ℕ) : ℤ := Fintype.card (Partition n)

protected abbrev length {n : ℕ} (p : Partition n) := p.parts.card
protected abbrev maxPart {n : ℕ} (p : Partition n) := Multiset.fold max 0 p.parts

def lengthRestricted (n k : ℕ) :=  {p : Partition n // p.length <= k}
def sizeRestricted (n k : ℕ) :=  Partition.restricted n (· ≤ k)

protected abbrev rank {n : ℕ} (p : Partition n) := (p.maxPart : ℤ) - p.length

def rankFiber (m : ℤ) (n : ℕ) := {p : Partition n | p.rank = m}
def rankModFiber {q : ℕ} (m : ZMod q) (n : ℕ) := {p : Partition n | (p.rank : ZMod q) = m}

protected abbrev crank {n : ℕ} (p : Partition n) :=
  let w := p.parts.count 1
  if w = 0 then (p.maxPart : ℤ) else (w : ℤ) - (p.parts.filter (· > w)).card

def crankFiber (m : ℤ) (n : ℕ) := {p : Partition n | p.crank = m}
def crankModFiber {q : ℕ} (m : ZMod q) (n : ℕ) := {p : Partition n | (p.crank : ZMod q) = m}

def spt (n : ℕ) := ∑ p : Partition n, p.parts.count (Multiset.fold min 1 p.parts)

end Nat.Partition
