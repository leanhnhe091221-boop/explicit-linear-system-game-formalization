module

public import ThomGame.Finite.HypergraphCycles
public import Mathlib.Data.ZMod.Basic

/-!
# The finite local rules for folding a wheel onto a five-sided sun

`hit` marks an occurrence of the selected ordinary letter. The phase
changes by one at each occurrence. Consecutive occurrences are excluded
by cyclic reduction. The three original row families map according to
these rules; every possible local state is checked by kernel reduction.
-/

@[expose] public section
namespace ThomGame.PentagonFold

abbrev Edge := Fin 5 ⊕ Fin 5

def step (p : ZMod 2) (hit : Bool) : ZMod 2 := p + if hit then 1 else 0

def ordinary (hit : Bool) : Option Edge := if hit then some (.inl 0) else none

def a (hit : Bool) (p : ZMod 2) : Option Edge :=
  some (if hit then (if p = 0 then .inr 0 else .inr 1)
    else if p = 0 then .inl 4 else .inl 1)

def b (hit : Bool) (p : ZMod 2) : Option Edge :=
  some (if hit then (if p = 0 then .inr 1 else .inr 0)
    else if p = 0 then .inl 4 else .inl 1)

def c (hit nextHit : Bool) (p : ZMod 2) : Option Edge :=
  if hit then some (if p = 0 then .inr 2 else .inr 4)
  else if nextHit then some (if p = 0 then .inr 4 else .inr 2)
  else none

def d (hit : Bool) (p : ZMod 2) : Option Edge :=
  some (if hit then .inr 3 else if p = 0 then .inl 3 else .inl 2)

def vertex (hit nextHit : Bool) (p : ZMod 2) : Fin 3 → Option (Fin 5) :=
  ![if hit then some 0 else none,
    if hit then some (if p = 0 then 1 else 4)
      else if nextHit then some (if p = 0 then 4 else 1) else none,
    if hit then some (if p = 0 then 2 else 3)
      else if nextHit then some (if p = 0 then 3 else 2) else none]

def aux (hit nextHit : Bool) (p : ZMod 2) : Fin 4 → Option Edge :=
  ![a hit p, b hit p, c hit nextHit p, d hit p]

def rowImages (hit nextHit : Bool) (p : ZMod 2) : Fin 3 → Multiset Edge :=
  fun k => (if k = 0 then [ordinary hit, a hit p, b hit p]
    else if k = 1 then [b hit p, c hit nextHit p, a nextHit (step p hit)]
    else [c hit nextHit p, d hit p, d nextHit (step p hit)]).filterMap id

theorem local_valid : ∀ (hit nextHit : Bool) (p : ZMod 2) (k : Fin 3),
    ¬ (hit = true ∧ nextHit = true) →
    (∀ v, vertex hit nextHit p k = some v →
      rowImages hit nextHit p k = (Hypergraph.sun 5).incidence v) ∧
    (vertex hit nextHit p k = none → Even (rowImages hit nextHit p k).card ∧
      Hypergraph.Monochromatic (rowImages hit nextHit p k)) := by
  intro hit nextHit p k h
  cases hit <;> cases nextHit <;> fin_cases p <;> fin_cases k
  all_goals first | exact (h ⟨rfl, rfl⟩).elim | (unfold Hypergraph.Monochromatic; decide +kernel)

theorem retained (hit nextHit : Bool) (p : ZMod 2) (k : Fin 3)
    (h : ¬ (hit = true ∧ nextHit = true)) {v : Fin 5} (hv : vertex hit nextHit p k = some v) :
    rowImages hit nextHit p k = (Hypergraph.sun 5).incidence v :=
  (local_valid hit nextHit p k h).1 v hv

theorem deleted (hit nextHit : Bool) (p : ZMod 2) (k : Fin 3)
    (h : ¬ (hit = true ∧ nextHit = true)) (hv : vertex hit nextHit p k = none) :
    Even (rowImages hit nextHit p k).card ∧ Hypergraph.Monochromatic (rowImages hit nextHit p k) :=
  (local_valid hit nextHit p k h).2 hv

end ThomGame.PentagonFold
