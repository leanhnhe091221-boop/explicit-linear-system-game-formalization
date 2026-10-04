module

public import ThomGame.Finite.HypergraphCycles

/-!
# Constellations of indexed closed hypergraph cycles

These are the finite incidence conditions of Slofstra Definition 11.2.
The cycle indexing supplies the order used in part (a)(ii). The last
two conditions express intersections of size at most one, and disjoint
nonstellar cycles, without replacing natural incidence multiplicities.
No picture normalization theorem is part of this definition.
-/

@[expose] public section
namespace ThomGame.Hypergraph

variable {V E I : Type*} [DecidableEq V] [DecidableEq E] {H : Hypergraph V E}

def HasPrivateEdge (Φ : I → Cycle H) (i : I) : Prop :=
  ∃ e, e ∈ Set.range (Φ i).edge ∧ ∀ j, e ∈ Set.range (Φ j).edge → j = i

def ShareEdge (Φ : I → Cycle H) (i j : I) : Prop :=
  ∃ e, e ∈ Set.range (Φ i).edge ∧ e ∈ Set.range (Φ j).edge

structure Constellation (Φ : I → Cycle H) (b : V → ZMod 2) where
  neighbourhood : ∀ i, (Φ i).SunNeighbourhood
  stellar_or_covered : ∀ i, Nonempty ((Φ i).Stellar b) ∨
    ∀ k : Fin (Φ i).length, 2 ≤ k.val →
      ∃ j, Nonempty ((Φ j).Stellar b) ∧ (Φ i).edge k ∈ Set.range (Φ j).edge
  private_or_neighbour : ∀ i, HasPrivateEdge Φ i ∨
    ∃ j, j ≠ i ∧ ShareEdge Φ i j ∧ HasPrivateEdge Φ j
  intersection_unique : ∀ i j, i ≠ j → ∀ e f,
    e ∈ Set.range (Φ i).edge → e ∈ Set.range (Φ j).edge →
    f ∈ Set.range (Φ i).edge → f ∈ Set.range (Φ j).edge → e = f
  nonstellar_disjoint : ∀ i j, i ≠ j →
    ¬ Nonempty ((Φ i).Stellar b) → ¬ Nonempty ((Φ j).Stellar b) → ¬ ShareEdge Φ i j

namespace Constellation

variable {Φ : I → Cycle H} {b : V → ZMod 2} (h : Constellation Φ b)

include h in
/-- The indices describe genuinely different cycles, as witnessed by
their edge sets; duplicate copies cannot satisfy the intersection rule. -/
theorem edge_range_injective : Function.Injective (fun i => Set.range (Φ i).edge) := by
  intro i j he
  by_contra hij
  let u : Fin (Φ i).length := ⟨0, by have := (Φ i).length_ge_three; omega⟩
  let v : Fin (Φ i).length := ⟨1, by have := (Φ i).length_ge_three; omega⟩
  have hu : (Φ i).edge u ∈ Set.range (Φ i).edge := ⟨u, rfl⟩
  have hv : (Φ i).edge v ∈ Set.range (Φ i).edge := ⟨v, rfl⟩
  change Set.range (Φ i).edge = Set.range (Φ j).edge at he
  have huj : (Φ i).edge u ∈ Set.range (Φ j).edge := by
    rw [← he]
    exact hu
  have hvj : (Φ i).edge v ∈ Set.range (Φ j).edge := by
    rw [← he]
    exact hv
  have huv := h.intersection_unique i j hij _ _ hu huj hv hvj
  have hval := congrArg Fin.val ((Φ i).edge.injective huv)
  change 0 = 1 at hval
  exact Nat.zero_ne_one hval

def withAllStellar (b' : V → ZMod 2) (stars : ∀ i, (Φ i).Stellar b') : Constellation Φ b' where
  neighbourhood := h.neighbourhood
  stellar_or_covered i := Or.inl ⟨stars i⟩
  private_or_neighbour := h.private_or_neighbour
  intersection_unique := h.intersection_unique
  nonstellar_disjoint i _ _ hi _ := (hi ⟨stars i⟩).elim

end Constellation
end ThomGame.Hypergraph
