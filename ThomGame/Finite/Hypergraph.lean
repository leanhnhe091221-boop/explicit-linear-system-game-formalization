module

public import ThomGame.Finite.SparseSystem
public import Mathlib.Data.Multiset.Filter
public import Mathlib.Tactic.FinCases

/-!
# Finite incidence data and generalized hypergraph morphisms

An incidence multiset retains multiplicities, as in the natural-number
incidence matrix of Slofstra §8. A generalized morphism sends vertices
and edges to an optional image. At a retained vertex, the multiset of
retained edge images is exactly the target incidence multiset. At a
deleted vertex it has even cardinality and at most one distinct edge.
These are the two local conditions of Definition 8.4.
-/

@[expose] public section
namespace ThomGame

structure Hypergraph (V E : Type*) where
  incidence : V → Multiset E

namespace Hypergraph

variable {V E W F : Type*}

def multiplicity (H : Hypergraph V E) [DecidableEq E] (v : V) (e : E) : Nat :=
  (H.incidence v).count e

def Monochromatic (s : Multiset E) : Prop := ∀ e ∈ s, ∀ f ∈ s, e = f

structure GeneralizedHom (H : Hypergraph V E) (K : Hypergraph W F) where
  vertex : V → Option W
  edge : E → Option F
  retained : ∀ v w, vertex v = some w → (H.incidence v).filterMap edge = K.incidence w
  deleted : ∀ v, vertex v = none →
    Even ((H.incidence v).filterMap edge).card ∧ Monochromatic ((H.incidence v).filterMap edge)

/-- An inclusion of an open subhypergraph: every incidence at an included
vertex is included, with its original multiplicity. -/
structure OpenEmbedding (H : Hypergraph V E) (K : Hypergraph W F) where
  vertex : V ↪ W
  edge : E ↪ F
  incidence : ∀ v, (H.incidence v).map edge = K.incidence (vertex v)

structure Retraction (H : Hypergraph V E) (K : Hypergraph W F) where
  inclusion : OpenEmbedding K H
  retract : GeneralizedHom H K
  vertex_leftInverse : ∀ v, retract.vertex (inclusion.vertex v) = some v
  edge_leftInverse : ∀ e, retract.edge (inclusion.edge e) = some e

theorem GeneralizedHom.incident (H : Hypergraph V E) (K : Hypergraph W F)
    (φ : GeneralizedHom H K) {v : V} {w : W} {e : E} {f : F}
    (hv : φ.vertex v = some w) (he : φ.edge e = some f) (h : e ∈ H.incidence v) :
    f ∈ K.incidence w := by
  rw [← φ.retained v w hv]
  exact (Multiset.mem_filterMap _ _).mpr ⟨e, h, he⟩

theorem GeneralizedHom.retained_count (H : Hypergraph V E) (K : Hypergraph W F)
    [DecidableEq F] (φ : GeneralizedHom H K) {v : V} {w : W}
    (hv : φ.vertex v = some w) (f : F) :
    ((H.incidence v).filterMap φ.edge).count f = K.multiplicity w f := by
  rw [φ.retained v w hv]
  rfl

end Hypergraph

namespace SparseSystem

variable {R C : Type*}

def hypergraph (S : SparseSystem R C) : Hypergraph R C where
  incidence r := [S.column r 0, S.column r 1, S.column r 2]

theorem mem_hypergraph_incidence (S : SparseSystem R C) (r : R) (c : C) :
    c ∈ S.hypergraph.incidence r ↔ ∃ i, S.column r i = c := by
  change c ∈ ([S.column r 0, S.column r 1, S.column r 2] : Multiset C) ↔ _
  simp only [Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro (h | h | h)
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩
    · exact ⟨2, h.symm⟩
  · rintro ⟨i, hi⟩
    fin_cases i
    · exact Or.inl hi.symm
    · exact Or.inr (Or.inl hi.symm)
    · exact Or.inr (Or.inr hi.symm)

end SparseSystem
end ThomGame
