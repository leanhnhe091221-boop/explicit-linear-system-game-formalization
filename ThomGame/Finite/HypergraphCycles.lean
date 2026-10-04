module

public import ThomGame.Finite.Hypergraph
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Logic.Relation

/-!
# Indexed cycles, sun neighbourhoods, and stellar cycles

A cycle is specified by distinct indexed vertices and edges, with length
at least three. Each rim edge has multiplicity one at precisely its two
cyclic endpoints, including in the ambient hypergraph. Thus it is a closed
subhypergraph, not just a cycle inside a chosen open neighbourhood.

A stellar certificate supplies the actual retraction onto a sun, identifies
its rim with the cycle, and checks the zero vertex labelling. The exact
neighbourhood and cubic degree are consequences of these data.
-/

@[expose] public section
namespace ThomGame.Hypergraph

def sun (n : Nat) : Hypergraph (Fin n) (Fin n ⊕ Fin n) where
  incidence j := [Sum.inl j, Sum.inr j, Sum.inr (finRotate n j)]

theorem sun_edge_incident {n : Nat} (e : Fin n ⊕ Fin n) :
    ∃ j, e ∈ (sun n).incidence j := by
  cases e with
  | inl j => exact ⟨j, by simp [sun]⟩
  | inr j => exact ⟨j, by simp [sun]⟩

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

structure Cycle (H : Hypergraph V E) where
  length : Nat
  length_ge_three : 3 ≤ length
  vertex : Fin length ↪ V
  edge : Fin length ↪ E
  edge_multiplicity : ∀ v j, H.multiplicity v (edge j) =
    if v = vertex j ∨ v = vertex ((finRotate length).symm j) then 1 else 0

namespace Cycle

variable {H : Hypergraph V E} (C : Cycle H)

instance length_neZero : NeZero C.length := ⟨by have := C.length_ge_three; omega⟩

theorem next_ne_self (j : Fin C.length) : finRotate C.length j ≠ j := by
  rw [finRotate_apply]
  intro h
  have hz : (1 : Fin C.length) = 0 := add_left_cancel (h.trans (add_zero j).symm)
  have hv := congrArg Fin.val hz
  change 1 % C.length = 0 at hv
  rw [Nat.mod_eq_of_lt (by have := C.length_ge_three; omega)] at hv
  exact Nat.one_ne_zero hv

theorem endpoints_distinct (j : Fin C.length) :
    C.vertex j ≠ C.vertex ((finRotate C.length).symm j) := by
  intro h
  have hi := C.vertex.injective h
  have hn := congrArg (finRotate C.length) hi
  exact C.next_ne_self j (by simpa using hn)

theorem next_next_ne_self (j : Fin C.length) :
    finRotate C.length (finRotate C.length j) ≠ j := by
  simp only [finRotate_apply, add_assoc]
  intro h
  have hz : (1 : Fin C.length) + 1 = 0 := add_left_cancel (h.trans (add_zero j).symm)
  have hv := congrArg Fin.val hz
  change (1 % C.length + 1 % C.length) % C.length = 0 at hv
  have h1 : 1 < C.length := by have := C.length_ge_three; omega
  have h2 : 2 < C.length := by have := C.length_ge_three; omega
  simp only [Nat.mod_eq_of_lt h1, Nat.reduceAdd, Nat.mod_eq_of_lt h2] at hv
  exact Nat.succ_ne_zero 1 hv

theorem incident_iff (v : V) (j : Fin C.length) :
    C.edge j ∈ H.incidence v ↔
      v = C.vertex j ∨ v = C.vertex ((finRotate C.length).symm j) := by
  rw [← Multiset.count_pos]
  change 0 < H.multiplicity v (C.edge j) ↔ _
  rw [C.edge_multiplicity]
  split <;> simp_all

theorem closed {v : V} {e : E} (he : e ∈ Set.range C.edge) (hv : e ∈ H.incidence v) :
    v ∈ Set.range C.vertex := by
  obtain ⟨j, rfl⟩ := he
  rcases (C.incident_iff v j).mp hv with h | h
  · exact ⟨j, h.symm⟩
  · exact ⟨(finRotate C.length).symm j, h.symm⟩

theorem incident_index_iff (i j : Fin C.length) :
    C.edge j ∈ H.incidence (C.vertex i) ↔ j = i ∨ j = finRotate C.length i := by
  rw [C.incident_iff]
  simp only [C.vertex.injective.eq_iff, Equiv.eq_symm_apply]
  exact or_congr eq_comm eq_comm

/-- The cyclic endpoint pair determines its edge uniquely. In particular,
the indexed closed subhypergraph has no parallel edges. -/
theorem edge_eq_of_endpoints (i j : Fin C.length)
    (hi : C.edge j ∈ H.incidence (C.vertex i))
    (hp : C.edge j ∈ H.incidence (C.vertex ((finRotate C.length).symm i))) : j = i := by
  rcases (C.incident_index_iff _ _).mp hi with h | h
  · exact h
  rcases (C.incident_index_iff _ _).mp hp with hp | hp
  · have hn := congrArg (finRotate C.length) (h.symm.trans hp)
    exact (C.next_next_ne_self i (by simpa using hn)).elim
  · exact hp.trans ((finRotate C.length).apply_symm_apply i)

theorem rim_degree (i : Fin C.length) :
    (Finset.univ.filter (fun j => C.edge j ∈ H.incidence (C.vertex i))).card = 2 := by
  have hs : Finset.univ.filter (fun j => C.edge j ∈ H.incidence (C.vertex i)) =
      {i, finRotate C.length i} := by
    ext j
    simp [C.incident_index_iff]
  rw [hs, Finset.card_pair (Ne.symm (C.next_ne_self i))]

/-- At any vertex on the cycle, one of its two rim edges differs from
a specified edge, while remaining incident at that same vertex. -/
theorem exists_other_incident {v : V} (hv : v ∈ Set.range C.vertex) (e : E) :
    ∃ f, f ∈ Set.range C.edge ∧ f ∈ H.incidence v ∧ f ≠ e := by
  classical
  obtain ⟨j, rfl⟩ := hv
  by_cases he : C.edge j = e
  · refine ⟨C.edge (finRotate C.length j), ⟨_, rfl⟩,
      (C.incident_index_iff _ _).mpr (Or.inr rfl), ?_⟩
    intro hn
    exact C.next_ne_self j (C.edge.injective (hn.trans he.symm))
  · exact ⟨C.edge j, ⟨j, rfl⟩, (C.incident_index_iff _ _).mpr (Or.inl rfl), he⟩

/-- Adjacency using just the selected rim edges. -/
def Adj (v w : V) : Prop :=
  v ≠ w ∧ ∃ j, C.edge j ∈ H.incidence v ∧ C.edge j ∈ H.incidence w

theorem adj_next (i : Fin C.length) : C.Adj (C.vertex i) (C.vertex (finRotate C.length i)) := by
  refine ⟨fun h => C.next_ne_self i (C.vertex.injective h).symm,
    finRotate C.length i, ?_, ?_⟩
  · exact (C.incident_index_iff _ _).mpr (Or.inr rfl)
  · exact (C.incident_index_iff _ _).mpr (Or.inl rfl)

theorem connected (i j : Fin C.length) : Relation.ReflTransGen C.Adj (C.vertex i) (C.vertex j) := by
  have hp (k : Nat) :
      Relation.ReflTransGen C.Adj (C.vertex i) (C.vertex ((finRotate C.length)^[k] i)) := by
    induction k with
    | zero => exact Relation.ReflTransGen.refl
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact ih.tail (C.adj_next _)
  have he : (finRotate C.length)^[(j - i).val] i = j := by
    rw [← finCycle_eq_finRotate_iterate]
    simp [finCycle_apply]
  simpa only [he] using hp (j - i).val

/-- An open sun with exactly this cycle as its rim. -/
structure SunNeighbourhood where
  inclusion : OpenEmbedding (sun C.length) H
  vertex_eq : ∀ j, inclusion.vertex j = C.vertex j
  rim_eq : ∀ j, inclusion.edge (.inr j) = C.edge j

namespace SunNeighbourhood

variable {C} (h : C.SunNeighbourhood)

def spoke (j : Fin C.length) : E := h.inclusion.edge (.inl j)

theorem incidence_eq (j : Fin C.length) :
    H.incidence (C.vertex j) = [h.spoke j, C.edge j, C.edge (finRotate C.length j)] := by
  rw [← h.vertex_eq, ← h.inclusion.incidence]
  simp [sun, spoke, h.rim_eq]

theorem spoke_not_mem_cycle (j : Fin C.length) : h.spoke j ∉ Set.range C.edge := by
  rintro ⟨k, hk⟩
  have he : h.inclusion.edge (.inr k) = h.inclusion.edge (.inl j) :=
    (h.rim_eq k).trans hk
  cases h.inclusion.edge.injective he

theorem edge_iff (e : E) :
    e ∈ Set.range h.inclusion.edge ↔ ∃ j, e ∈ H.incidence (C.vertex j) := by
  constructor
  · rintro ⟨f, rfl⟩
    obtain ⟨j, hj⟩ := sun_edge_incident f
    refine ⟨j, ?_⟩
    rw [← h.vertex_eq, ← h.inclusion.incidence]
    exact Multiset.mem_map.mpr ⟨f, hj, rfl⟩
  · rintro ⟨j, hj⟩
    rw [← h.vertex_eq, ← h.inclusion.incidence] at hj
    obtain ⟨f, _, hf⟩ := Multiset.mem_map.mp hj
    exact ⟨f, hf⟩

include h in
theorem cubic (j : Fin C.length) : (H.incidence (C.vertex j)).card = 3 := by
  rw [← h.vertex_eq, ← h.inclusion.incidence, Multiset.card_map]
  simp [sun]

end SunNeighbourhood

/-- Slofstra Definition 11.1, with the sun isomorphism and retraction
expressed by their actual maps. -/
structure Stellar (b : V → ZMod 2) where
  retraction : Retraction H (sun C.length)
  vertex_eq : ∀ j, retraction.inclusion.vertex j = C.vertex j
  rim_eq : ∀ j, retraction.inclusion.edge (.inr j) = C.edge j
  rhs_zero : ∀ j, b (C.vertex j) = 0

namespace Stellar

variable {C} {b : V → ZMod 2} (h : C.Stellar b)

def neighbourhood : C.SunNeighbourhood :=
  ⟨h.retraction.inclusion, h.vertex_eq, h.rim_eq⟩

/-- The open embedding has precisely the edges incident to the cycle's
vertices, so it is the actual neighbourhood, with no extra isolated edges. -/
theorem neighbourhood_edge_iff (e : E) :
    e ∈ Set.range h.retraction.inclusion.edge ↔
      ∃ j, e ∈ H.incidence (C.vertex j) := h.neighbourhood.edge_iff e

include h in
theorem cubic (j : Fin C.length) : (H.incidence (C.vertex j)).card = 3 :=
  h.neighbourhood.cubic j

end Stellar
end Cycle
end ThomGame.Hypergraph
