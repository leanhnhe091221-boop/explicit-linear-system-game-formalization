module

public import ThomGame.Pictures.BoundaryOrder

/-!
# The exact three-edge boundary of an outer quadrilateral

This certificate records a simple three-edge face walk between adjacent
ambient boundary positions. Its internal vertices are two distinct hubs,
and its three picture edges are proved distinct. It records boundary
incidences and cyclic order; identifying its bounded region as an empty
geometric face is a separate realization issue.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
  (G : PortGraph P u v)

theorem rotation_boundaryDart (i : BoundaryIndex u v) : G.rotation (G.boundaryDart i) = G.boundaryDart i := by
  cases i <;> rfl

theorem boundaryDart_vertex_ne_hub (i : BoundaryIndex u v) (h : G.Hub) :
    (G.boundaryDart i).vertex ≠ .inr (.inl h) := by
  cases i <;> intro he <;> cases he

structure BoundaryQuadPath where
  start : BoundaryIndex u v
  finish : BoundaryIndex u v
  firstHub : G.Hub
  secondHub : G.Hub
  firstSlot : Fin (P.word (G.hubLabel firstHub)).length
  secondSlot : Fin (P.word (G.hubLabel secondHub)).length
  first_step : G.circuitStep (G.boundaryDart start) = .hub firstHub firstSlot
  second_step : G.circuitStep (.hub firstHub firstSlot) = .hub secondHub secondSlot
  last_step : G.circuitStep (.hub secondHub secondSlot) = G.boundaryDart finish
  boundary_adjacent : boundaryCyclic u v start = finish
  ends_distinct : start ≠ finish
  hubs_distinct : firstHub ≠ secondHub

namespace BoundaryQuadPath

variable {G} (q : G.BoundaryQuadPath)

abbrev firstDart : G.Dart := G.boundaryDart q.start
abbrev middleDart : G.Dart := .hub q.firstHub q.firstSlot
abbrev lastDart : G.Dart := .hub q.secondHub q.secondSlot

theorem first_twin_vertex : (G.pairing.twin q.firstDart).vertex = .inr (.inl q.firstHub) :=
  (G.vertex_circuitStep q.firstDart).symm.trans (congrArg Port.vertex q.first_step)

theorem middle_twin_vertex : (G.pairing.twin q.middleDart).vertex = .inr (.inl q.secondHub) :=
  (G.vertex_circuitStep q.middleDart).symm.trans (congrArg Port.vertex q.second_step)

theorem last_twin : G.pairing.twin q.lastDart = G.boundaryDart q.finish := by
  apply G.rotation.injective
  exact q.last_step.trans (G.rotation_boundaryDart q.finish).symm

theorem boundaryNext : G.boundaryNext q.start = q.finish := by
  apply G.boundaryNext_eq_of_first q.start q.finish (n := 3) (by omega)
  · simp only [pow_succ', pow_zero, Equiv.Perm.one_apply, Equiv.Perm.mul_apply,
      q.first_step, q.second_step, q.last_step]
  · intro k hk hkn
    have h : k = 1 ∨ k = 2 := by omega
    rcases h with rfl | rfl
    · rw [pow_one, q.first_step]
      exact id
    · rw [pow_two, Equiv.Perm.mul_apply, q.first_step, q.second_step]
      exact id

theorem first_edge_ne_middle : G.pairing.edge q.firstDart ≠ G.pairing.edge q.middleDart := by
  intro he
  rcases (G.pairing.edge_eq_iff _ _).mp he with he | he
  · exact G.boundaryDart_vertex_ne_hub q.start q.firstHub (congrArg Port.vertex he)
  · exact G.boundaryDart_vertex_ne_hub q.start q.secondHub
      ((congrArg Port.vertex he).trans q.middle_twin_vertex)

theorem first_edge_ne_last : G.pairing.edge q.firstDart ≠ G.pairing.edge q.lastDart := by
  intro he
  rcases (G.pairing.edge_eq_iff _ _).mp he with he | he
  · exact G.boundaryDart_vertex_ne_hub q.start q.secondHub (congrArg Port.vertex he)
  · rw [q.last_twin] at he
    exact q.ends_distinct (G.boundaryDart.injective he)

theorem middle_edge_ne_last : G.pairing.edge q.middleDart ≠ G.pairing.edge q.lastDart := by
  intro he
  rcases (G.pairing.edge_eq_iff _ _).mp he with he | he
  · exact q.hubs_distinct (Sum.inl.inj (Sum.inr.inj (congrArg Port.vertex he)))
  · rw [q.last_twin] at he
    exact G.boundaryDart_vertex_ne_hub q.finish q.firstHub (congrArg Port.vertex he.symm)

end BoundaryQuadPath
end ThomGame.Pictures.PortGraph
