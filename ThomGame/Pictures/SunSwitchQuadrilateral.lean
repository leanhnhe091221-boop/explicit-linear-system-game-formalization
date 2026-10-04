module

public import ThomGame.Pictures.SunSwitchBoundary
public import ThomGame.Pictures.BoundaryQuadPath

/-!
# Preserving the three-edge boundaries of sun outer quadrilaterals

With only spokes on the boundary, both hubs on a quadrilateral boundary
have their unique spoke paired to the ambient boundary. Neither can be
an endpoint of the internal spoke being switched. Hence all three edge
pairs and both local face turns are unchanged. This preserves the exact
boundary certificate, not a relabelled or merely equal-size replacement.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) u v}

theorem sun_boundary_twin_at_hub
    (hb : ∀ i : BoundaryIndex u v, ∃ j, Port.label G.jointLabel (G.boundaryDart i) = Sum.inl j)
    (i : BoundaryIndex u v) (h : G.Hub)
    (hv : (G.pairing.twin (G.boundaryDart i)).vertex = .inr (.inl h)) :
    G.pairing.twin (G.boundaryDart i) = .hub h (0 : Fin 3) := by
  have hl := G.pairing.label_twin (G.boundaryDart i)
  generalize he : G.pairing.twin (G.boundaryDart i) = a at hl hv ⊢
  cases a with
  | top k => cases hv
  | bottom k => cases hv
  | joint j side => cases hv
  | hub k p =>
    have hk : k = h := Sum.inl.inj (Sum.inr.inj hv)
    subst k
    obtain ⟨j, hj⟩ := hb i
    have hp := ((G.sun_hub_spoke_iff h p j).mp (hl.trans hj)).2
    exact congrArg (fun p : Fin 3 => (Port.hub h p : G.Dart)) hp

namespace BoundaryQuadPath

variable (q : G.BoundaryQuadPath)
  (hb : ∀ i : BoundaryIndex u v, ∃ j, Port.label G.jointLabel (G.boundaryDart i) = Sum.inl j)

include hb in
theorem sun_first_spoke_to_boundary :
    G.pairing.twin (.hub q.firstHub (0 : Fin 3)) = G.boundaryDart q.start := by
  have h := sun_boundary_twin_at_hub hb q.start q.firstHub q.first_twin_vertex
  rw [← h, G.pairing.involutive]

include hb in
theorem sun_last_spoke_to_boundary :
    G.pairing.twin (.hub q.secondHub (0 : Fin 3)) = G.boundaryDart q.finish := by
  obtain ⟨j, hj⟩ := hb q.finish
  have hl := G.pairing.label_twin q.lastDart
  rw [q.last_twin] at hl
  have hp := ((G.sun_hub_spoke_iff q.secondHub q.secondSlot j).mp (hl.symm.trans hj)).2
  have h := q.last_twin
  change G.pairing.twin (.hub q.secondHub q.secondSlot) = _ at h
  rwa [hp] at h

end BoundaryQuadPath

namespace SunSpoke

variable (s : G.SunSpoke)

theorem hub_ne_of_boundary_spoke (h : G.Hub) (i : BoundaryIndex u v)
    (hp : G.pairing.twin (.hub h (0 : Fin 3)) = G.boundaryDart i) : h ≠ s.left ∧ h ≠ s.right := by
  constructor
  · intro hh
    rw [hh, s.paired] at hp
    exact G.boundaryDart_vertex_ne_hub i s.right (congrArg Port.vertex hp.symm)
  · intro hh
    rw [hh, s.paired_right] at hp
    exact G.boundaryDart_vertex_ne_hub i s.left (congrArg Port.vertex hp.symm)

theorem switch_twin_away {x : G.Dart}
    (hl : x.vertex ≠ .inr (.inl s.left)) (hr : x.vertex ≠ .inr (.inl s.right))
    (hpl : (G.pairing.twin x).vertex ≠ .inr (.inl s.left))
    (hpr : (G.pairing.twin x).vertex ≠ .inr (.inl s.right)) :
    s.switch.pairing.twin x = G.pairing.twin x := by
  rw [s.switch_twin, s.portSwap_of_vertex_away hl hr, s.portSwap_of_vertex_away hpl hpr]

theorem switch_step_away {x : G.Dart}
    (hl : x.vertex ≠ .inr (.inl s.left)) (hr : x.vertex ≠ .inr (.inl s.right))
    (hpl : (G.pairing.twin x).vertex ≠ .inr (.inl s.left))
    (hpr : (G.pairing.twin x).vertex ≠ .inr (.inl s.right)) :
    s.switch.circuitStep x = G.circuitStep x := by
  rw [s.switch.circuitStep_apply, s.switch_twin_away hl hr hpl hpr, s.switch_rotation_away hpl hpr]
  rfl

variable (q : G.BoundaryQuadPath)
  (hb : ∀ i : BoundaryIndex u v, ∃ j, Port.label G.jointLabel (G.boundaryDart i) = Sum.inl j)

include hb in
theorem quad_hubs_away : (q.firstHub ≠ s.left ∧ q.firstHub ≠ s.right) ∧
    (q.secondHub ≠ s.left ∧ q.secondHub ≠ s.right) :=
  ⟨s.hub_ne_of_boundary_spoke q.firstHub q.start (q.sun_first_spoke_to_boundary hb),
    s.hub_ne_of_boundary_spoke q.secondHub q.finish (q.sun_last_spoke_to_boundary hb)⟩

include hb in
theorem quad_darts_away :
    ∀ x ∈ [q.firstDart, q.middleDart, q.lastDart],
      (x.vertex ≠ .inr (.inl s.left) ∧ x.vertex ≠ .inr (.inl s.right)) ∧
      ((G.pairing.twin x).vertex ≠ .inr (.inl s.left) ∧
        (G.pairing.twin x).vertex ≠ .inr (.inl s.right)) := by
  obtain ⟨hfirst, hlast⟩ := s.quad_hubs_away q hb
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · refine ⟨⟨G.boundaryDart_vertex_ne_hub _ _, G.boundaryDart_vertex_ne_hub _ _⟩, ?_⟩
    rw [q.first_twin_vertex]
    simpa only [ne_eq, Sum.inr.injEq, Sum.inl.injEq] using hfirst
  · constructor
    · simpa only [BoundaryQuadPath.middleDart, Port.vertex, ne_eq, Sum.inr.injEq, Sum.inl.injEq] using hfirst
    · rw [q.middle_twin_vertex]
      simpa only [ne_eq, Sum.inr.injEq, Sum.inl.injEq] using hlast
  · constructor
    · simpa only [BoundaryQuadPath.lastDart, Port.vertex, ne_eq, Sum.inr.injEq, Sum.inl.injEq] using hlast
    · rw [q.last_twin]
      exact ⟨G.boundaryDart_vertex_ne_hub _ _, G.boundaryDart_vertex_ne_hub _ _⟩

include hb in
theorem quad_pairs_preserved : ∀ x ∈ [q.firstDart, q.middleDart, q.lastDart],
    s.switch.pairing.twin x = G.pairing.twin x := by
  intro x hx
  obtain ⟨hl, hr⟩ := s.quad_darts_away q hb x hx
  exact s.switch_twin_away hl.1 hl.2 hr.1 hr.2

def switchQuadPath : s.switch.BoundaryQuadPath := by
  have hstep : ∀ x ∈ [q.firstDart, q.middleDart, q.lastDart],
      s.switch.circuitStep x = G.circuitStep x := by
    intro x hx
    obtain ⟨hl, hr⟩ := s.quad_darts_away q hb x hx
    exact s.switch_step_away hl.1 hl.2 hr.1 hr.2
  have hbd (i : BoundaryIndex u v) : s.switch.boundaryDart i = G.boundaryDart i := by cases i <;> rfl
  exact {
    start := q.start
    finish := q.finish
    firstHub := q.firstHub
    secondHub := q.secondHub
    firstSlot := q.firstSlot
    secondSlot := q.secondSlot
    first_step := (congrArg s.switch.circuitStep (hbd q.start)).trans
      ((hstep q.firstDart (by simp)).trans q.first_step)
    second_step := (hstep q.middleDart (by simp)).trans q.second_step
    last_step := (hstep q.lastDart (by simp)).trans (q.last_step.trans (hbd q.finish).symm)
    boundary_adjacent := q.boundary_adjacent
    ends_distinct := q.ends_distinct
    hubs_distinct := q.hubs_distinct }

end SunSpoke
end ThomGame.Pictures.PortGraph
