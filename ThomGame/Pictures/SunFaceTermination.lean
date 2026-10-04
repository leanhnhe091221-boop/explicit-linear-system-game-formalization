module

public import ThomGame.Pictures.SunRimFaces
public import ThomGame.Pictures.CircuitEmptyRegion

/-!
# A finite inward switch trace reaches a graph whose rims are face orbits

All invariants in `SunFaceState` are proved for the actual endpoint graph.
The smoothing trace and its circle records remain explicit. This does not
assert a covering property of the labels, or a structural isomorphism to
the graph of a newly realized diagram.
-/

@[expose] public section
namespace ThomGame.Pictures

open RibbonConnectivity
open scoped BigOperators

variable {n : Nat} {b : Fin n → ZMod 2} {w : List (Fin n ⊕ Fin n)}
  (hn : 3 ≤ n) (hw : ∀ z ∈ w, ∃ j, z = Sum.inl j)

namespace PortGraph

structure SunFaceState (G : PortGraph (sunPresentation n b) [] w) : Prop where
  minimal : G.SunMinimalState
  noJoints : IsEmpty G.Joint
  boundary : G.HubsReachBoundary
  terminal : G.NoInteriorSunSpoke hn hw
  faces : G.SunRimsBoundFaceOrbits hn hw

namespace SunFaceState

variable {G : PortGraph (sunPresentation n b) [] w}

theorem of_terminal (h : G.SunMinimalState) (hJ : IsEmpty G.Joint)
    (hb : G.HubsReachBoundary) (hNo : G.NoInteriorSunSpoke hn hw) : G.SunFaceState hn hw := by
  let : IsEmpty G.Joint := hJ
  exact ⟨h, hJ, hb, hNo, G.noInteriorSunSpoke_rims_bound_faces hn hw h.euler h.sees hNo hb⟩

variable (h : G.SunFaceState hn hw)

include h in
theorem interior_marked (a : G.SunRimDart hn) {x : G.Dart}
    (hx : (G.sunRimSimpleCircuit hn (by simp) hw a).CutInterior x) :
    (G.sunRimSimpleCircuit hn (by simp) hw a).Marked x := by
  let : IsEmpty G.Joint := h.noJoints
  exact G.noInteriorSunSpoke_interior_marked hn hw h.minimal.euler h.minimal.sees h.terminal a
    ((G.sunRimSimpleCircuit hn (by simp) hw a).meetsBoundary_of_hubsReachBoundary h.boundary) hx

include h in
theorem total_interior_count_eq_zero
    (hb : ∀ a : G.SunRimDart hn, (G.sunRimSimpleCircuit hn (by simp) hw a).MeetsBoundary) :
    G.sunTotalInteriorSpokeCount hn (by simp) hw h.minimal.euler h.minimal.sees hb = 0 := by
  let : IsEmpty G.Joint := h.noJoints
  exact G.noInteriorSunSpoke_total_interior_count hn hw h.minimal.euler h.minimal.sees h.terminal hb

include h in
theorem interior_region_empty (a : G.SunRimDart hn)
    (hb : (G.sunRimSimpleCircuit hn (by simp) hw a).MeetsBoundary) :
    let C := G.sunRimSimpleCircuit hn (by simp) hw a
    IsEmpty (Subtype (C.KeptDart (!C.boundarySide hb))) ∧
      IsEmpty (C.keptPairing (!C.boundarySide hb)).Edge ∧
      IsEmpty (C.InteriorHub (!C.boundarySide hb)) ∧
      IsEmpty (C.InteriorJoint (!C.boundarySide hb)) ∧
      C.frontierWord (!C.boundarySide hb) = [] ∧
      IsEmpty (C.RegionPort (!C.boundarySide hb)) := by
  let C := G.sunRimSimpleCircuit hn (by simp) hw a
  have hc (x : G.Dart) (_ : C.OnCircuitVertex x.vertex) (hx : C.OnSide (!C.boundarySide hb) x) :
      C.Marked x := h.interior_marked hn hw a
    ((C.on_opposite_boundarySide_iff (G.dualEuler_eq_twice_components h.minimal.euler)
      h.minimal.sees hb x).mp hx)
  exact ⟨C.keptDart_isEmpty_of_closed _ hc, C.keptEdge_isEmpty_of_closed _ hc,
    C.interiorHub_isEmpty_of_closed _ hc, C.interiorJoint_isEmpty_of_closed _ hc,
    C.frontierWord_eq_nil_of_closed _ hc (G.dualEuler_eq_twice_components h.minimal.euler),
    C.regionPort_isEmpty_of_closed _ hc (G.dualEuler_eq_twice_components h.minimal.euler)⟩

end SunFaceState
end PortGraph

namespace Smoothing

theorem exists_sun_face_switches {d : Diagram (sunPresentation n b) [] w}
    {G : PortGraph (sunPresentation n b) [] w} [IsEmpty G.Joint] {cs : List (Fin n ⊕ Fin n)}
    (t : Smoothing d.graph G cs) (hm : d.CharacterMinimal) :
    ∃ (H : PortGraph (sunPresentation n b) [] w) (q : PortGraph.SunSwitchTrace G H),
      q.Inward hn hw ∧ H.SunFaceState hn hw ∧
      (∑ h : H.Hub, ([H.hubLabel h] : Multiset (Fin n))) = (d.labels : Multiset (Fin n)) ∧
      Fintype.card H.Hub = d.size ∧ H.sign = d.sign ∧
      H.boundaryNext = d.graph.boundaryNext ∧
      q.length ≤ G.sunTotalInteriorSpokeCount hn (by simp) hw
        (t.sunMinimalState hm).euler (t.sunMinimalState hm).sees
        (t.sun_rim_meetsBoundary hm hn (by simp) hw) := by
  obtain ⟨H, q, hq, hNo, hJ, hH, hb, hc, hs, hlen⟩ := t.exists_terminal_sun_switches hm hn hw
  exact ⟨H, q, hq, PortGraph.SunFaceState.of_terminal hn hw hH hJ hb hNo,
    q.hub_relations.trans (t.hub_relations.trans d.graph_hub_relations), hc, hs,
    (q.boundaryNext (t.sunMinimalState hm)).trans t.boundaryNext, hlen⟩

end Smoothing
end ThomGame.Pictures
