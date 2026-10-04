module

public import ThomGame.Pictures.MinimalBoundaryAccessibility
public import ThomGame.Pictures.SunBoundarySides
public import ThomGame.Pictures.SunSwitchTrace

/-!
# Actual minimal sun diagrams supply the required boundary witnesses

Character minimality for suns implies minimum size with fixed boundary.
Every hub therefore reaches the boundary. This property survives arbitrary
smoothing traces and actual sun switches. After all joints have been
smoothed, every simple circuit has a boundary-visible ambient component,
including every rim at every stage of a finite switch trace. Recorded
circles are not discarded or identified with port-bearing components.
-/

@[expose] public section
namespace ThomGame.Pictures

open RibbonConnectivity

namespace PortGraph.SimpleCircuit

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
  {G : PortGraph P u v} [IsEmpty G.Joint]

theorem meetsBoundary_of_hubsReachBoundary (C : G.SimpleCircuit) (hb : G.HubsReachBoundary) :
    C.MeetsBoundary := by
  obtain ⟨i, hi⟩ := G.connected_boundary_of_hubsReachBoundary hb C.cutBase
  exact ⟨G.boundaryDart i, (G.boundaryPorts i).property,
    ((RotationEuler.connected_swap_iff _ _ _ _).mp hi).symm⟩

end PortGraph.SimpleCircuit

variable {n : Nat} {b : Fin n → ZMod 2} {u v w : List (Fin n ⊕ Fin n)}

namespace Diagram

theorem sun_hubsReachBoundary (d : Diagram (sunPresentation n b) u v) (hm : d.CharacterMinimal) :
    d.graph.HubsReachBoundary :=
  d.hubsReachBoundary_of_minimum_size (d.sun_characterMinimal_iff.mp hm)

end Diagram

namespace Smoothing

theorem sun_hubsReachBoundary {d : Diagram (sunPresentation n b) u v}
    {G : PortGraph (sunPresentation n b) u v} {cs : List (Fin n ⊕ Fin n)}
    (t : Smoothing d.graph G cs) (hm : d.CharacterMinimal) : G.HubsReachBoundary :=
  t.hubsReachBoundary (fun _ => by change 0 < 3; decide +kernel) (d.sun_hubsReachBoundary hm)

theorem sun_rim_meetsBoundary {d : Diagram (sunPresentation n b) u v}
    {G : PortGraph (sunPresentation n b) u v} [IsEmpty G.Joint] {cs : List (Fin n ⊕ Fin n)}
    (t : Smoothing d.graph G cs) (hm : d.CharacterMinimal) (hn : 3 ≤ n)
    (hu : ∀ z ∈ u, ∃ j, z = Sum.inl j) (hv : ∀ z ∈ v, ∃ j, z = Sum.inl j)
    (a : G.SunRimDart hn) : (G.sunRimSimpleCircuit hn hu hv a).MeetsBoundary :=
  (G.sunRimSimpleCircuit hn hu hv a).meetsBoundary_of_hubsReachBoundary (t.sun_hubsReachBoundary hm)

end Smoothing

namespace PortGraph.SunSpoke

theorem switch_hubsReachBoundary {G : PortGraph (sunPresentation n b) u v}
    (s : G.SunSpoke) (hb : G.HubsReachBoundary) : s.switch.HubsReachBoundary := by
  intro h
  obtain ⟨i, hi⟩ := hb h
  have hc := G.reachable_connects_darts hi (.hub h (0 : Fin 3)) (G.boundaryDart i) rfl
    (G.boundaryDart_vertex i)
  have hs := (s.switch_circuit_connected (.hub h (0 : Fin 3)) (G.boundaryDart i)).mpr hc
  have he : s.switch.boundaryDart i = G.boundaryDart i := by cases i <;> rfl
  rw [← he] at hs
  have hr := s.switch.connected_vertex_reachable hs
  rw [s.switch.boundaryDart_vertex] at hr
  exact ⟨i, hr⟩

end PortGraph.SunSpoke

namespace PortGraph.SunSwitchTrace

theorem hubsReachBoundary {G H : PortGraph (sunPresentation n b) [] w}
    (t : SunSwitchTrace G H) (hb : G.HubsReachBoundary) : H.HubsReachBoundary := by
  induction t with
  | refl _ => exact hb
  | step s _ ih => exact ih (s.switch_hubsReachBoundary hb)

theorem smoothed_minimal_rims_meetBoundary {d : Diagram (sunPresentation n b) [] w}
    {G H : PortGraph (sunPresentation n b) [] w} [IsEmpty H.Joint]
    {cs : List (Fin n ⊕ Fin n)} (t : Smoothing d.graph G cs)
    (q : SunSwitchTrace G H) (hm : d.CharacterMinimal) (hn : 3 ≤ n)
    (hw : ∀ z ∈ w, ∃ j, z = Sum.inl j) (a : H.SunRimDart hn) :
    (H.sunRimSimpleCircuit hn (by simp) hw a).MeetsBoundary :=
  (H.sunRimSimpleCircuit hn (by simp) hw a).meetsBoundary_of_hubsReachBoundary
    (q.hubsReachBoundary (t.sun_hubsReachBoundary hm))

end PortGraph.SunSwitchTrace
end ThomGame.Pictures
