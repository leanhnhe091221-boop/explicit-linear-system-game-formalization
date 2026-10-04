module

public import ThomGame.Pictures.CircuitFaces
public import ThomGame.Pictures.CircuitRegionGraph

/-!
# A closed circuit side has empty combinatorial restriction

The retained darts, vertices, frontier word, and region ports are those
of the existing region construction. No edge or vertex of the circuit's
ambient component remains after the rim itself is removed. Components
outside that ambient component and recorded circles are not encoded by
this restriction and are not discarded by these statements.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open Equiv RibbonConnectivity

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
  {G : PortGraph P u v} (C : G.SimpleCircuit) (side : Bool)
  (hclosed : ∀ x, C.OnCircuitVertex x.vertex → C.OnSide side x → C.Marked x)

include hclosed

theorem keptDart_isEmpty_of_closed : IsEmpty (Subtype (C.KeptDart side)) :=
  ⟨fun x => x.property.1 (C.marked_of_closed_side side hclosed x.property.2)⟩

theorem not_interiorVertex_of_closed (v : G.Vertex) : ¬ C.InteriorVertex side v := by
  rintro ⟨hv, x, hx, hs⟩
  exact hv (hx ▸ C.marked_onCircuitVertex (C.marked_of_closed_side side hclosed hs))

theorem interiorHub_isEmpty_of_closed : IsEmpty (C.InteriorHub side) :=
  ⟨fun h => C.not_interiorVertex_of_closed side hclosed _ h.property⟩

theorem interiorJoint_isEmpty_of_closed : IsEmpty (C.InteriorJoint side) :=
  ⟨fun j => C.not_interiorVertex_of_closed side hclosed _ j.property⟩

theorem keptEdge_isEmpty_of_closed : IsEmpty (C.keptPairing side).Edge := by
  refine ⟨fun e => Quotient.inductionOn e ?_⟩
  intro x
  exact (C.keptDart_isEmpty_of_closed side hclosed).false x

variable (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
  2 * Nat.card (Component G.circuitStep G.pairing.perm))

include hEuler

theorem frontier_isEmpty_of_closed : IsEmpty (Subtype (C.Frontier side)) := by
  refine ⟨?_⟩
  rintro ⟨x, hx⟩
  obtain ⟨hv, hm, hs⟩ := (C.frontier_iff hEuler side x).mp hx
  exact hm (hclosed x hv hs)

theorem frontierWord_eq_nil_of_closed : C.frontierWord side = [] := by
  apply List.length_eq_zero_iff.mp
  by_contra hn
  let i : Fin (C.frontierWord side).length := ⟨0, by omega⟩
  exact (C.frontier_isEmpty_of_closed side hclosed hEuler).false (C.boundaryEnumeration side i)

theorem regionPort_isEmpty_of_closed : IsEmpty (C.RegionPort side) :=
  ⟨fun x => (C.keptDart_isEmpty_of_closed side hclosed).false (C.regionPortMap hEuler side x)⟩

end ThomGame.Pictures.PortGraph.SimpleCircuit
