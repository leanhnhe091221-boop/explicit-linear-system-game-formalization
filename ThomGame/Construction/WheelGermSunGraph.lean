module

public import ThomGame.Construction.WheelSunDiagrams
public import ThomGame.Pictures.RetainedRowGraph
public import ThomGame.Pictures.TopBoundaryGraph
public import ThomGame.Pictures.CircuitGermBoundaryOrder
public import ThomGame.Pictures.DiagramBottomReversal
public import ThomGame.Pictures.ConnectedSunNormalization

/-!
# The actual stellar germ becomes an actual minimal sun graph

Equality of the retracted diagram size proves that every original germ
hub is retained. A generalized row map then acts on the germ itself.
Swapping its stored boundary names and reversing the top into the bottom
gives the correct sun boundary order. The complete port bijection retains
pairing, rotations and all outer-quadrilateral paths. Minimality comes
from the already proved minimum-size sun witness, without a graph
isomorphism assertion about that witness.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures RibbonConnectivity
open scoped BigOperators

variable {d : SigmaDiagram [] []} {H : SigmaGraph [] []} 
  (t : SigmaGraphWitness d H) (i : WheelCycleIndex)
  (a : H.RimDart (numberedWheelCycles i)) (side : Bool)

abbrev GermSunRelabelling := (smoothedSigmaRimGermGraph t i a side).swapBoundary.RowRelabelling
  (Hypergraph.sunSystem (wheelCycles i).length (wheelCycles i).length_ge_three (fun _ => 0))

variable (m : GermSunRelabelling t i a side)

@[reducible] noncomputable def germSunInitialGraph :
    PortGraph (sunPresentation (wheelCycles i).length (fun _ => 0))
      [] (((closedSigmaRimCircuit H i a).frontierWord (!side)).map m.edge).reverse :=
  m.graph.topBottomGraph

noncomputable def germSunInitialPorts :
    (smoothedSigmaRimGermGraph t i a side).swapBoundary.Dart ≃ (germSunInitialGraph t i a side m).Dart :=
  m.ports.trans m.graph.topBottomPorts

theorem germSunInitialPorts_top (j : Fin ((closedSigmaRimCircuit H i a).frontierWord (!side)).length) :
    germSunInitialPorts t i a side m (.top j) =
      .bottom (PortGraph.reverseWordIndex (((closedSigmaRimCircuit H i a).frontierWord (!side)).map m.edge)
        (mapWordIndex m.edge ((closedSigmaRimCircuit H i a).frontierWord (!side)) j)) := rfl

theorem germSunInitialPorts_label (x : (smoothedSigmaRimGermGraph t i a side).swapBoundary.Dart) :
    Port.label (germSunInitialGraph t i a side m).jointLabel (germSunInitialPorts t i a side m x) =
      m.edge (Port.label (smoothedSigmaRimGermGraph t i a side).swapBoundary.jointLabel x) :=
  (m.graph.topBottomPorts_label _).trans (m.ports_label x)

theorem germSunInitialPorts_twin (x : (smoothedSigmaRimGermGraph t i a side).swapBoundary.Dart) :
    (germSunInitialGraph t i a side m).pairing.twin (germSunInitialPorts t i a side m x) =
      germSunInitialPorts t i a side m ((smoothedSigmaRimGermGraph t i a side).swapBoundary.pairing.twin x) :=
  (m.graph.topBottom_pairing _).trans (congrArg m.graph.topBottomPorts (m.ports_twin x))

theorem germSunInitialPorts_rotation (x : (smoothedSigmaRimGermGraph t i a side).swapBoundary.Dart) :
    (germSunInitialGraph t i a side m).rotation (germSunInitialPorts t i a side m x) =
      germSunInitialPorts t i a side m ((smoothedSigmaRimGermGraph t i a side).swapBoundary.rotation x) :=
  (m.graph.topBottom_rotation _).trans (congrArg m.graph.topBottomPorts (m.ports_rotation x))

theorem germSunInitialGraph_hub_card : Fintype.card (germSunInitialGraph t i a side m).Hub =
    Fintype.card (smoothedSigmaRimGermGraph t i a side).Hub := rfl

theorem germSunInitialGraph_sign : (germSunInitialGraph t i a side m).sign = 0 :=
  m.sign_zero (fun _ => rfl)

theorem germSunInitialGraph_euler :
    eulerDefect (germSunInitialGraph t i a side m).pairing.perm
      (germSunInitialGraph t i a side m).circuitStep = 0 := by
  apply (m.graph.topBottom_eulerDefect.trans m.eulerDefect).trans
  exact (smoothedSigmaRimGermGraph t i a side).swapBoundary.rotationEuler_saturated_iff.mp
    ((smoothedSigmaRimGermGraph t i a side).swapBoundary_rotationEuler
      ((closedSigmaRimCircuit H i a).germGraph_rotationEuler
        (t.dualEuler) side))

theorem germSunInitialGraph_noncrossing : (germSunInitialGraph t i a side m).BoundaryNoncrossing :=
  m.graph.topBottom_boundaryNoncrossing (m.noncrossing
    ((smoothedSigmaRimGermGraph t i a side).forwardBottom_swapBoundary_noncrossing
      ((closedSigmaRimCircuit H i a).germGraph_boundaryNext_bottom
        (t.dualEuler) side)))

theorem germSunInitialGraph_sees : (germSunInitialGraph t i a side m).BoundarySeesComponents :=
  m.graph.topBottom_boundarySeesComponents (m.sees
    ((smoothedSigmaRimGermGraph t i a side).forwardBottom_swapBoundary_sees
      ((closedSigmaRimCircuit H i a).germGraph_boundaryNext_bottom
        (t.dualEuler) side)))

theorem germSunInitialGraph_connected : ∀ x y : (germSunInitialGraph t i a side m).Dart,
    Connected (germSunInitialGraph t i a side m).rotation
      (germSunInitialGraph t i a side m).pairing.perm x y := by
  intro x y
  obtain ⟨x, rfl⟩ := (germSunInitialPorts t i a side m).surjective x
  obtain ⟨y, rfl⟩ := (germSunInitialPorts t i a side m).surjective y
  apply (connected_congr
    (smoothedSigmaRimGermGraph t i a side).swapBoundary.rotation
    (smoothedSigmaRimGermGraph t i a side).swapBoundary.pairing.perm
    (germSunInitialGraph t i a side m).rotation
    (germSunInitialGraph t i a side m).pairing.perm (germSunInitialPorts t i a side m)
    (germSunInitialPorts_rotation t i a side m) (germSunInitialPorts_twin t i a side m) x y).mp
  exact (smoothedSigmaRimGermGraph t i a side).swapBoundary_connected
    ((closedSigmaRimCircuit H i a).germGraph_connected
      (t.dualEuler) side) x y

theorem germSunInitialGraph_noJoints [IsEmpty H.Joint] : IsEmpty (germSunInitialGraph t i a side m).Joint :=
  inferInstanceAs (IsEmpty (smoothedSigmaRimGermGraph t i a side).Joint)

noncomputable def germSunInitialQuad
    (q : (smoothedSigmaRimGermGraph t i a side).swapBoundary.BoundaryQuadPath) :
    (germSunInitialGraph t i a side m).BoundaryQuadPath := (m.quadPath q).topBottom

theorem germSunInitialQuad_firstDart
    (q : (smoothedSigmaRimGermGraph t i a side).swapBoundary.BoundaryQuadPath) :
    (germSunInitialQuad t i a side m q).firstDart = germSunInitialPorts t i a side m q.firstDart :=
  (m.quadPath q).topBottom_firstDart.trans (congrArg m.graph.topBottomPorts (m.quadPath_firstDart q))

theorem germSunInitialQuad_middleDart
    (q : (smoothedSigmaRimGermGraph t i a side).swapBoundary.BoundaryQuadPath) :
    (germSunInitialQuad t i a side m q).middleDart = germSunInitialPorts t i a side m q.middleDart := rfl

theorem germSunInitialQuad_lastDart
    (q : (smoothedSigmaRimGermGraph t i a side).swapBoundary.BoundaryQuadPath) :
    (germSunInitialQuad t i a side m q).lastDart = germSunInitialPorts t i a side m q.lastDart := rfl

theorem germSunInitialGraph_minimal
    (hw : ((closedSigmaRimCircuit H i a).frontierWord (!side)).map m.edge =
      closedSigmaRimSunFrontierWord H i a (!side))
    (e : Diagram (sunPresentation (wheelCycles i).length (fun _ => 0))
      [] (closedSigmaRimSunFrontierWord H i a (!side)))
    (hn : e.size = Fintype.card (smoothedSigmaRimGermGraph t i a side).Hub) (hm : e.Minimal) :
    (germSunInitialGraph t i a side m).SunMinimalState where
  euler := germSunInitialGraph_euler t i a side m
  noncrossing := germSunInitialGraph_noncrossing t i a side m
  sees := germSunInitialGraph_sees t i a side m
  minimal f := by
    have h := ((e.reverseBottom).sun_characterMinimal_iff.mp hm.reverseBottom.characterMinimal)
      (f.cast rfl (congrArg List.reverse hw))
    rw [Diagram.size_reverseBottom, Diagram.size_cast, hn] at h
    exact h

theorem smoothedSigmaRimGerm_exists_structural_sun [IsEmpty H.Joint]
    (hmin : d.Minimal) (hs : d.sign = 1) (hi : i ≠ oddWheelCycle) :
    ∃ side, ∃ m : GermSunRelabelling t i a side,
      ((closedSigmaRimCircuit H i a).frontierWord (!side)).map m.edge =
        closedSigmaRimSunFrontierWord H i a (!side) ∧
      (∀ x : (smoothedSigmaRimGermGraph t i a side).swapBoundary.Dart,
        (numberedWheelCycleRetraction i).retract.edge
          (Port.label (smoothedSigmaRimGermGraph t i a side).swapBoundary.jointLabel x) =
            some (Port.label (germSunInitialGraph t i a side m).jointLabel
              (germSunInitialPorts t i a side m x))) ∧
      (∑ h : (germSunInitialGraph t i a side m).Hub,
        ([(germSunInitialGraph t i a side m).hubLabel h] : Multiset (Fin (wheelCycles i).length))) =
        (∑ h : (smoothedSigmaRimGermGraph t i a side).Hub,
          ([(smoothedSigmaRimGermGraph t i a side).hubLabel h] : Multiset (Fin 1417152))).filterMap
            (numberedWheelCycleRetraction i).retract.vertex ∧
      (germSunInitialGraph t i a side m).SunMinimalState ∧
      (smoothedSigmaRimGermGraph t i a side).sign = 0 := by
  obtain ⟨side, e, hl, hn, _, hm, _, hz⟩ :=
    smoothedSigmaRimGerm_exists_minimal_sun_diagram_with_sign t hmin hs i a hi
  let G := smoothedSigmaRimGermGraph t i a side
  let : IsEmpty G.swapBoundary.Joint := ⟨fun j => isEmptyElim (j.val : H.Joint)⟩
  let φ : numberedSystem.hypergraph.GeneralizedHom
      (Hypergraph.sunSystem (wheelCycles i).length (wheelCycles i).length_ge_three (fun _ => 0)).hypergraph :=
    (numberedWheelCycleRetraction i).retract
  have hc : ((∑ h : G.Hub, ([G.hubLabel h] : Multiset (Fin 1417152))).filterMap φ.vertex).card =
      Fintype.card G.Hub := (congrArg Multiset.card hl).symm.trans hn
  have hV : ∀ h : G.swapBoundary.Hub, ∃ r, φ.vertex (G.swapBoundary.hubLabel h) = some r :=
    G.hubs_retained_of_filterMap_card φ.vertex hc
  let fallback : Fin (wheelCycles i).length ⊕ Fin (wheelCycles i).length :=
    .inl ⟨0, lt_of_lt_of_le (by decide +kernel : 0 < 3) (wheelCycles i).length_ge_three⟩
  let m := PortGraph.RowRelabelling.ofRetained G.swapBoundary φ fallback hV
  have hTop : ∀ z ∈ (closedSigmaRimCircuit H i a).frontierWord (!side), ∃ f, φ.edge z = some f := by
    intro z hz
    obtain ⟨j, rfl⟩ := closedSigmaRimFrontierWord_in_neighbourhood H i a (!side) z hz
    exact ⟨j, (numberedWheelCycleRetraction i).edge_leftInverse j⟩
  have hw := PortGraph.RowRelabelling.retained_word_map G.swapBoundary φ fallback hV hTop
  refine ⟨side, m, hw, ?_, PortGraph.RowRelabelling.ofRetained_hub_relations G.swapBoundary φ fallback hV,
    germSunInitialGraph_minimal t i a side m hw e hn hm, hz⟩
  intro x
  rw [germSunInitialPorts_label]
  have hp := PortGraph.RowRelabelling.ofRetained_port_image G.swapBoundary φ fallback hV hTop (by simp) x
  rw [PortGraph.RowRelabelling.ports_label] at hp
  exact hp

end ThomGame.Construction
