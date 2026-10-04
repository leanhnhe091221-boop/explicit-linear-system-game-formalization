module

public import ThomGame.Construction.WheelGermQuadLabels
public import ThomGame.Pictures.BoundaryQuadTransport

/-!
# The normalized germ has the original top boundary and quadrilaterals

Reversing the lower boundary back to the top cancels the initial index
reversal exactly. The complete port equivalence fixes each original
boundary position. Original quadrilateral certificates, edge pairs and
Sigma labels are retained in the actual graph used for oriented gluing.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures

variable {d : SigmaDiagram [] []} {H : SigmaGraph [] []} 
  (t : SigmaGraphWitness d H) (i : WheelCycleIndex)
  (a : H.RimDart (numberedWheelCycles i)) (side : Bool)
  (m : GermSunRelabelling t i a side)
  (hw : ((closedSigmaRimCircuit H i a).frontierWord (!side)).map m.edge =
    closedSigmaRimSunFrontierWord H i a (!side))
  {K : PortGraph (sunPresentation (wheelCycles i).length (fun _ => 0))
    [] (((closedSigmaRimCircuit H i a).frontierWord (!side)).map m.edge).reverse}
  (q : PortGraph.SunSwitchTrace (germSunInitialGraph t i a side m) K)
  (L : IncludedWheelSun i K ((closedSigmaRimCircuit H i a).frontierWord (!side)).reverse)

noncomputable def germSunTopPorts :
    (smoothedSigmaRimGermGraph t i a side).swapBoundary.Dart ≃ L.topGraph.Dart :=
  (germSunNormalizedPorts t i a side m q L).trans L.topPorts

theorem germSunTopPorts_top (j : Fin ((closedSigmaRimCircuit H i a).frontierWord (!side)).length) :
    germSunTopPorts t i a side m q L (.top j) = .top j := by
  change L.topPorts (L.ports (q.ports (germSunInitialPorts t i a side m (.top j)))) = _
  rw [germSunInitialPorts_top]
  have hq (k) : q.ports (.bottom k) = .bottom k := q.ports_boundaryDart (.inr k)
  rw [hq, L.bottom, L.topPorts_bottom]
  apply congrArg Port.top
  apply Fin.ext
  simp only [PortGraph.reverseWordIndex, mapWordIndex, Equiv.trans_apply,
    finCongr_apply, Fin.val_cast, Fin.revPerm_apply, Fin.val_rev, List.length_reverse, List.length_map]
  have hj := j.isLt
  omega

theorem germSunTopPorts_boundaryDart
    (j : PortGraph.BoundaryIndex ((closedSigmaRimCircuit H i a).frontierWord (!side)) []) :
    germSunTopPorts t i a side m q L ((smoothedSigmaRimGermGraph t i a side).swapBoundary.boundaryDart j) =
      L.topGraph.boundaryDart j := by
  cases j with
  | inl j => exact germSunTopPorts_top t i a side m q L j
  | inr j => exact j.elim0

noncomputable def germSunTopQuad
    (p : (smoothedSigmaRimGermGraph t i a side).swapBoundary.BoundaryQuadPath) : L.topGraph.BoundaryQuadPath :=
  (germSunNormalizedQuad t i a side m hw q L p).bottomTop.castBoundary (List.reverse_reverse _) rfl

theorem germSunTopQuad_firstDart
    (p : (smoothedSigmaRimGermGraph t i a side).swapBoundary.BoundaryQuadPath) :
    (germSunTopQuad t i a side m hw q L p).firstDart = germSunTopPorts t i a side m q L p.firstDart :=
  ((germSunNormalizedQuad t i a side m hw q L p).bottomTop.castBoundary_firstDart _ _).trans
    (congrArg (L.graph.bottomTopGraph.castPorts _ _)
      (((germSunNormalizedQuad t i a side m hw q L p).bottomTop_firstDart).trans
        (congrArg L.graph.bottomTopPorts (germSunNormalizedQuad_firstDart t i a side m hw q L p))))

theorem germSunTopQuad_middleDart
    (p : (smoothedSigmaRimGermGraph t i a side).swapBoundary.BoundaryQuadPath) :
    (germSunTopQuad t i a side m hw q L p).middleDart = germSunTopPorts t i a side m q L p.middleDart :=
  ((germSunNormalizedQuad t i a side m hw q L p).bottomTop.castBoundary_middleDart _ _).trans
    (congrArg (L.graph.bottomTopGraph.castPorts _ _)
      (((germSunNormalizedQuad t i a side m hw q L p).bottomTop_middleDart).trans
        (congrArg L.graph.bottomTopPorts (germSunNormalizedQuad_middleDart t i a side m hw q L p))))

theorem germSunTopQuad_lastDart
    (p : (smoothedSigmaRimGermGraph t i a side).swapBoundary.BoundaryQuadPath) :
    (germSunTopQuad t i a side m hw q L p).lastDart = germSunTopPorts t i a side m q L p.lastDart :=
  ((germSunNormalizedQuad t i a side m hw q L p).bottomTop.castBoundary_lastDart _ _).trans
    (congrArg (L.graph.bottomTopGraph.castPorts _ _)
      (((germSunNormalizedQuad t i a side m hw q L p).bottomTop_lastDart).trans
        (congrArg L.graph.bottomTopPorts (germSunNormalizedQuad_lastDart t i a side m hw q L p))))

theorem germSunTopQuad_start
    (p : (smoothedSigmaRimGermGraph t i a side).swapBoundary.BoundaryQuadPath) :
    (germSunTopQuad t i a side m hw q L p).start = p.start := by
  apply L.topGraph.boundaryDart.injective
  exact (germSunTopQuad_firstDart t i a side m hw q L p).trans
    (germSunTopPorts_boundaryDart t i a side m q L p.start)

include hw in
theorem germSunTopQuad_pairs
    (p : (smoothedSigmaRimGermGraph t i a side).swapBoundary.BoundaryQuadPath)
    (x : (smoothedSigmaRimGermGraph t i a side).swapBoundary.Dart)
    (hx : x ∈ [p.firstDart, p.middleDart, p.lastDart]) :
    L.topGraph.pairing.twin (germSunTopPorts t i a side m q L x) =
      germSunTopPorts t i a side m q L ((smoothedSigmaRimGermGraph t i a side).swapBoundary.pairing.twin x) :=
  (L.topPorts_pairing _).trans (congrArg L.topPorts (germSunNormalizedQuad_pairs t i a side m hw q L p x hx))

theorem germSunTopQuad_finish
    (p : (smoothedSigmaRimGermGraph t i a side).swapBoundary.BoundaryQuadPath) :
    (germSunTopQuad t i a side m hw q L p).finish = p.finish := by
  apply L.topGraph.boundaryDart.injective
  rw [← (germSunTopQuad t i a side m hw q L p).last_twin, germSunTopQuad_lastDart,
    germSunTopQuad_pairs t i a side m hw q L p p.lastDart (by simp), p.last_twin]
  exact germSunTopPorts_boundaryDart t i a side m q L p.finish

theorem germSunTopQuad_labels
    (hp : ∀ x : (smoothedSigmaRimGermGraph t i a side).swapBoundary.Dart,
      (numberedWheelCycleRetraction i).retract.edge
        (Port.label (smoothedSigmaRimGermGraph t i a side).swapBoundary.jointLabel x) =
          some (m.edge (Port.label (smoothedSigmaRimGermGraph t i a side).swapBoundary.jointLabel x)))
    (p : (smoothedSigmaRimGermGraph t i a side).swapBoundary.BoundaryQuadPath)
    (x : (smoothedSigmaRimGermGraph t i a side).swapBoundary.Dart)
    (hx : x ∈ [p.firstDart, p.middleDart, p.lastDart]) :
    Port.label L.topGraph.jointLabel (germSunTopPorts t i a side m q L x) =
      Port.label (smoothedSigmaRimGermGraph t i a side).swapBoundary.jointLabel x :=
  (L.topPorts_label _).trans (germSunNormalizedQuad_labels t i a side m q L hp p x hx)

end ThomGame.Construction
