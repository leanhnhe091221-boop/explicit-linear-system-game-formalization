module

public import ThomGame.Pictures.GermSeamCircuit
public import ThomGame.Pictures.LiftedFaceReplacement

/-!
# A preserved original boundary edge meets the actual reduced face

The replacement fixes both ports at every numbered seam. If the target
edge is adjacent to that seam before smoothing, the transported original
face contains it as an unoriented edge. The exact smoothing result keeps
this membership, even if only its opposite face orientation survives.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

variable {R S : Type*} {P : InvolutionPresentation R S} {v : List S}
  {E : PortGraph P [] v} {G N : PortGraph P v []}

namespace BoundaryQuadReplacement

variable (r : G.BoundaryQuadReplacement N)

theorem gluedPorts_seam (j : Fin v.length) (b : Bool) :
    r.gluedPorts E (.joint (.inr j) b) = .joint (.inr j) b := by
  cases b
  · exact r.gluedPorts_left E (.bottom j)
  · have he := r.gluedPorts_right E (.top j)
    have hb : r.ports (.top j) = (.top j : N.Dart) := r.boundary (.inl j)
    rw [hb] at he
    exact he

variable (C : (E.comp G).SimpleCircuit) (side : Bool) (hs : C.SupportedByQuads side)

theorem crossingCircuit_marked_iff (x : (E.comp G).Dart) :
    (r.crossingCircuit C side hs).Marked (r.gluedPorts E x) ↔ C.Marked x := by
  constructor
  · rintro ⟨i, hi⟩
    rw [r.crossingCircuit_port] at hi
    exact ⟨i, (r.gluedPorts E).injective hi⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, r.crossingCircuit_port C side hs i⟩

variable [IsEmpty G.Joint] [IsEmpty N.Joint] (hf : C.BoundsFaceOrbit side)
  (d : ThomGame.Pictures.ClosedGluingReduction E N)
  (i₀ : Fin C.length) (ha : (E.comp G).Terminal (C.port (i₀, side)))

theorem reducedCrossingCircuit_marked_iff (x : d.graph.Dart) :
    (r.reducedCrossingCircuit C side hs hf d i₀ ha).Marked x ↔
      (r.crossingCircuit C side hs).Marked (d.trace.portEmbedding x) :=
  (r.crossingCircuit C side hs).reducedFacialCircuit_marked_iff side
    (r.crossingCircuit_face C side hs hf) d.trace i₀ (r.crossingCircuit_terminal C side hs i₀ ha) x

end BoundaryQuadReplacement

namespace SimpleCircuit

open RibbonConnectivity

variable {G : PortGraph P [] []} [IsEmpty G.Joint] (C : G.SimpleCircuit)
  (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
    2 * Nat.card (Component G.circuitStep G.pairing.perm))
  (hc : ∀ x y : G.Vertex, G.Reachable x y) (s : Bool)
  (D : G.SimpleCircuit) (side : Bool) (hf : D.BoundsFaceOrbit side)
  (hsup : (C.orientedLiftedCircuit hEuler hc s D side hf).SupportedByQuads false)
  {N : PortGraph P (C.frontierWord (!s)) []} [IsEmpty N.Joint]
  (r : (C.germGraph hEuler s).swapBoundary.BoundaryQuadReplacement N)
  (red : ThomGame.Pictures.ClosedGluingReduction (C.regionGraph hEuler (!s)).swapBoundary N)

include hsup r in
theorem liftedFace_replacement_meets_seam
    (j : Fin (C.frontierWord (!s)).length)
    (hj : D.Marked (C.boundaryEnumeration (!s) j).val) (b : Bool)
    (x : red.graph.Dart)
    (hx : ((C.regionGraph hEuler (!s)).swapBoundary.comp N).pairing.twin
      (red.trace.portEmbedding x) = .joint (.inr j) b) :
    ∃ F : red.graph.SimpleCircuit, F.BoundsFaceOrbit false ∧ F.Marked x ∧
      ∀ k : Fin F.length, ∃ l : Fin D.length,
        Port.label red.graph.jointLabel (F.dart k) = Port.label G.jointLabel (D.port (l, side)) := by
  let : IsEmpty (C.germGraph hEuler s).swapBoundary.Joint := ⟨fun j => isEmptyElim j.val⟩
  let E := (C.regionGraph hEuler (!s)).swapBoundary
  let L := C.orientedLiftedCircuit hEuler hc s D side hf
  have hface : L.BoundsFaceOrbit false := C.orientedLiftedCircuit_face hEuler hc s D side hf
  obtain ⟨k₀, hk₀, _⟩ := C.orientedLiftedCircuit_complete hEuler hc s D side hf 0
  have ht₀ : (C.orientedGluedGraph hEuler s).Terminal (L.port (k₀, false)) := by
    change (C.orientedGluedGraph hEuler s).Terminal (L.dart k₀)
    rw [hk₀]
    exact C.orientedLiftPort_terminal hEuler hc s (D.port (0, side))
  let F := r.reducedCrossingCircuit L false hsup hface red k₀ ht₀
  refine ⟨F, r.reducedCrossingCircuit_face L false hsup hface red k₀ ht₀, ?_, ?_⟩
  · apply (r.reducedCrossingCircuit_marked_iff L false hsup hface red k₀ ht₀ x).mpr
    apply ((r.crossingCircuit L false hsup).marked_twin_iff _).mp
    rw [hx, ← r.gluedPorts_seam (E := E) j b, r.crossingCircuit_marked_iff]
    exact C.orientedLiftedCircuit_marked_seam hEuler s hc D side hf j hj b
  · intro k
    obtain ⟨l, _, hl⟩ := r.reducedCrossingCircuit_label L false hsup hface red k₀ ht₀ k
    obtain ⟨m, hm⟩ := (hf _).mp (C.orientedLiftedCircuit_source hEuler hc s D side hf l)
    refine ⟨m, hl.trans ?_⟩
    exact (C.orientedFaceProjection_label hEuler s (L.dart l)).symm.trans
      (congrArg (Port.label G.jointLabel) hm.symm)

end SimpleCircuit
end ThomGame.Pictures.PortGraph
