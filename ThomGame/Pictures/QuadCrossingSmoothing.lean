module

public import ThomGame.Pictures.QuadCrossingCircuit
public import ThomGame.Pictures.SmoothedFacialCircuit
public import ThomGame.Pictures.ClosedGluingCovers

/-!
# Crossing facial circuits survive full smoothing of the replacement

After the actual seam composition, suppress all joints. A nonempty
retained part of the old supported facial circuit becomes a simple
facial circuit in that specific smoothing result. Its darts correspond
exactly to the old surviving face darts, with their original labels.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

variable {R S : Type*} {P : InvolutionPresentation R S} {v : List S}
  (E : PortGraph P [] v) (G : PortGraph P v [])

theorem compRight_terminal_iff [IsEmpty G.Joint] (x : G.Dart) :
    (E.comp G).Terminal (compRightEmbedding E G x) ↔ ¬ G.IsBoundary x := by
  cases x with
  | top j => change False ↔ ¬ True; simp
  | bottom j => exact j.elim0
  | hub h j => change True ↔ ¬ False; simp
  | joint j b => exact isEmptyElim j

theorem SimpleCircuit.exists_terminal_of_quad_crossing (C : (E.comp G).SimpleCircuit) (side : Bool)
    (hs : C.SupportedByQuads side) (hf : C.BoundsFaceOrbit side)
    (hx : ∃ i x, C.port (i, side) = compRightEmbedding E G x) :
    ∃ i, (E.comp G).Terminal (C.port (i, side)) := by
  obtain ⟨i, x, hx⟩ := hx
  obtain ⟨p, hp⟩ := hs i x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · have hn := ((hf _).mpr ⟨i, rfl⟩).apply_left
    obtain ⟨j, hj⟩ := (hf _).mp hn
    have hstep : (E.comp G).circuitStep (compRightEmbedding E G p.firstDart) =
        compRightEmbedding E G p.middleDart := by
      have hnb : ¬ G.IsBoundary (G.circuitStep p.firstDart) := by rw [p.first_step]; exact id
      exact (compRightEmbedding_step E G p.firstDart hnb).trans
        (congrArg (compRightEmbedding E G) p.first_step)
    rw [hx, hstep] at hj
    refine ⟨j, ?_⟩
    rw [hj]
    trivial
  · refine ⟨i, ?_⟩
    rw [hx]
    trivial
  · refine ⟨i, ?_⟩
    rw [hx]
    trivial

namespace BoundaryQuadReplacement

variable {G} {H : PortGraph P v []} (r : G.BoundaryQuadReplacement H)
  [IsEmpty G.Joint] [IsEmpty H.Joint]

theorem gluedPorts_terminal_iff (x : (E.comp G).Dart) :
    (E.comp H).Terminal (r.gluedPorts E x) ↔ (E.comp G).Terminal x := by
  obtain ⟨x, rfl⟩ := (compPorts E G).surjective x
  rcases x with x | x
  · change (E.comp H).Terminal (r.gluedPorts E (compLeftEmbedding E G x)) ↔ _
    rw [r.gluedPorts_left]
    cases x with
    | top j => exact j.elim0
    | bottom j => rfl
    | hub h j => rfl
    | joint j b => rfl
  · change (E.comp H).Terminal (r.gluedPorts E (compRightEmbedding E G x)) ↔
      (E.comp G).Terminal (compRightEmbedding E G x)
    rw [r.gluedPorts_right, compRight_terminal_iff, compRight_terminal_iff, r.boundary_iff]

variable {E} (C : (E.comp G).SimpleCircuit) (side : Bool) (h : C.SupportedByQuads side)
  (hf : C.BoundsFaceOrbit side) (d : ClosedGluingReduction E H)
  (i₀ : Fin C.length) (ha : (E.comp G).Terminal (C.port (i₀, side)))

include ha in
theorem crossingCircuit_terminal :
    (E.comp H).Terminal ((r.crossingCircuit C side h).port (i₀, side)) := by
  rw [r.crossingCircuit_port]
  exact (r.gluedPorts_terminal_iff E _).mpr ha

@[reducible] noncomputable def reducedCrossingCircuit : d.graph.SimpleCircuit :=
  (r.crossingCircuit C side h).reducedFacialCircuit side (r.crossingCircuit_face C side h hf)
    d.trace i₀ (r.crossingCircuit_terminal C side h i₀ ha)

theorem reducedCrossingCircuit_face : (r.reducedCrossingCircuit C side h hf d i₀ ha).BoundsFaceOrbit false :=
  (r.crossingCircuit C side h).reducedFacialCircuit_face side _ d.trace i₀ _

theorem reducedCrossingCircuit_dart_original
    (j : Fin (r.reducedCrossingCircuit C side h hf d i₀ ha).length) :
    ∃ i, d.trace.portEmbedding ((r.reducedCrossingCircuit C side h hf d i₀ ha).dart j) =
      r.gluedPorts E (C.port (i, side)) := by
  obtain ⟨i, hi⟩ := (r.crossingCircuit C side h).reducedFacialCircuit_dart_original side _ d.trace i₀ _ j
  exact ⟨i, hi.trans (r.crossingCircuit_port C side h (i, side))⟩

theorem reducedCrossingCircuit_complete (i : Fin C.length) (hi : (E.comp G).Terminal (C.port (i, side))) :
    ∃! j : Fin (r.reducedCrossingCircuit C side h hf d i₀ ha).length,
      d.trace.portEmbedding ((r.reducedCrossingCircuit C side h hf d i₀ ha).dart j) =
        r.gluedPorts E (C.port (i, side)) := by
  simpa only [r.crossingCircuit_port] using
    (r.crossingCircuit C side h).reducedFacialCircuit_complete side _ d.trace i₀ _ i
      (r.crossingCircuit_terminal C side h i hi)

theorem reducedCrossingCircuit_label
    (j : Fin (r.reducedCrossingCircuit C side h hf d i₀ ha).length) :
    ∃ i, d.trace.portEmbedding ((r.reducedCrossingCircuit C side h hf d i₀ ha).dart j) =
        r.gluedPorts E (C.port (i, side)) ∧
      Port.label d.graph.jointLabel ((r.reducedCrossingCircuit C side h hf d i₀ ha).dart j) =
        Port.label (E.comp G).jointLabel (C.port (i, side)) := by
  obtain ⟨i, hi⟩ := r.reducedCrossingCircuit_dart_original C side h hf d i₀ ha j
  refine ⟨i, hi, ?_⟩
  rw [← d.trace.portLabel, hi]
  exact r.supported_face_label C side h i

end BoundaryQuadReplacement
end ThomGame.Pictures.PortGraph
