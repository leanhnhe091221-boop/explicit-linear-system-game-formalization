module

public import ThomGame.Pictures.LiftedGermFaces
public import ThomGame.Pictures.QuadCrossingSmoothing

/-!
# Original ports recovered after a supported lifted-face replacement

The lift of every original face has an original terminal port, including
faces entirely outside the germ. Support is the only local replacement
condition; later theorems derive it for crossing and exterior faces.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open RibbonConnectivity

variable {R S : Type*} {P : InvolutionPresentation R S} {G : PortGraph P [] []}
  [IsEmpty G.Joint] (C : G.SimpleCircuit)
  (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
    2 * Nat.card (Component G.circuitStep G.pairing.perm))
  (hc : ∀ x y : G.Vertex, G.Reachable x y) (s : Bool)
  (D : G.SimpleCircuit) (side : Bool) (hf : D.BoundsFaceOrbit side)
  (hsup : (C.orientedLiftedCircuit hEuler hc s D side hf).SupportedByQuads false)
  {N : PortGraph P (C.frontierWord (!s)) []} [IsEmpty N.Joint]
  (r : (C.germGraph hEuler s).swapBoundary.BoundaryQuadReplacement N)
  (red : ClosedGluingReduction (C.regionGraph hEuler (!s)).swapBoundary N)

include hsup in
theorem liftedFace_replacement_survives :
    ∃ F : red.graph.SimpleCircuit, F.BoundsFaceOrbit false ∧
      (∀ j : Fin F.length, ∃ i : Fin D.length,
        red.trace.portEmbedding (F.dart j) = r.gluedPorts (C.regionGraph hEuler (!s)).swapBoundary
          (C.orientedLiftPort hEuler hc s (D.port (i, side))) ∧
        Port.label red.graph.jointLabel (F.dart j) = Port.label G.jointLabel (D.port (i, side))) ∧
      (∀ i : Fin D.length, ∃! j : Fin F.length,
        red.trace.portEmbedding (F.dart j) = r.gluedPorts (C.regionGraph hEuler (!s)).swapBoundary
          (C.orientedLiftPort hEuler hc s (D.port (i, side)))) := by
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
  · intro j
    obtain ⟨k, hkp, hkl⟩ := r.reducedCrossingCircuit_label L false hsup hface red k₀ ht₀ j
    have ht : (E.comp N).Terminal (r.gluedPorts E (L.port (k, false))) := by
      rw [← hkp]
      exact (red.trace.terminal_iff (F.dart j)).mpr (red.graph.terminal_of_no_junctions (F.dart j))
    have hk := (r.gluedPorts_terminal_iff E (L.port (k, false))).mp ht
    obtain ⟨i, hi⟩ := C.orientedLiftedCircuit_terminal_original hEuler hc s D side hf k hk
    refine ⟨i, hkp.trans (congrArg (r.gluedPorts E) hi), ?_⟩
    exact hkl.trans ((congrArg (Port.label (C.orientedGluedGraph hEuler s).jointLabel) hi).trans
      (C.orientedLiftPort_label hEuler hc s (D.port (i, side))))
  · intro i
    obtain ⟨k, hk, _⟩ := C.orientedLiftedCircuit_complete hEuler hc s D side hf i
    have ht : (E.comp (C.germGraph hEuler s).swapBoundary).Terminal (L.port (k, false)) := by
      change (C.orientedGluedGraph hEuler s).Terminal
        ((C.orientedLiftedCircuit hEuler hc s D side hf).dart k)
      rw [hk]
      exact C.orientedLiftPort_terminal hEuler hc s (D.port (i, side))
    obtain ⟨j, hj, hu⟩ := r.reducedCrossingCircuit_complete L false hsup hface red k₀ ht₀ k ht
    have heq := congrArg (r.gluedPorts E) hk
    exact ⟨j, hj.trans heq, fun k hk => hu k (hk.trans heq.symm)⟩

include hsup in
theorem liftedFace_replacement_survives_equiv :
    ∃ F : red.graph.SimpleCircuit, F.BoundsFaceOrbit false ∧
      F.length = D.length ∧
      ∃ e : Fin F.length ≃ Fin D.length,
        ∀ j : Fin F.length,
          red.trace.portEmbedding (F.dart j) =
            r.gluedPorts (C.regionGraph hEuler (!s)).swapBoundary
              (C.orientedLiftPort hEuler hc s
                (D.port (e j, side))) ∧
          Port.label red.graph.jointLabel (F.dart j) =
            Port.label G.jointLabel (D.port (e j, side)) := by
  classical
  obtain ⟨F, hF, hsource, hcomplete⟩ :=
    C.liftedFace_replacement_survives hEuler hc s D side hf hsup r red
  let γ := C
  let δ := D
  choose f hport hlabel using hsource
  have hfi : Function.Injective f := by
    intro j k hjk
    apply F.dart.injective
    apply red.trace.portEmbedding.injective
    exact (hport j).trans ((congrArg
      (fun l => r.gluedPorts (γ.regionGraph hEuler (!s)).swapBoundary
        (γ.orientedLiftPort hEuler hc s (δ.port (l, side)))) hjk).trans (hport k).symm)
  have hfs : Function.Surjective f := by
    intro i
    obtain ⟨j, hj, _⟩ := hcomplete i
    refine ⟨j, ?_⟩
    have heq := (r.gluedPorts (γ.regionGraph hEuler (!s)).swapBoundary).injective
      ((hport j).symm.trans hj)
    have hpj := congrArg (γ.orientedFaceProjection hEuler s) heq
    have hports : δ.port (f j, side) = δ.port (i, side) :=
      (γ.orientedLiftPort_projection hEuler hc s _).symm.trans
        (hpj.trans (γ.orientedLiftPort_projection hEuler hc s _))
    exact congrArg Prod.fst (δ.port_injective hports)
  let e := Equiv.ofBijective f ⟨hfi, hfs⟩
  refine ⟨F, hF, ?_, e, fun j => ⟨hport j, hlabel j⟩⟩
  simpa only [Fintype.card_fin] using Fintype.card_congr e


end ThomGame.Pictures.PortGraph.SimpleCircuit
