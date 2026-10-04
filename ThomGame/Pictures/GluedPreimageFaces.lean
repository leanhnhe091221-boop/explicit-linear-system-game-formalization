module

public import ThomGame.Pictures.ReducedGluingClassification
public import ThomGame.Pictures.RegionCircuitRecovery

/-!
# Faciality of a target circuit with an exact input preimage

An input preimage need not be a label cover. The exact indexed-port
correspondence and the smoothing trace identify its face orbit in the
target. For a complementary-region preimage, faciality of its recovered
original circuit therefore implies faciality of the target circuit.
-/

@[expose] public section
namespace ThomGame.Pictures

open PortGraph

variable {R S : Type*} {P : InvolutionPresentation R S} {w : List S}
  {G : PortGraph P [] w} {H : PortGraph P w []}

namespace ClosedGluingReduction

variable (d : ClosedGluingReduction G H) (C : d.graph.SimpleCircuit)
  (D : G.SimpleCircuit) (hlen : D.length = C.length)
  (hp : ∀ x : Fin D.length × Bool, compLeftEmbedding G H (D.port x) =
    d.trace.portEmbedding (C.port (finCongr hlen x.1, x.2)))

include hp in
theorem leftPreimage_label (x : Fin D.length × Bool) :
    Port.label G.jointLabel (D.port x) =
      Port.label d.graph.jointLabel (C.port (finCongr hlen x.1, x.2)) := by
  rw [← compLeftEmbedding_label G H, hp]
  exact d.trace.portLabel _

include hp in
theorem boundsFaceOrbit_of_leftPreimage (side : Bool) (hf : D.BoundsFaceOrbit side) :
    C.BoundsFaceOrbit side := by
  have hf' := D.boundsFaceOrbit_compLeft G H side hf
  have hz : finCongr hlen (0 : Fin D.length) = (0 : Fin C.length) := by
    apply Fin.ext
    simp
  have hp0 := hp (0, side)
  rw [hz] at hp0
  intro x
  have hi : d.graph.circuitStep.SameCycle x (C.port (0, side)) ↔
      (G.comp H).circuitStep.SameCycle (d.trace.portEmbedding x)
        ((D.compLeft G H).port (0, side)) := by
    rw [← d.graph.circuit_eq_iff, d.trace.sameCircuit_iff, (G.comp H).circuit_eq_iff,
      D.compLeft_port G H (0, side), hp0]
  rw [hi, hf']
  constructor
  · rintro ⟨i, he⟩
    rw [D.compLeft_port G H (i, side), hp] at he
    exact ⟨finCongr hlen i, d.trace.portEmbedding.injective he⟩
  · rintro ⟨i, rfl⟩
    obtain ⟨j, rfl⟩ := (finCongr hlen).surjective i
    exact ⟨j, (D.compLeft_port G H (j, side)).trans (hp (j, side))⟩

end ClosedGluingReduction

namespace PortGraph.SimpleCircuit

open RibbonConnectivity

variable {G : PortGraph P [] []} (B : G.SimpleCircuit)
  (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
    2 * Nat.card (Component G.circuitStep G.pairing.perm)) (s : Bool)
  {N : PortGraph P (B.frontierWord s) []}
  (d : ClosedGluingReduction (B.regionGraph hEuler s).swapBoundary N)
  (C : d.graph.SimpleCircuit)
  (D : (B.regionGraph hEuler s).swapBoundary.SimpleCircuit) (hlen : D.length = C.length)
  (hp : ∀ x : Fin D.length × Bool,
    compLeftEmbedding (B.regionGraph hEuler s).swapBoundary N (D.port x) =
      d.trace.portEmbedding (C.port (finCongr hlen x.1, x.2)))

include hp in
theorem recoveredExteriorPreimage_label (x : Fin D.length × Bool) :
    Port.label G.jointLabel ((B.recoverSwappedRegionCircuit hEuler s D).port x) =
      Port.label d.graph.jointLabel (C.port (finCongr hlen x.1, x.2)) :=
  (B.recoverSwappedRegionCircuit_label hEuler s D x).trans (d.leftPreimage_label C D hlen hp x)

include hp in
theorem face_of_recoveredExteriorPreimage (side : Bool)
    (hf : (B.recoverSwappedRegionCircuit hEuler s D).BoundsFaceOrbit side) :
    C.BoundsFaceOrbit side :=
  d.boundsFaceOrbit_of_leftPreimage C D hlen hp side
    ((B.recoverSwappedRegionCircuit_face_iff hEuler s D side).mp hf)

include hp in
theorem recoveredExteriorPreimage_nonfacial (hn : ¬ ∃ side, C.BoundsFaceOrbit side) :
    ¬ ∃ side, (B.recoverSwappedRegionCircuit hEuler s D).BoundsFaceOrbit side := by
  rintro ⟨side, hf⟩
  exact hn ⟨side, B.face_of_recoveredExteriorPreimage hEuler s d C D hlen hp side hf⟩

theorem exists_original_of_exterior_preimage (hleft : d.HasLeftPreimage C) :
    ∃ E : G.SimpleCircuit, ∃ he : E.length = C.length,
      (∀ x : Fin E.length × Bool, Port.label G.jointLabel (E.port x) =
        Port.label d.graph.jointLabel (C.port (finCongr he x.1, x.2))) ∧
      (∀ x : Fin E.length × Bool, ¬ B.GermVertex (!s) (E.port x).vertex) ∧
      (∀ side, E.BoundsFaceOrbit side → C.BoundsFaceOrbit side) := by
  obtain ⟨D, hlen, hp⟩ := hleft
  exact ⟨B.recoverSwappedRegionCircuit hEuler s D, hlen,
    B.recoveredExteriorPreimage_label hEuler s d C D hlen hp,
    B.recoverSwappedRegionCircuit_not_germ hEuler s D,
    B.face_of_recoveredExteriorPreimage hEuler s d C D hlen hp⟩

end PortGraph.SimpleCircuit
end ThomGame.Pictures
