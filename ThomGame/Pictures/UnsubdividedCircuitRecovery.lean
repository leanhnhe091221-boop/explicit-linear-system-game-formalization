module

public import ThomGame.Pictures.SmoothedCircuitCovers
public import ThomGame.Pictures.CircuitLocalEmbedding

/-!
# Recovering circuits whose edges never enter a removed joint

If the original twin of each retained outgoing port is already a
terminal, smoothing did not change that edge. The whole simple circuit
therefore embeds back into the original graph, preserving its indices,
ports, and labels. No facial assumption is used.
-/

@[expose] public section
namespace ThomGame.Pictures

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
  {G H : PortGraph P u v} {cs : List S} [IsEmpty H.Joint]

namespace Smoothing

variable (t : Smoothing G H cs)

theorem portEmbedding_twin_of_terminal (a : H.Dart)
    (ha : G.Terminal (G.pairing.twin (t.portEmbedding a))) :
    t.portEmbedding (H.pairing.twin a) = G.pairing.twin (t.portEmbedding a) := by
  have hT := (t.terminal_iff a).mpr (H.terminal_of_no_junctions a)
  have he : t.liftTerminal ⟨t.portEmbedding a, hT⟩ = a := t.terminalEquiv.symm_apply_apply a
  have ht := t.twin_liftTerminal (t.portEmbedding a) hT ha
  rw [he] at ht
  exact (congrArg t.portEmbedding ht).trans (t.portEmbedding_liftTerminal _)

end Smoothing

namespace PortGraph.SimpleCircuit

variable (C : H.SimpleCircuit) (t : Smoothing G H cs)
  (hT : ∀ i : Fin C.length, G.Terminal (G.pairing.twin (t.portEmbedding (C.dart i))))

@[reducible] noncomputable def recoverUnsubdivided : G.SimpleCircuit :=
  C.mapAlong t.portEmbedding (fun a b => (t.portEmbedding_vertex_iff a b).symm)
    (fun i => (t.portEmbedding_twin_of_terminal (C.dart i) (hT i)).symm)

theorem recoverUnsubdivided_port (x : Fin C.length × Bool) :
    (C.recoverUnsubdivided t hT).port x = t.portEmbedding (C.port x) :=
  C.mapAlong_port _ _ _ x

theorem recoverUnsubdivided_label (x : Fin C.length × Bool) :
    Port.label G.jointLabel ((C.recoverUnsubdivided t hT).port x) = Port.label H.jointLabel (C.port x) := by
  rw [C.recoverUnsubdivided_port]
  exact t.portLabel _

theorem recoverUnsubdivided_terminal (x : Fin C.length × Bool) :
    G.Terminal ((C.recoverUnsubdivided t hT).port x) := by
  rw [C.recoverUnsubdivided_port]
  exact (t.terminal_iff _).mpr (H.terminal_of_no_junctions _)

end PortGraph.SimpleCircuit
end ThomGame.Pictures
