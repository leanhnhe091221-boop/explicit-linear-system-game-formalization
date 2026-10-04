module

public import ThomGame.Pictures.GluedCircuitSides
public import ThomGame.Pictures.UnsubdividedCircuitRecovery

/-!
# Every reduced circuit meets the interface or comes from one input

The interface case records an actual boundary occurrence, its seam
joint, and the unchanged edge label. If no circuit edge enters a joint
removed by smoothing, the whole circuit recovers in one gluing input
with the same indexed ports. Both inputs are assumed joint-free, so
every removed joint is an interface joint.
-/

@[expose] public section
namespace ThomGame.Pictures

open PortGraph

variable {R S : Type*} {P : InvolutionPresentation R S} {w : List S}
  {G : PortGraph P [] w} {H : PortGraph P w []}

namespace ClosedGluingReduction

variable (d : ClosedGluingReduction G H) (C : d.graph.SimpleCircuit)

def HasLeftPreimage : Prop :=
  ∃ D : G.SimpleCircuit, ∃ hlen : D.length = C.length,
    ∀ x : Fin D.length × Bool, compLeftEmbedding G H (D.port x) =
      d.trace.portEmbedding (C.port (finCongr hlen x.1, x.2))

def HasRightPreimage : Prop :=
  ∃ D : H.SimpleCircuit, ∃ hlen : D.length = C.length,
    ∀ x : Fin D.length × Bool, compRightEmbedding G H (D.port x) =
      d.trace.portEmbedding (C.port (finCongr hlen x.1, x.2))

theorem input_preimage_of_no_removed_joint
    (hT : ∀ k : Fin C.length, (G.comp H).Terminal ((G.comp H).pairing.twin (d.trace.portEmbedding (C.dart k)))) :
    d.HasLeftPreimage C ∨ d.HasRightPreimage C := by
  let D := C.recoverUnsubdivided d.trace hT
  have ht (k : Fin D.length) : (G.comp H).Terminal (D.dart k) :=
    C.recoverUnsubdivided_terminal d.trace hT (k, false)
  rcases D.exists_input_circuit ht with ⟨E, hlen, he⟩ | ⟨E, hlen, he⟩
  · exact Or.inl ⟨E, hlen, fun x => (he x).trans
      (C.recoverUnsubdivided_port d.trace hT (finCongr hlen x.1, x.2))⟩
  · exact Or.inr ⟨E, hlen, fun x => (he x).trans
      (C.recoverUnsubdivided_port d.trace hT (finCongr hlen x.1, x.2))⟩

def MeetsSeam : Prop :=
  ∃ (k : Fin C.length) (j : Fin w.length) (side : Bool),
    (G.comp H).pairing.twin (d.trace.portEmbedding (C.dart k)) = .joint (.inr j) side ∧
    Port.label d.graph.jointLabel (C.dart k) = w[j]

variable [IsEmpty G.Joint] [IsEmpty H.Joint]

theorem nonterminal_is_seam (x : (G.comp H).Dart) (hx : ¬ (G.comp H).Terminal x) :
    ∃ (j : Fin w.length) (side : Bool), x = .joint (.inr j) side := by
  cases x with
  | top j => exact j.elim0
  | bottom j => exact j.elim0
  | hub h p => exact (hx trivial).elim
  | joint j side =>
    rcases j with (j | j) | j
    · exact isEmptyElim j
    · exact isEmptyElim j
    · exact ⟨j, side, rfl⟩

theorem classify_circuit : d.MeetsSeam C ∨ d.HasLeftPreimage C ∨ d.HasRightPreimage C := by
  classical
  by_cases hT : ∀ k : Fin C.length,
      (G.comp H).Terminal ((G.comp H).pairing.twin (d.trace.portEmbedding (C.dart k)))
  · exact Or.inr (d.input_preimage_of_no_removed_joint C hT)
  · obtain ⟨k, hk⟩ := not_forall.mp hT
    obtain ⟨j, side, he⟩ := nonterminal_is_seam (G := G) (H := H) _ hk
    refine Or.inl ⟨k, j, side, he, ?_⟩
    have hl := (G.comp H).pairing.label_twin (d.trace.portEmbedding (C.dart k))
    rw [he] at hl
    exact ((d.trace.portLabel _).symm.trans hl.symm)

end ClosedGluingReduction
end ThomGame.Pictures
