module

public import ThomGame.Pictures.SunBandErasureDiagram
public import ThomGame.Pictures.SunFaceTermination

/-!
# Slofstra Lemma 10.6: three-label circuits cannot occur in a minimal sun

Our sun row is `[f_j, e_j, e_{j+1}]`. Thus the three labels for the
fixed rim edge `e_i` are `e_i, f_i, f_{i-1}`. A circuit with these labels
would give a genuine diagram with the same boundary and strictly fewer
hubs, contradicting minimality. The theorem applies to the actual
joint-free graphs produced by smoothing and sun normalization.
-/

@[expose] public section
namespace ThomGame.Pictures

variable {n : Nat} {b : Fin n → ZMod 2} {w : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) [] w}

namespace PortGraph

def NoSunBandCircuit (G : PortGraph (sunPresentation n b) [] w) : Prop :=
  ∀ (C : G.SimpleCircuit) (i : Fin n),
    ¬ ∀ k : Fin C.length, SunBandLabel i (Port.label G.jointLabel (C.dart k))

namespace SunMinimalState

variable [IsEmpty G.Joint] (H : G.SunMinimalState) (hn : 3 ≤ n)

include H hn in
theorem no_sunBand_circuit : G.NoSunBandCircuit := by
  intro C i hband
  by_cases hw : 0 < w.length
  · obtain ⟨d, hc, _, _⟩ := C.exists_sunBand_erased_bottom_diagram hn i hband hw H.euler H.noncrossing H.sees
    have hm := H.minimal d
    have hp := C.length_pos
    omega
  · have hw0 : w = [] := List.length_eq_zero_iff.mp (by omega)
    subst w
    have hm := H.minimal (.identity [])
    have hp : 0 < Fintype.card G.Hub := Fintype.card_pos_iff.mpr ⟨C.hubAt ⟨0, C.length_pos⟩⟩
    change Fintype.card G.Hub ≤ 0 at hm
    omega

include H hn in
theorem circuit_has_label_outside_sunBand (C : G.SimpleCircuit) (i : Fin n) :
    ∃ k : Fin C.length, ¬ SunBandLabel i (Port.label G.jointLabel (C.dart k)) := by
  classical
  exact not_forall.mp (H.no_sunBand_circuit hn C i)

end SunMinimalState

namespace SunFaceState

variable {hn : 3 ≤ n} {hw : ∀ z ∈ w, ∃ j, z = Sum.inl j} (H : G.SunFaceState hn hw)

include H in
theorem no_sunBand_circuit : G.NoSunBandCircuit := by
  let : IsEmpty G.Joint := H.noJoints
  exact H.minimal.no_sunBand_circuit hn

end SunFaceState
end PortGraph

namespace Smoothing

variable {d : Diagram (sunPresentation n b) [] w} [IsEmpty G.Joint]
  {cs : List (Fin n ⊕ Fin n)} (t : Smoothing d.graph G cs)

include t in
theorem no_sunBand_circuit (hm : d.CharacterMinimal) (hn : 3 ≤ n) : G.NoSunBandCircuit :=
  (t.sunMinimalState hm).no_sunBand_circuit hn

end Smoothing
end ThomGame.Pictures
