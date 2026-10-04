module

public import ThomGame.Pictures.CircuitTrace

/-!
# The circuits retained by complete junction elimination

They are precisely the original circuits containing a boundary or relation
port. The permutation on these terminal ports and the number of discarded
isolated circles are independent of the order of smoothing.
-/

@[expose] public section
namespace ThomGame.Pictures

open scoped Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}

namespace PortGraph

variable (G : PortGraph P u v)

theorem terminal_rotation_iff (a : G.Dart) : G.Terminal (G.rotation a) ↔ G.Terminal a := by
  cases a <;> rfl

theorem terminal_rotation_symm_iff (a : G.Dart) : G.Terminal (G.rotation.symm a) ↔ G.Terminal a := by
  cases a <;> rfl

def terminalRotation : Equiv.Perm {a : G.Dart // G.Terminal a} where
  toFun a := ⟨G.rotation a.val, (G.terminal_rotation_iff a.val).mpr a.property⟩
  invFun a := ⟨G.rotation.symm a.val, (G.terminal_rotation_symm_iff a.val).mpr a.property⟩
  left_inv a := Subtype.ext (G.rotation.symm_apply_apply a.val)
  right_inv a := Subtype.ext (G.rotation.apply_symm_apply a.val)

def CircuitHasTerminal (c : G.Circuit) : Prop := ∃ a : G.Dart, G.Terminal a ∧ G.circuit a = c

end PortGraph

namespace Smoothing

variable {G H : PortGraph P u v} {circles : List S}

theorem portRotation (d : Smoothing G H circles) (a : H.Dart) :
    d.portEmbedding (H.rotation a) = G.rotation (d.portEmbedding a) := by
  induction d with
  | refl _ => rfl
  | @step G H circles j tail ih =>
    change G.smoothPortEmbedding j (tail.portEmbedding (H.rotation a)) = _
    rw [ih]
    exact G.smooth_rotation j (tail.portEmbedding a)

theorem terminalRotation_equiv (d : Smoothing G H circles) [IsEmpty H.Joint] (a : H.Dart) :
    d.terminalEquiv (H.rotation a) = G.terminalRotation (d.terminalEquiv a) :=
  Subtype.ext (d.portRotation a)

noncomputable def terminalCircuitStep (d : Smoothing G H circles) [IsEmpty H.Joint] :
    Equiv.Perm {a : G.Dart // G.Terminal a} := d.terminalPairing.perm.trans G.terminalRotation

theorem terminalCircuitStep_equiv (d : Smoothing G H circles) [IsEmpty H.Joint] (a : H.Dart) :
    d.terminalCircuitStep (d.terminalEquiv a) = d.terminalEquiv (H.circuitStep a) := by
  change G.terminalRotation (d.terminalPairing.twin (d.terminalEquiv a)) = _
  rw [d.terminalPairing_twin]
  exact (d.terminalRotation_equiv (H.pairing.twin a)).symm

theorem terminalCircuitStep_independent {K : PortGraph P u v} {circles' : List S}
    (d : Smoothing G H circles) (e : Smoothing G K circles') [IsEmpty H.Joint] [IsEmpty K.Joint] :
    d.terminalCircuitStep = e.terminalCircuitStep := by
  unfold terminalCircuitStep
  rw [d.terminalPairing_independent e]

theorem circuitEmbedding_range_iff (d : Smoothing G H circles) [IsEmpty H.Joint] (c : G.Circuit) :
    (∃ q : H.Circuit, d.circuitEmbedding q = c) ↔ G.CircuitHasTerminal c := by
  constructor
  · rintro ⟨q, rfl⟩
    refine Quotient.inductionOn q fun a => ?_
    refine ⟨d.portEmbedding a, (d.terminal_iff a).mpr (H.terminal_of_no_junctions a), ?_⟩
    exact (d.circuitEmbedding_circuit a).symm
  · rintro ⟨a, ha, hc⟩
    obtain ⟨b, _, hb⟩ := d.terminal_surjective a ha
    refine ⟨H.circuit b, ?_⟩
    rw [d.circuitEmbedding_circuit, hb, hc]

noncomputable def retainedCircuitEquiv (d : Smoothing G H circles) [IsEmpty H.Joint] :
    H.Circuit ≃ {c : G.Circuit // G.CircuitHasTerminal c} :=
  Equiv.ofBijective (fun q => ⟨d.circuitEmbedding q, (d.circuitEmbedding_range_iff _).mp ⟨q, rfl⟩⟩)
    ⟨fun _ _ h => d.circuitEmbedding.injective (congrArg Subtype.val h), fun c => by
      obtain ⟨q, hq⟩ := (d.circuitEmbedding_range_iff c.val).mpr c.property
      exact ⟨q, Subtype.ext hq⟩⟩

theorem discarded_circuit_card (d : Smoothing G H circles) [IsEmpty H.Joint] :
    Fintype.card {c : G.Circuit // ¬ G.CircuitHasTerminal c} = 2 * circles.length := by
  have hr := Fintype.card_congr d.retainedCircuitEquiv
  have hc := d.circuit_card
  have hh := Fintype.card_subtype_compl G.CircuitHasTerminal
  simp only [← Nat.card_eq_fintype_card] at hr hc hh ⊢
  omega

theorem circles_length_independent {K : PortGraph P u v} {circles' : List S}
    (d : Smoothing G H circles) (e : Smoothing G K circles') [IsEmpty H.Joint] [IsEmpty K.Joint] :
    circles.length = circles'.length := by
  have hd := d.discarded_circuit_card
  have he := e.discarded_circuit_card
  omega

end Smoothing
end ThomGame.Pictures
