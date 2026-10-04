module

public import ThomGame.Pictures.SmoothingTrace
public import ThomGame.Pictures.WireSmoothing

/-!
# The exact endpoint matching after all junctions are smoothed

Smoothing traces preserve wires in both directions. Their final darts are
in bijection with all the original boundary and relation ports, with labels
unchanged. Thus the final matching records precisely the original wires.
-/

@[expose] public section
namespace ThomGame.Pictures

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}

namespace PortGraph

variable (G : PortGraph P u v)

def Terminal : G.Dart → Prop
  | .top _ => True
  | .bottom _ => True
  | .hub _ _ => True
  | .joint _ _ => False

theorem terminal_of_no_junctions [IsEmpty G.Joint] (a : G.Dart) : G.Terminal a := by
  cases a with
  | top i => trivial
  | bottom i => trivial
  | hub h i => trivial
  | joint j _ => exact isEmptyElim j

def smoothPortEmbedding (j : G.Joint) : (G.smooth j).Dart ↪ G.Dart :=
  ⟨fun a => (G.smoothPorts j a).val, Subtype.val_injective.comp (G.smoothPorts j).injective⟩

theorem smooth_terminal_iff (j : G.Joint) (a : (G.smooth j).Dart) :
    G.Terminal (G.smoothPortEmbedding j a) ↔ (G.smooth j).Terminal a := by
  cases a <;> rfl

theorem terminal_survives (j : G.Joint) (x : G.Dart) (hx : G.Terminal x) :
    ∃ y : (G.smooth j).Dart, (G.smooth j).Terminal y ∧ G.smoothPortEmbedding j y = x := by
  cases x with
  | top i => exact ⟨.top i, trivial, rfl⟩
  | bottom i => exact ⟨.bottom i, trivial, rfl⟩
  | hub h i => exact ⟨.hub h i, trivial, rfl⟩
  | joint j side => exact hx.elim

end PortGraph

namespace Smoothing

variable {G H : PortGraph P u v} {circles : List S}

noncomputable def portEmbedding : {G H : PortGraph P u v} → {circles : List S} →
    Smoothing G H circles → H.Dart ↪ G.Dart
  | _, _, _, .refl _ => Function.Embedding.refl _
  | G, _, _, .step j tail => tail.portEmbedding.trans (G.smoothPortEmbedding j)

theorem portLabel (d : Smoothing G H circles) (a : H.Dart) :
    Port.label G.jointLabel (d.portEmbedding a) = Port.label H.jointLabel a := by
  induction d with
  | refl _ => rfl
  | @step G H circles j tail ih =>
    exact (G.smoothPorts_label j (tail.portEmbedding a)).trans (ih a)

theorem terminal_iff (d : Smoothing G H circles) (a : H.Dart) :
    G.Terminal (d.portEmbedding a) ↔ H.Terminal a := by
  induction d with
  | refl _ => rfl
  | @step G H circles j tail ih =>
    exact (G.smooth_terminal_iff j (tail.portEmbedding a)).trans (ih a)

theorem terminal_surjective (d : Smoothing G H circles) (x : G.Dart) (hx : G.Terminal x) :
    ∃ y : H.Dart, H.Terminal y ∧ d.portEmbedding y = x := by
  induction d with
  | refl _ => exact ⟨x, hx, rfl⟩
  | @step G H circles j tail ih =>
    obtain ⟨z, hz, hxz⟩ := G.terminal_survives j x hx
    obtain ⟨y, hy, hzy⟩ := ih z hz
    refine ⟨y, hy, ?_⟩
    change G.smoothPortEmbedding j (tail.portEmbedding y) = x
    rw [hzy]
    exact hxz

theorem wireConnected_iff (d : Smoothing G H circles) (a b : H.Dart) :
    H.WireConnected a b ↔ G.WireConnected (d.portEmbedding a) (d.portEmbedding b) := by
  induction d with
  | refl _ => rfl
  | @step G H circles j tail ih =>
    exact (ih a b).trans (G.smooth_wireConnected_iff j (tail.portEmbedding a) (tail.portEmbedding b))

theorem wire_iff_final_edge (d : Smoothing G H circles) [IsEmpty H.Joint] (a b : H.Dart) :
    G.WireConnected (d.portEmbedding a) (d.portEmbedding b) ↔ H.pairing.edge a = H.pairing.edge b :=
  (d.wireConnected_iff a b).symm.trans (H.wireConnected_iff_edge a b)

/-- Every original terminal occurs exactly once among the final edge endpoints. -/
noncomputable def terminalEquiv (d : Smoothing G H circles) [IsEmpty H.Joint] :
    H.Dart ≃ {a : G.Dart // G.Terminal a} :=
  Equiv.ofBijective (fun a => ⟨d.portEmbedding a, (d.terminal_iff a).mpr (H.terminal_of_no_junctions a)⟩)
    ⟨fun _ _ h => d.portEmbedding.injective (congrArg Subtype.val h), fun x => by
      obtain ⟨a, _, ha⟩ := d.terminal_surjective x.val x.property
      exact ⟨a, Subtype.ext ha⟩⟩

noncomputable def terminalPairing (d : Smoothing G H circles) [IsEmpty H.Joint] :
    Pairing (fun a : {a : G.Dart // G.Terminal a} => Port.label G.jointLabel a.val) :=
  H.pairing.transport d.terminalEquiv _ d.portLabel

theorem terminalPairing_twin (d : Smoothing G H circles) [IsEmpty H.Joint] (a : H.Dart) :
    d.terminalPairing.twin (d.terminalEquiv a) = d.terminalEquiv (H.pairing.twin a) := by
  simp only [terminalPairing, Pairing.transport, Equiv.symm_apply_apply]

theorem terminalPairing_edge_iff (d : Smoothing G H circles) [IsEmpty H.Joint]
    (a b : {a : G.Dart // G.Terminal a}) :
    d.terminalPairing.edge a = d.terminalPairing.edge b ↔ G.WireConnected a.val b.val := by
  obtain ⟨x, rfl⟩ := d.terminalEquiv.surjective a
  obtain ⟨y, rfl⟩ := d.terminalEquiv.surjective b
  rw [Pairing.edge_eq_iff, d.terminalPairing_twin]
  change (d.terminalEquiv x = d.terminalEquiv y ∨
    d.terminalEquiv x = d.terminalEquiv (H.pairing.twin y)) ↔
      G.WireConnected (d.portEmbedding x) (d.portEmbedding y)
  rw [d.terminalEquiv.injective.eq_iff, d.terminalEquiv.injective.eq_iff,
    d.wire_iff_final_edge, Pairing.edge_eq_iff]

/-- The matching on original terminals does not depend on the order of smoothing. -/
theorem terminalPairing_independent {K : PortGraph P u v} {circles' : List S}
    (d : Smoothing G H circles) (e : Smoothing G K circles') [IsEmpty H.Joint] [IsEmpty K.Joint] :
    d.terminalPairing = e.terminalPairing := by
  apply Pairing.ext_edge_relation
  intro a b
  exact (d.terminalPairing_edge_iff a b).trans (e.terminalPairing_edge_iff a b).symm

theorem unique_other_terminal (d : Smoothing G H circles) [IsEmpty H.Joint]
    (a : {a : G.Dart // G.Terminal a}) :
    ∃! b : {b : G.Dart // G.Terminal b}, b ≠ a ∧ G.WireConnected a.val b.val := by
  refine ⟨d.terminalPairing.twin a, ⟨d.terminalPairing.ne_self a, ?_⟩, ?_⟩
  · exact (d.terminalPairing_edge_iff _ _).mp (d.terminalPairing.edge_twin a).symm
  · rintro b ⟨hba, hab⟩
    exact (d.terminalPairing.twin_eq_of_edge_eq ((d.terminalPairing_edge_iff _ _).mpr hab)
      hba.symm).symm

end Smoothing
end ThomGame.Pictures
