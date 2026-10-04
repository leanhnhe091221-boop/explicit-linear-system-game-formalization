module

public import ThomGame.Pictures.GraphSmoothing

/-!
# Wires through degree-two junctions

A wire may cross an edge or pass through a subdivision vertex. It does not
turn through a relation hub. This separates single labelled wires from paths
in the full graph and makes the effect of smoothing on endpoints explicit.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S} (G : PortGraph P u v)

def wireTurn : G.Dart → G.Dart
  | .top i => .top i
  | .bottom i => .bottom i
  | .hub h i => .hub h i
  | .joint j side => .joint j (!side)

theorem wireTurn_involutive : Function.Involutive G.wireTurn := by
  intro a
  cases a <;> simp [wireTurn]

theorem wireTurn_label (a : G.Dart) :
    Port.label G.jointLabel (G.wireTurn a) = Port.label G.jointLabel a := by
  cases a <;> rfl

def WireStep (a b : G.Dart) : Prop := b = G.pairing.twin a ∨ b = G.wireTurn a

def WireConnected (a b : G.Dart) : Prop := Relation.ReflTransGen G.WireStep a b

theorem wireStep_symm {a b : G.Dart} (h : G.WireStep a b) : G.WireStep b a := by
  rcases h with h | h
  · exact Or.inl (by rw [h, G.pairing.involutive])
  · exact Or.inr (by rw [h, G.wireTurn_involutive])

theorem wireConnected_refl (a : G.Dart) : G.WireConnected a a := Relation.ReflTransGen.refl

theorem wireConnected_edge (a : G.Dart) : G.WireConnected a (G.pairing.twin a) :=
  Relation.ReflTransGen.single (Or.inl rfl)

theorem wireConnected_turn (a : G.Dart) : G.WireConnected a (G.wireTurn a) :=
  Relation.ReflTransGen.single (Or.inr rfl)

theorem wireConnected_trans {a b c : G.Dart} (h : G.WireConnected a b) (k : G.WireConnected b c) :
    G.WireConnected a c := h.trans k

theorem wireConnected_symm {a b : G.Dart} (h : G.WireConnected a b) : G.WireConnected b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih =>
    exact (Relation.ReflTransGen.single (G.wireStep_symm hbc)).trans ih

theorem wireConnected_label {a b : G.Dart} (h : G.WireConnected a b) :
    Port.label G.jointLabel a = Port.label G.jointLabel b := by
  induction h with
  | refl => rfl
  | @tail b c hab hbc ih =>
    rcases hbc with rfl | rfl
    · exact ih.trans (G.pairing.label_twin b).symm
    · exact ih.trans (G.wireTurn_label b).symm

theorem wireTurn_of_no_junctions [IsEmpty G.Joint] (a : G.Dart) : G.wireTurn a = a := by
  cases a with
  | top i => rfl
  | bottom i => rfl
  | hub h i => rfl
  | joint j _ => exact isEmptyElim j

theorem wireConnected_iff_edge [IsEmpty G.Joint] (a b : G.Dart) :
    G.WireConnected a b ↔ G.pairing.edge a = G.pairing.edge b := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | @tail b c hab hbc ih =>
      rcases hbc with rfl | rfl
      · exact ih.trans (G.pairing.edge_twin b).symm
      · rwa [G.wireTurn_of_no_junctions]
  · intro h
    rcases (G.pairing.edge_eq_iff a b).mp h with rfl | rfl
    · exact G.wireConnected_refl _
    · exact G.wireConnected_symm (G.wireConnected_edge b)

theorem smooth_wireTurn (j : G.Joint) (a : (G.smooth j).Dart) :
    (G.smoothPorts j ((G.smooth j).wireTurn a)).val =
      G.wireTurn (G.smoothPorts j a).val := by
  cases a <;> rfl

/-- The isolated pair recorded as a circle has exactly its two junction ports. -/
theorem loop_wire_component (j : G.Joint)
    (hp : G.pairing.twin (.joint j false) = .joint j true) (x : G.Dart) :
    G.WireConnected (.joint j false) x ↔ x = .joint j false ∨ x = .joint j true := by
  have hp' : G.pairing.twin (.joint j true) = .joint j false := by
    calc
      G.pairing.twin (.joint j true) = G.pairing.twin (G.pairing.twin (.joint j false)) :=
        congrArg G.pairing.twin hp.symm
      _ = _ := G.pairing.involutive _
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl rfl
    | @tail b c hab hbc ih =>
      rcases ih with rfl | rfl <;> rcases hbc with rfl | rfl
      · exact Or.inr hp
      · exact Or.inr rfl
      · exact Or.inl hp'
      · exact Or.inl rfl
  · rintro (rfl | rfl)
    · exact G.wireConnected_refl _
    · exact G.wireConnected_turn _

/-- Every new edge can be expanded to a wire in the original graph. -/
theorem smooth_edge_expands (j : G.Joint) (x : (G.smooth j).Dart) :
    G.WireConnected (G.smoothPorts j x).val
      (G.smoothPorts j ((G.smooth j).pairing.twin x)).val := by
  classical
  rw [G.smooth_twin_val]
  let a : G.Dart := .joint j false
  let b : G.Dart := .joint j true
  have hab : a ≠ b := by simp [a, b]
  have hl : Port.label G.jointLabel a = Port.label G.jointLabel b := rfl
  have hmiddle : G.WireConnected a b := G.wireConnected_turn a
  have hchain : G.WireConnected (G.pairing.twin a) (G.pairing.twin b) :=
    G.wireConnected_trans (G.wireConnected_symm (G.wireConnected_edge a))
      (G.wireConnected_trans hmiddle (G.wireConnected_edge b))
  by_cases hxa : (G.smoothPorts j x).val = G.pairing.twin a
  · rw [hxa, G.pairing.splice_twin_partner_left hab hl]
    exact hchain
  by_cases hxb : (G.smoothPorts j x).val = G.pairing.twin b
  · rw [hxb, G.pairing.splice_twin_partner_right hab hl]
    exact G.wireConnected_symm hchain
  · rw [G.pairing.splice_twin_unchanged hl (G.smoothPorts j x).property.1
      (G.smoothPorts j x).property.2 hxa hxb]
    exact G.wireConnected_edge _

theorem smooth_wireConnected_expands (j : G.Joint) {a b : (G.smooth j).Dart}
    (h : (G.smooth j).WireConnected a b) :
    G.WireConnected (G.smoothPorts j a).val (G.smoothPorts j b).val := by
  induction h with
  | refl => exact G.wireConnected_refl _
  | @tail b c hab hbc ih =>
    rcases hbc with rfl | rfl
    · exact G.wireConnected_trans ih (G.smooth_edge_expands j b)
    · rw [G.smooth_wireTurn]
      exact G.wireConnected_trans ih (G.wireConnected_turn _)

end ThomGame.Pictures.PortGraph
