module

public import ThomGame.Pictures.CircuitHubPorts
public import ThomGame.Pictures.SunTriangleBlocks

/-!
# Circuits using one sun rim label and its two incident spoke labels

At every vertex the circuit uses precisely the spoke and the specified
rim label. These are the alternating circuits in Slofstra Lemma 10.6.
Our rim label i is incident to rows i and predecessor i.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}

def SunBandLabel (i : Fin n) (z : Fin n ⊕ Fin n) : Prop :=
  z = Sum.inr i ∨ z = Sum.inl i ∨ z = Sum.inl ((finRotate n).symm i)

theorem sunBandLabel_rim (i j : Fin n) : SunBandLabel i (Sum.inr j) ↔ j = i := by
  simp [SunBandLabel]

variable (G : PortGraph (sunPresentation n b) u v) (hn : 3 ≤ n)

theorem sunBand_nonspoke_label (i : Fin n) (h : G.Hub) (p : Fin 3) (hp : p ≠ 0)
    (hl : SunBandLabel i (Port.label G.jointLabel (.hub h p : G.Dart))) :
    Port.label G.jointLabel (.hub h p : G.Dart) = Sum.inr i := by
  fin_cases p
  · exact (hp rfl).elim
  · exact congrArg Sum.inr ((sunBandLabel_rim i (G.hubLabel h)).mp hl)
  · exact congrArg Sum.inr ((sunBandLabel_rim i (finRotate n (G.hubLabel h))).mp hl)

include hn in
theorem sunBand_pair_slots (i : Fin n) (h : G.Hub) (p q : Fin 3) (hpq : p ≠ q)
    (hp : SunBandLabel i (Port.label G.jointLabel (.hub h p : G.Dart)))
    (hq : SunBandLabel i (Port.label G.jointLabel (.hub h q : G.Dart))) :
    (p = 0 ∧ Port.label G.jointLabel (.hub h q : G.Dart) = Sum.inr i) ∨
      (q = 0 ∧ Port.label G.jointLabel (.hub h p : G.Dart) = Sum.inr i) := by
  by_cases hp0 : p = 0
  · exact Or.inl ⟨hp0, G.sunBand_nonspoke_label i h q (fun hq0 => hpq (hp0.trans hq0.symm)) hq⟩
  · by_cases hq0 : q = 0
    · exact Or.inr ⟨hq0, G.sunBand_nonspoke_label i h p hp0 hp⟩
    · have he := (G.sunBand_nonspoke_label i h p hp0 hp).trans
        (G.sunBand_nonspoke_label i h q hq0 hq).symm
      apply (hpq ((Hypergraph.sunSystem n hn b).column_injective (G.hubLabel h) ?_)).elim
      exact (SolutionGroup.rowGraph_port_label (Hypergraph.sunSystem n hn b) G h p).symm.trans
        (he.trans (SolutionGroup.rowGraph_port_label (Hypergraph.sunSystem n hn b) G h q))

namespace SimpleCircuit

variable {G} [IsEmpty G.Joint] (C : G.SimpleCircuit) (i : Fin n)
  (hband : ∀ k : Fin C.length, SunBandLabel i (Port.label G.jointLabel (C.dart k)))

omit [IsEmpty G.Joint] in
include hband in
theorem sunBand_port_label (k : Fin C.length) (side : Bool) :
    SunBandLabel i (Port.label G.jointLabel (C.port (k, side))) := by
  cases side
  · exact hband k
  · change SunBandLabel i (Port.label G.jointLabel (G.pairing.twin (C.dart ((finRotate C.length).symm k))))
    rw [G.pairing.label_twin]
    exact hband _

include hn hband in
theorem sunBand_vertex_ports (k : Fin C.length) :
    (C.outgoing k = .hub (C.hubAt k) (0 : Fin 3) ∧
      Port.label G.jointLabel (C.incoming k) = Sum.inr i) ∨
    (C.incoming k = .hub (C.hubAt k) (0 : Fin 3) ∧
      Port.label G.jointLabel (C.outgoing k) = Sum.inr i) := by
  obtain ⟨p, hp⟩ := C.port_eq_hubAt k false
  obtain ⟨q, hq⟩ := C.port_eq_hubAt k true
  have hpq : p ≠ q := by
    intro he
    exact C.incoming_ne_outgoing k (hq.trans ((congrArg (Port.hub (C.hubAt k)) he.symm).trans hp.symm))
  have hpl := C.sunBand_port_label i hband k false
  have hql := C.sunBand_port_label i hband k true
  rw [hp] at hpl
  rw [hq] at hql
  rcases G.sunBand_pair_slots hn i (C.hubAt k) p q hpq hpl hql with ⟨hp0, hl⟩ | ⟨hq0, hl⟩
  · exact Or.inl ⟨hp.trans (hp0 ▸ rfl), (congrArg (Port.label G.jointLabel) hq).trans hl⟩
  · exact Or.inr ⟨hq.trans (hq0 ▸ rfl), (congrArg (Port.label G.jointLabel) hp).trans hl⟩

end SimpleCircuit
end ThomGame.Pictures.PortGraph
