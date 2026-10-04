module

public import ThomGame.Pictures.RowTriangleBlocks
public import ThomGame.Pictures.PairingSurgery
public import ThomGame.Pictures.CircuitLocalEmbedding
public import ThomGame.Pictures.CircuitLabelCopies

/-!
# Actual same-label edge reconnection without changing any hub

Exchange the attachments of two distinct edges at equal-labelled hub
slots. The pairing is conjugated by the transposition of those actual
ports; all hub labels, orientations and counts are unchanged. This is
the graph operation used to split a repeated cover in Lemma 11.9.
Euler preservation and the changed circuits are separate conclusions.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv
open scoped Classical

variable {R S : Type*} {A : SparseSystem R S} {u v : List S}

structure RowEdgeSwitch (G : SolutionGroup.RowGraph A u v) where
  left : G.Hub
  right : G.Hub
  slot : Fin 3
  same_row : G.hubLabel left = G.hubLabel right
  different_edges : G.pairing.edge (.hub left slot) ≠ G.pairing.edge (.hub right slot)

namespace RowEdgeSwitch

variable {G : SolutionGroup.RowGraph A u v} (s : G.RowEdgeSwitch)

abbrev first : G.Dart := .hub s.left s.slot
abbrev second : G.Dart := .hub s.right s.slot

theorem label_eq : Port.label G.jointLabel s.first = Port.label G.jointLabel s.second :=
  G.row_same_hubLabel_port_label s.same_row s.slot

theorem first_ne_second : s.first ≠ s.second := fun he => s.different_edges (congrArg G.pairing.edge he)

theorem first_ne_twin_second : s.first ≠ G.pairing.twin s.second :=
  fun he => s.different_edges ((G.pairing.edge_eq_iff _ _).mpr (Or.inr he))

noncomputable def portSwap : Perm G.Dart := swap s.first s.second

theorem portSwap_label (x : G.Dart) : Port.label G.jointLabel (s.portSwap x) = Port.label G.jointLabel x :=
  Pairing.label_swap s.label_eq x

@[reducible] noncomputable def graph : SolutionGroup.RowGraph A u v where
  Hub := G.Hub
  Joint := G.Joint
  hubLabel := G.hubLabel
  hubFlip := G.hubFlip
  jointLabel := G.jointLabel
  pairing := G.pairing.transport s.portSwap (Port.label G.jointLabel) s.portSwap_label

theorem twin (x : G.Dart) : s.graph.pairing.twin x = s.portSwap (G.pairing.twin (s.portSwap x)) := rfl

theorem twin_first : s.graph.pairing.twin s.first = G.pairing.twin s.second := by
  rw [s.twin]
  change swap s.first s.second (G.pairing.twin (swap s.first s.second s.first)) = _
  rw [swap_apply_left]
  exact swap_apply_of_ne_of_ne s.first_ne_twin_second.symm (G.pairing.ne_self s.second)

theorem twin_second : s.graph.pairing.twin s.second = G.pairing.twin s.first := by
  rw [s.twin]
  change swap s.first s.second (G.pairing.twin (swap s.first s.second s.second)) = _
  rw [swap_apply_right]
  apply swap_apply_of_ne_of_ne (G.pairing.ne_self s.first)
  intro he
  exact s.first_ne_twin_second ((G.pairing.involutive s.first).symm.trans (congrArg G.pairing.twin he))

theorem twin_away (x : G.Dart) (ha : x ≠ s.first) (hb : x ≠ s.second)
    (hta : x ≠ G.pairing.twin s.first) (htb : x ≠ G.pairing.twin s.second) :
    s.graph.pairing.twin x = G.pairing.twin x := by
  rw [s.twin]
  change swap s.first s.second (G.pairing.twin (swap s.first s.second x)) = _
  rw [swap_apply_of_ne_of_ne ha hb]
  apply swap_apply_of_ne_of_ne
  · intro he
    exact hta ((G.pairing.involutive x).symm.trans (congrArg G.pairing.twin he))
  · intro he
    exact htb ((G.pairing.involutive x).symm.trans (congrArg G.pairing.twin he))

theorem twin_of_label (x : G.Dart) (hx : Port.label G.jointLabel x ≠ Port.label G.jointLabel s.first) :
    s.graph.pairing.twin x = G.pairing.twin x := by
  apply s.twin_away x
  · exact fun he => hx (congrArg (Port.label G.jointLabel) he)
  · exact fun he => hx ((congrArg (Port.label G.jointLabel) he).trans s.label_eq.symm)
  · exact fun he => hx ((congrArg (Port.label G.jointLabel) he).trans (G.pairing.label_twin _))
  · exact fun he => hx ((congrArg (Port.label G.jointLabel) he).trans
      ((G.pairing.label_twin _).trans s.label_eq.symm))

theorem rotation (x : G.Dart) : s.graph.rotation x = G.rotation x := by
  cases x <;> rfl

theorem face_permutation : s.graph.circuitStep = G.rotation * s.portSwap * G.pairing.perm * s.portSwap := by
  ext x
  rw [s.graph.circuitStep_apply, s.rotation, s.twin]
  rfl

theorem hub_card : Fintype.card s.graph.Hub = Fintype.card G.Hub := rfl
theorem character : s.graph.character = G.character := rfl
theorem sign : s.graph.sign = G.sign := rfl

variable (C : G.SimpleCircuit) (ha : ¬ C.Marked s.first) (hb : ¬ C.Marked s.second)

include ha hb in
theorem twin_of_marked {x : G.Dart} (hx : C.Marked x) : s.graph.pairing.twin x = G.pairing.twin x := by
  apply s.twin_away x
  · exact fun he => ha (he ▸ hx)
  · exact fun he => hb (he ▸ hx)
  · exact fun he => ha ((C.marked_twin_iff _).mp (he ▸ hx))
  · exact fun he => hb ((C.marked_twin_iff _).mp (he ▸ hx))

@[reducible] noncomputable def disjointCircuit : s.graph.SimpleCircuit :=
  C.mapAlong (Function.Embedding.refl _) (fun _ _ => Iff.rfl)
    (fun i => s.twin_of_marked C ha hb ⟨(i, false), rfl⟩)

theorem disjointCircuit_port (x : Fin C.length × Bool) : (s.disjointCircuit C ha hb).port x = C.port x :=
  C.mapAlong_port _ _ _ x

theorem disjointCircuit_face (side : Bool) (hf : C.BoundsFaceOrbit side) :
    (s.disjointCircuit C ha hb).BoundsFaceOrbit side := by
  apply C.boundsFaceOrbit_mapAlong _ _ _ side hf
  intro i
  change s.graph.circuitStep (C.port (i, side)) = G.circuitStep (C.port (i, side))
  rw [s.graph.circuitStep_apply, s.twin_of_marked C ha hb ⟨(i, side), rfl⟩, s.rotation]
  rfl

theorem disjointCircuit_cover (hc : C.IsLabelCover) : (s.disjointCircuit C ha hb).IsLabelCover := by
  intro i
  obtain ⟨h, k, p, q, hx, hy, hn, hl⟩ := hc i
  exact ⟨h, k, p, q, hx, (s.twin_of_marked C ha hb ⟨(i, false), rfl⟩).trans hy, hn, hl⟩

end RowEdgeSwitch
end ThomGame.Pictures.PortGraph
