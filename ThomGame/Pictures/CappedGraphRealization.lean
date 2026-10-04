module

public import ThomGame.Pictures.OpenGraphBlocks
public import ThomGame.Pictures.DisconnectedClosedGraph

/-!
# Prescribed-boundary realization from capped Euler saturation

The actual reversed boundary is a single auxiliary relation block.
Degree-two joints supply relation-free cap blocks, so smoothing is not
needed before capping. The disconnected block realization closes the
whole family; puncturing the unique auxiliary relation restores the
exact boundary word and all original relation occurrences.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv CyclicBlock RibbonConnectivity
open scoped Classical BigOperators

variable {R S : Type*} {P : InvolutionPresentation R S} {w : List S}
  (G : PortGraph P w [])

theorem cappedRotation_joint (j : G.Joint) (side : Bool) :
    G.cappedRotation (.joint j side) = .joint j (!side) :=
  G.cappingTargets_unmarked (.joint j (!side)) (fun h => h)

noncomputable def cappedJointBlock (j : G.Joint) :
    DiagramBlock (P.adjoinRelation w 0) (Port.label G.jointLabel)
      G.cappedRotation G.pairing.perm where
  ports := [.joint j false, .joint j true]
  cyclic := {
    nodup := by simp
    nonempty := by simp
    rotation := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> simp [G.cappedRotation_joint, List.formPerm] }
  diagram := (Diagram.cap (P := P.adjoinRelation w 0) (G.jointLabel j)).cast
    (by rw [G.filter_moving_pairing]; rfl) rfl

theorem cappedJointBlock_labels (j : G.Joint) : (G.cappedJointBlock j).diagram.labels = [] := by
  simp only [cappedJointBlock, Diagram.labels_cast, Diagram.labels]

def cappedAllOwner : G.Dart → Option (G.Hub ⊕ G.Joint)
  | .top _ => none
  | .bottom i => i.elim0
  | .hub h _ => some (.inl h)
  | .joint j _ => some (.inr j)

theorem outerBlock_mem_allOwner (hw : 0 < w.length) (x : G.Dart) :
    x ∈ (G.outerBlock hw).ports ↔ G.cappedAllOwner x = none := by
  change x ∈ G.topPorts.reverse ↔ _
  simp only [List.mem_reverse, topPorts, List.mem_ofFn]
  cases x with
  | top i => exact ⟨fun _ => rfl, fun _ => ⟨i, rfl⟩⟩
  | bottom i => exact i.elim0
  | hub h i => simp [cappedAllOwner]
  | joint j side => simp [cappedAllOwner]

theorem cappedHubBlock_mem_allOwner (h : G.Hub)
    (hn : 0 < (P.word (G.hubLabel h)).length) (x : G.Dart) :
    x ∈ (G.cappedHubBlock h hn).ports ↔ G.cappedAllOwner x = some (.inl h) := by
  change x ∈ (G.hubBlock h hn).ports ↔ _
  rw [G.hubBlock_mem]
  cases x with
  | top i => simp [cappedAllOwner]
  | bottom i => exact i.elim0
  | joint j side => simp [cappedAllOwner]
  | hub k i =>
    constructor
    · rintro ⟨j, he⟩; cases he; rfl
    · intro he
      have hk : k = h := Sum.inl.inj (Option.some.inj he)
      subst k
      exact ⟨i, rfl⟩

theorem cappedJointBlock_mem_allOwner (j : G.Joint) (x : G.Dart) :
    x ∈ (G.cappedJointBlock j).ports ↔ G.cappedAllOwner x = some (.inr j) := by
  cases x with
  | top i => simp [cappedJointBlock, cappedAllOwner]
  | bottom i => exact i.elim0
  | hub h i => simp [cappedJointBlock, cappedAllOwner]
  | joint k side => cases side <;> simp [cappedJointBlock, cappedAllOwner]

noncomputable def cappedAllBlockFamily (hw : 0 < w.length)
    (hn : ∀ h, 0 < (P.word (G.hubLabel h)).length) :
    BlockFamily (P.adjoinRelation w 0) (Port.label G.jointLabel)
      G.cappedRotation G.pairing.perm where
  Index := Option (G.Hub ⊕ G.Joint)
  block
    | none => G.outerBlock hw
    | some (.inl h) => G.cappedHubBlock h (hn h)
    | some (.inr j) => G.cappedJointBlock j
  owner := G.cappedAllOwner
  mem_ports x i := by
    rcases i with _ | (h | j)
    · exact G.outerBlock_mem_allOwner hw x
    · exact G.cappedHubBlock_mem_allOwner h (hn h) x
    · exact G.cappedJointBlock_mem_allOwner j x

theorem cappedAllBlockFamily_relations (hw : 0 < w.length)
    (hn : ∀ h, 0 < (P.word (G.hubLabel h)).length) :
    (G.cappedAllBlockFamily hw hn).relations =
      {none} + (∑ h : G.Hub, ([G.hubLabel h] : Multiset R)).map some := by
  unfold BlockFamily.relations cappedAllBlockFamily
  rw [Fintype.sum_option, Fintype.sum_sum_type]
  simp only [G.outerBlock_labels, G.cappedHubBlock_labels, G.cappedJointBlock_labels,
    Multiset.coe_nil, Finset.sum_const_zero, add_zero]
  congr 1
  let f : Multiset R →+ Multiset (Option R) := {
    toFun := Multiset.map some
    map_zero' := rfl
    map_add' := Multiset.map_add some }
  exact (map_sum f (fun h : G.Hub => ([G.hubLabel h] : Multiset R)) Finset.univ).symm

theorem exists_diagram_of_capped_saturated
    (hw : 0 < w.length) (hn : ∀ h, 0 < (P.word (G.hubLabel h)).length)
    (hcap : RotationEuler.count G.cappedRotation G.pairing.perm =
      2 * Nat.card (Component G.cappedRotation G.pairing.perm)) :
    ∃ d : Diagram P w [], (d.labels : Multiset R) =
      ∑ h : G.Hub, ([G.hubLabel h] : Multiset R) := by
  obtain ⟨d, hd⟩ := (G.cappedAllBlockFamily hw hn).exists_closed_diagram_of_saturated
    G.pairing.involutive G.pairing.label_twin hcap
  exact d.exists_punctured_diagram_of_multiset _
    (hd.trans (G.cappedAllBlockFamily_relations hw hn))

theorem exists_diagram_of_capped_saturated_preserving
    (hw : 0 < w.length) (hn : ∀ h, 0 < (P.word (G.hubLabel h)).length)
    (hcap : RotationEuler.count G.cappedRotation G.pairing.perm =
      2 * Nat.card (Component G.cappedRotation G.pairing.perm)) :
    ∃ d : Diagram P w [],
      (d.labels : Multiset R) = (∑ h : G.Hub, ([G.hubLabel h] : Multiset R)) ∧
      d.size = Fintype.card G.Hub ∧ d.sign = G.sign := by
  obtain ⟨d, hd⟩ := G.exists_diagram_of_capped_saturated hw hn hcap
  exact ⟨d, hd, G.diagram_size_of_hub_labels hd, G.diagram_sign_of_hub_labels hd⟩

end ThomGame.Pictures.PortGraph
