module

public import ThomGame.Pictures.BlockFamilyClosed
public import ThomGame.Pictures.EnumeratedCycleWord
public import ThomGame.Pictures.GraphRotation

/-!
# Initial diagram blocks for actual closed port graphs

Every relation hub supplies its own defining-word diagram, reversed when
the hub rotation is reversed. For a closed graph without subdivision
joints these blocks partition all ports. The resulting realization
theorem uses the actual graph rotation, pairing, and hub labels.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv CyclicBlock RibbonConnectivity
open scoped Classical BigOperators

variable {R S : Type*} {P : InvolutionPresentation R S}

section Hubs

variable {u v : List S} (G : PortGraph P u v)

def hubPorts (h : G.Hub) : List G.Dart := List.ofFn (fun i => Port.hub h i)

theorem hubPorts_label (h : G.Hub) :
    (G.hubPorts h).map (Port.label G.jointLabel) = P.word (G.hubLabel h) := by
  simp only [hubPorts, List.map_ofFn, Function.comp_def, Port.label]
  exact List.ofFn_get (P.word (G.hubLabel h))

theorem hubPorts_cyclic (h : G.Hub) (hn : 0 < (P.word (G.hubLabel h)).length)
    (hf : G.hubFlip h = false) : IsCycleWord G.rotation (G.hubPorts h) := by
  apply IsCycleWord.ofFn G.rotation (fun i => Port.hub h i)
  · intro i j he; cases he; rfl
  · exact hn
  · intro i
    change Port.hub h (G.hubRotation h i) = Port.hub h (finRotate _ i)
    simp only [hubRotation, hf, Bool.false_eq_true, ↓reduceIte]

theorem hubPorts_reverse_cyclic (h : G.Hub) (hn : 0 < (P.word (G.hubLabel h)).length)
    (hf : G.hubFlip h = true) : IsCycleWord G.rotation (G.hubPorts h).reverse := by
  have hc : IsCycleWord G.rotation.symm (G.hubPorts h) := by
    apply IsCycleWord.ofFn G.rotation.symm (fun i => Port.hub h i)
    · intro i j he; cases he; rfl
    · exact hn
    · intro i
      change Port.hub h ((G.hubRotation h).symm i) = Port.hub h (finRotate _ i)
      simp only [hubRotation, hf, ↓reduceIte, Equiv.symm_symm]
  exact hc.reverse

theorem filter_moving_pairing (w : List G.Dart) : w.filter (moving G.pairing.perm) = w := by
  apply List.filter_eq_self.mpr
  intro x _
  change decide (G.pairing.twin x ≠ x) = true
  exact decide_eq_true (G.pairing.ne_self x)

noncomputable def hubBlock (h : G.Hub) (hn : 0 < (P.word (G.hubLabel h)).length) :
    DiagramBlock P (Port.label G.jointLabel) G.rotation G.pairing.perm := by
  classical
  by_cases hf : G.hubFlip h = true
  · exact {
      ports := (G.hubPorts h).reverse
      cyclic := G.hubPorts_reverse_cyclic h hn hf
      diagram := (Diagram.down (P := P) (G.hubLabel h)).reverseDown.cast
        (by rw [G.filter_moving_pairing, List.map_reverse, G.hubPorts_label]) rfl }
  · exact {
      ports := G.hubPorts h
      cyclic := G.hubPorts_cyclic h hn (Bool.eq_false_iff.mpr hf)
      diagram := (Diagram.down (P := P) (G.hubLabel h)).cast
        (by rw [G.filter_moving_pairing, G.hubPorts_label]) rfl }

theorem hubBlock_labels (h : G.Hub) (hn : 0 < (P.word (G.hubLabel h)).length) :
    (G.hubBlock h hn).diagram.labels = [G.hubLabel h] := by
  classical
  unfold hubBlock
  split_ifs with hf
  · rw [dite_eq_left hf]
    simp only [Diagram.labels_cast]
    exact List.perm_singleton.mp (Diagram.down (P := P) (G.hubLabel h)).labels_reverseDown_perm
  · rw [dite_eq_right hf]
    simp only [Diagram.labels_cast, Diagram.labels]

theorem hubBlock_mem (h : G.Hub) (hn : 0 < (P.word (G.hubLabel h)).length) (x : G.Dart) :
    x ∈ (G.hubBlock h hn).ports ↔ ∃ i, Port.hub h i = x := by
  classical
  unfold hubBlock
  split_ifs <;> simp only [List.mem_reverse, hubPorts, List.mem_ofFn]

end Hubs

variable (G : PortGraph P [] []) [IsEmpty G.Joint]

def closedHubOwner : G.Dart → G.Hub
  | .top i => i.elim0
  | .bottom i => i.elim0
  | .hub h _ => h
  | .joint j _ => isEmptyElim j

theorem hubBlock_mem_owner (h : G.Hub) (hn : 0 < (P.word (G.hubLabel h)).length) (x : G.Dart) :
    x ∈ (G.hubBlock h hn).ports ↔ G.closedHubOwner x = h := by
  rw [G.hubBlock_mem]
  cases x with
  | top i => exact i.elim0
  | bottom i => exact i.elim0
  | joint j _ => exact (isEmptyElim j : False).elim
  | hub j k =>
    change (∃ i, Port.hub h i = Port.hub j k) ↔ j = h
    constructor
    · rintro ⟨i, he⟩; cases he; rfl
    · intro he; subst j; exact ⟨k, rfl⟩

noncomputable def closedBlockFamily (hn : ∀ h, 0 < (P.word (G.hubLabel h)).length) :
    BlockFamily P (Port.label G.jointLabel) G.rotation G.pairing.perm where
  Index := G.Hub
  block h := G.hubBlock h (hn h)
  owner := G.closedHubOwner
  mem_ports x h := G.hubBlock_mem_owner h (hn h) x

theorem closedBlockFamily_relations (hn : ∀ h, 0 < (P.word (G.hubLabel h)).length) :
    (G.closedBlockFamily hn).relations = ∑ h : G.Hub, ([G.hubLabel h] : Multiset R) := by
  unfold BlockFamily.relations closedBlockFamily
  simp only [G.hubBlock_labels]

theorem exists_closed_diagram_of_rotationEuler
    (hn : ∀ h, 0 < (P.word (G.hubLabel h)).length)
    (hEuler : RotationEuler.count G.rotation G.pairing.perm =
      2 * Nat.card (Component G.rotation G.pairing.perm))
    (hconn : ∀ x y : G.Dart, Connected G.rotation G.pairing.perm x y) :
    ∃ d : Diagram P [] [], (d.labels : Multiset R) = ∑ h : G.Hub, ([G.hubLabel h] : Multiset R) := by
  obtain ⟨d, hd⟩ := (G.closedBlockFamily hn).exists_closed_diagram G.pairing.involutive
    G.pairing.label_twin hEuler hconn
  exact ⟨d, hd.trans (G.closedBlockFamily_relations hn)⟩

end ThomGame.Pictures.PortGraph
