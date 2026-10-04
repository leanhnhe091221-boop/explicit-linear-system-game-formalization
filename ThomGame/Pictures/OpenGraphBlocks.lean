module

public import ThomGame.Pictures.ClosedGraphBlocks
public import ThomGame.Pictures.GraphBoundaryCapping
public import ThomGame.Pictures.DistinguishedRelation

/-!
# Diagram blocks with a distinguished outer boundary

The reversed top boundary forms one auxiliary relation block. All old
hubs remain ordinary blocks on the same darts and pairing. Closing the
assembled family and puncturing its unique auxiliary vertex realizes the
prescribed word, preserving the multiset of the original hub labels.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv CyclicBlock RibbonConnectivity
open scoped Classical BigOperators

variable {R S : Type*} {P : InvolutionPresentation R S} {w : List S}
    (G : PortGraph P w [])

theorem boundaryCyclic_top (i : Fin w.length) :
    boundaryCyclic w [] (.inl i) = .inl (finRotate _ i) := by
  apply (boundaryOrderIndex w []).injective
  rw [boundaryCyclic_index]
  rfl

theorem boundaryCyclic_symm_top (i : Fin w.length) :
    (boundaryCyclic w []).symm (.inl i) = .inl ((finRotate _).symm i) := by
  apply (boundaryCyclic w []).injective
  rw [Equiv.apply_symm_apply, boundaryCyclic_top, Equiv.apply_symm_apply]

theorem cappedRotation_top (i : Fin w.length) :
    G.cappedRotation (.top i) = .top ((finRotate _).symm i) := by
  change G.cappingTargets (G.boundaryDart (.inl i)) = _
  rw [G.cappingTargets_boundary, boundaryCyclic_symm_top]
  rfl

theorem cappedRotation_hub (h : G.Hub) (i : Fin (P.word (G.hubLabel h)).length) :
    G.cappedRotation (.hub h i) = G.rotation (.hub h i) :=
  G.cappingTargets_unmarked (.hub h (G.hubRotation h i)) (fun h => h)

noncomputable def cappedHubBlock (h : G.Hub)
    (hn : 0 < (P.word (G.hubLabel h)).length) :
    DiagramBlock (P.adjoinRelation w 0) (Port.label G.jointLabel)
      G.cappedRotation G.pairing.perm where
  ports := (G.hubBlock h hn).ports
  cyclic := {
    nodup := (G.hubBlock h hn).cyclic.nodup
    nonempty := (G.hubBlock h hn).cyclic.nonempty
    rotation x hx := by
      obtain ⟨i, rfl⟩ := (G.hubBlock_mem h hn x).mp hx
      rw [G.cappedRotation_hub]
      exact (G.hubBlock h hn).cyclic.rotation _ hx }
  diagram := (G.hubBlock h hn).diagram.adjoinRelation w 0

theorem cappedHubBlock_labels (h : G.Hub)
    (hn : 0 < (P.word (G.hubLabel h)).length) :
    (G.cappedHubBlock h hn).diagram.labels = [some (G.hubLabel h)] := by
  simp only [cappedHubBlock, Diagram.labels_adjoinRelation, G.hubBlock_labels, List.map_cons,
    List.map_nil]

def topPorts : List G.Dart := List.ofFn (fun i => Port.top i)

theorem topPorts_label : (G.topPorts.map (Port.label G.jointLabel)) = w := by
  simp only [topPorts, List.map_ofFn, Function.comp_def, Port.label]
  exact List.ofFn_get w

theorem topPorts_reverse_cyclic (hw : 0 < w.length) :
    IsCycleWord G.cappedRotation G.topPorts.reverse := by
  have hc : IsCycleWord G.cappedRotation.symm G.topPorts := by
    apply IsCycleWord.ofFn G.cappedRotation.symm (fun i => Port.top i)
    · intro i j he; cases he; rfl
    · exact hw
    · intro i
      apply G.cappedRotation.injective
      rw [Equiv.apply_symm_apply, G.cappedRotation_top, Equiv.symm_apply_apply]
  exact hc.reverse

noncomputable def outerBlock (hw : 0 < w.length) :
    DiagramBlock (P.adjoinRelation w 0) (Port.label G.jointLabel)
      G.cappedRotation G.pairing.perm where
  ports := G.topPorts.reverse
  cyclic := G.topPorts_reverse_cyclic hw
  diagram := (Diagram.down (P := P.adjoinRelation w 0) none).reverseDown.cast
    (by rw [G.filter_moving_pairing, List.map_reverse, G.topPorts_label]; rfl) rfl

theorem outerBlock_labels (hw : 0 < w.length) :
    (G.outerBlock hw).diagram.labels = [none] := by
  simp only [outerBlock, Diagram.labels_cast]
  exact List.perm_singleton.mp
    (Diagram.down (P := P.adjoinRelation w 0) none).labels_reverseDown_perm

variable [IsEmpty G.Joint]

def cappedOwner : G.Dart → Option G.Hub
  | .top _ => none
  | .bottom i => i.elim0
  | .hub h _ => some h
  | .joint j _ => isEmptyElim j

theorem outerBlock_mem_owner (hw : 0 < w.length) (x : G.Dart) :
    x ∈ (G.outerBlock hw).ports ↔ G.cappedOwner x = none := by
  change x ∈ G.topPorts.reverse ↔ _
  simp only [List.mem_reverse, topPorts, List.mem_ofFn]
  cases x with
  | top i => exact ⟨fun _ => rfl, fun _ => ⟨i, rfl⟩⟩
  | bottom i => exact i.elim0
  | hub h i => simp [cappedOwner]
  | joint j _ => exact (isEmptyElim j : False).elim

theorem cappedHubBlock_mem_owner (h : G.Hub)
    (hn : 0 < (P.word (G.hubLabel h)).length) (x : G.Dart) :
    x ∈ (G.cappedHubBlock h hn).ports ↔ G.cappedOwner x = some h := by
  change x ∈ (G.hubBlock h hn).ports ↔ _
  rw [G.hubBlock_mem]
  cases x with
  | top i => simp [cappedOwner]
  | bottom i => exact i.elim0
  | joint j _ => exact (isEmptyElim j : False).elim
  | hub j k =>
    change (∃ i, Port.hub h i = Port.hub j k) ↔ some j = some h
    constructor
    · rintro ⟨i, he⟩; cases he; rfl
    · intro he
      have hj := Option.some.inj he
      subst j
      exact ⟨k, rfl⟩

noncomputable def cappedBlockFamily (hw : 0 < w.length)
    (hn : ∀ h, 0 < (P.word (G.hubLabel h)).length) :
    BlockFamily (P.adjoinRelation w 0) (Port.label G.jointLabel)
      G.cappedRotation G.pairing.perm where
  Index := Option G.Hub
  block
    | none => G.outerBlock hw
    | some h => G.cappedHubBlock h (hn h)
  owner := G.cappedOwner
  mem_ports x i := by
    cases i with
    | none => exact G.outerBlock_mem_owner hw x
    | some h => exact G.cappedHubBlock_mem_owner h (hn h) x

theorem cappedBlockFamily_relations (hw : 0 < w.length)
    (hn : ∀ h, 0 < (P.word (G.hubLabel h)).length) :
    (G.cappedBlockFamily hw hn).relations =
      {none} + (∑ h : G.Hub, ([G.hubLabel h] : Multiset R)).map some := by
  unfold BlockFamily.relations cappedBlockFamily
  rw [Fintype.sum_option]
  simp only [G.outerBlock_labels, G.cappedHubBlock_labels]
  congr 1
  let f : Multiset R →+ Multiset (Option R) := {
    toFun := Multiset.map some
    map_zero' := rfl
    map_add' := Multiset.map_add some }
  exact (map_sum f (fun h : G.Hub => ([G.hubLabel h] : Multiset R)) Finset.univ).symm

theorem exists_diagram_of_rotationEuler_boundary
    (hw : 0 < w.length) (hn : ∀ h, 0 < (P.word (G.hubLabel h)).length)
    (hEuler : RotationEuler.count G.rotation G.pairing.perm =
      2 * Nat.card (Component G.rotation G.pairing.perm))
    (hconn : ∀ x y : G.Dart, Connected G.rotation G.pairing.perm x y)
    (hnc : G.BoundaryNoncrossing) (hsees : G.BoundarySeesComponents) :
    ∃ d : Diagram P w [], (d.labels : Multiset R) =
      ∑ h : G.Hub, ([G.hubLabel h] : Multiset R) := by
  have hnext := G.boundaryNext_eq_cyclic hnc hsees hconn
  obtain ⟨d, hd⟩ := (G.cappedBlockFamily hw hn).exists_closed_diagram
    G.pairing.involutive G.pairing.label_twin (G.cappedRotation_saturated hnext hconn hEuler)
    (fun x y => G.cappedRotation_connected (hconn x y))
  exact d.exists_punctured_diagram_of_multiset _ (hd.trans (G.cappedBlockFamily_relations hw hn))

end ThomGame.Pictures.PortGraph
