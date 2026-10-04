module

public import ThomGame.Pictures.BoundaryCapEuler

/-!
# Moving a lower boundary to the top in its actual circular order

The lower word becomes the reversed upper word, with explicit reversed
indices. Pairing, hub orientations and rotations are transported exactly.
This preserves the specified boundary circular order and its invariants.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv RibbonConnectivity CircularPartition

variable {R S : Type*} {P : InvolutionPresentation R S}

def reverseWordIndex (w : List S) : Fin w.length ≃ Fin w.reverse.length :=
  Fin.revPerm.trans (finCongr (by simp))

theorem get_reverseWordIndex (w : List S) (i : Fin w.length) :
    w.reverse[reverseWordIndex w i] = w[i] := by
  change w.reverse[(reverseWordIndex w i).val] = w[i.val]
  rw [List.getElem_reverse]
  congr 1
  simp only [reverseWordIndex, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
    Fin.revPerm_apply, Fin.val_rev]
  have hi := i.isLt
  omega

def bottomTopIndex (w : List S) : BoundaryIndex [] w ≃ BoundaryIndex w.reverse [] where
  toFun
    | .inl i => i.elim0
    | .inr i => .inl (reverseWordIndex w i)
  invFun
    | .inl i => .inr ((reverseWordIndex w).symm i)
    | .inr i => i.elim0
  left_inv x := by cases x with
    | inl i => exact i.elim0
    | inr i => simp
  right_inv x := by cases x with
    | inl i => simp
    | inr i => exact i.elim0

theorem bottomTopIndex_order (w : List S) (i : BoundaryIndex [] w) :
    boundaryOrderIndex w.reverse [] (bottomTopIndex w i) =
      finCongr (by simp) (boundaryOrderIndex [] w i) := by
  cases i with
  | inl i => exact i.elim0
  | inr i =>
    apply Fin.ext
    change (reverseWordIndex w i).val = 0 + i.rev.val
    simp [reverseWordIndex]

theorem bottomTopIndex_cyclic (w : List S) (i : BoundaryIndex [] w) :
    boundaryCyclic w.reverse [] (bottomTopIndex w i) = bottomTopIndex w (boundaryCyclic [] w i) := by
  have hcast {m n : Nat} (h : m = n) (j : Fin m) :
      finRotate n (finCongr h j) = finCongr h (finRotate m j) := by subst n; rfl
  apply (boundaryOrderIndex w.reverse []).injective
  rw [boundaryCyclic_index, bottomTopIndex_order, bottomTopIndex_order, boundaryCyclic_index, hcast]

theorem bottomTopIndex_between (w : List S) (a b c : BoundaryIndex [] w) :
    boundaryBetween w.reverse [] (bottomTopIndex w a) (bottomTopIndex w b) (bottomTopIndex w c) ↔
      boundaryBetween [] w a b c := by
  simp only [boundaryBetween, bottomTopIndex_order, Fin.sbtw_iff, Fin.lt_def, finCongr_apply, Fin.val_cast]

variable {w : List S} (G : PortGraph P [] w)

def bottomTopPorts : G.Dart ≃ Port P w.reverse [] G.Hub G.Joint G.hubLabel where
  toFun
    | .top i => i.elim0
    | .bottom i => .top (reverseWordIndex w i)
    | .hub h i => .hub h i
    | .joint j side => .joint j side
  invFun
    | .top i => .bottom ((reverseWordIndex w).symm i)
    | .bottom i => i.elim0
    | .hub h i => .hub h i
    | .joint j side => .joint j side
  left_inv x := by
    cases x with
    | top i => exact i.elim0
    | bottom i => simp
    | hub h i => rfl
    | joint j side => rfl
  right_inv x := by
    cases x with
    | top i => simp
    | bottom i => exact i.elim0
    | hub h i => rfl
    | joint j side => rfl

theorem bottomTopPorts_label (x : G.Dart) :
    Port.label G.jointLabel (G.bottomTopPorts x) = Port.label G.jointLabel x := by
  cases x with
  | top i => exact i.elim0
  | bottom i => exact get_reverseWordIndex w i
  | hub h i => rfl
  | joint j side => rfl

@[reducible] def bottomTopGraph : PortGraph P w.reverse [] where
  Hub := G.Hub
  Joint := G.Joint
  hubFintype := G.hubFintype
  jointFintype := G.jointFintype
  hubLabel := G.hubLabel
  hubFlip := G.hubFlip
  jointLabel := G.jointLabel
  pairing := G.pairing.transport G.bottomTopPorts _ G.bottomTopPorts_label

theorem bottomTop_pairing (x : G.Dart) :
    G.bottomTopGraph.pairing.perm (G.bottomTopPorts x) = G.bottomTopPorts (G.pairing.perm x) := by
  change G.bottomTopPorts (G.pairing.twin (G.bottomTopPorts.symm (G.bottomTopPorts x))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem bottomTop_rotation (x : G.Dart) :
    G.bottomTopGraph.rotation (G.bottomTopPorts x) = G.bottomTopPorts (G.rotation x) := by
  cases x with
  | top i => exact i.elim0
  | bottom i => rfl
  | hub h i => rfl
  | joint j side => rfl

theorem bottomTop_circuitStep (x : G.Dart) :
    G.bottomTopGraph.circuitStep (G.bottomTopPorts x) = G.bottomTopPorts (G.circuitStep x) := by
  change G.bottomTopGraph.rotation (G.bottomTopGraph.pairing.perm (G.bottomTopPorts x)) = _
  rw [G.bottomTop_pairing, G.bottomTop_rotation]
  rfl

theorem bottomTop_boundaryDart (i : BoundaryIndex [] w) :
    G.bottomTopPorts (G.boundaryDart i) = G.bottomTopGraph.boundaryDart (bottomTopIndex w i) := by
  cases i with
  | inl i => exact i.elim0
  | inr i => rfl

theorem bottomTop_boundaryNext (i : BoundaryIndex [] w) :
    G.bottomTopGraph.boundaryNext (bottomTopIndex w i) = bottomTopIndex w (G.boundaryNext i) := by
  have hm : ∀ x, G.bottomTopGraph.IsBoundary (G.bottomTopPorts x) ↔ G.IsBoundary x := by
    intro x
    cases x with
    | top i => exact i.elim0
    | bottom i => rfl
    | hub h i => rfl
    | joint j side => rfl
  have hr := MarkedReturn.perm_preserved_of_commutes G.bottomTopGraph.circuitStep
    G.bottomTopGraph.IsBoundary G.circuitStep G.IsBoundary G.bottomTopPorts G.bottomTop_circuitStep hm
    (G.boundaryPorts i)
  have he : (⟨G.bottomTopPorts (G.boundaryPorts i).val,
      (hm (G.boundaryPorts i).val).mpr (G.boundaryPorts i).property⟩ : Subtype G.bottomTopGraph.IsBoundary) =
      G.bottomTopGraph.boundaryPorts (bottomTopIndex w i) := by
    cases i with
    | inl i => exact i.elim0
    | inr i => rfl
  rw [he, G.boundaryPorts_next, G.bottomTopGraph.boundaryPorts_next] at hr
  apply G.bottomTopGraph.boundaryDart.injective
  exact hr.symm.trans (G.bottomTop_boundaryDart _)

theorem bottomTop_boundaryNoncrossing (h : G.BoundaryNoncrossing) :
    G.bottomTopGraph.BoundaryNoncrossing :=
  h.transport (bottomTopIndex w) (bottomTopIndex_cyclic w) G.bottomTop_boundaryNext (bottomTopIndex_between w)

theorem bottomTop_boundarySeesComponents (h : G.BoundarySeesComponents) :
    G.bottomTopGraph.BoundarySeesComponents := by
  intro x y
  obtain ⟨a, ha⟩ := G.bottomTopGraph.boundaryPorts.surjective x
  obtain ⟨a, rfl⟩ := (bottomTopIndex w).surjective a
  obtain ⟨b, hb⟩ := G.bottomTopGraph.boundaryPorts.surjective y
  obtain ⟨b, rfl⟩ := (bottomTopIndex w).surjective b
  rw [← ha, ← hb]
  have hc := connected_congr _ _ _ _ G.bottomTopPorts G.bottomTop_pairing G.bottomTop_circuitStep
    (G.boundaryDart a) (G.boundaryDart b)
  have hf := FiniteReturn.sameCycle_congr _ _ G.bottomTopPorts G.bottomTop_circuitStep
    (G.boundaryDart a) (G.boundaryDart b)
  rw [G.bottomTop_boundaryDart, G.bottomTop_boundaryDart] at hc hf
  exact hc.symm.trans ((h (G.boundaryPorts a) (G.boundaryPorts b)).trans hf)

theorem bottomTop_eulerDefect :
    eulerDefect G.bottomTopGraph.pairing.perm G.bottomTopGraph.circuitStep =
      eulerDefect G.pairing.perm G.circuitStep :=
  (eulerDefect_congr _ _ _ _ G.bottomTopPorts G.bottomTop_pairing G.bottomTop_circuitStep).symm

end ThomGame.Pictures.PortGraph
