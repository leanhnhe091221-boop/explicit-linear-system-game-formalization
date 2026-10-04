module

public import ThomGame.Pictures.BottomBoundaryGraph
public import ThomGame.Pictures.BoundaryQuadCapping

/-! # Moving the top to the reversed bottom, preserving actual outer quadrilaterals -/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv RibbonConnectivity CircularPartition

variable {R S : Type*} {P : InvolutionPresentation R S}

def topBottomIndex (w : List S) : BoundaryIndex w [] ≃ BoundaryIndex [] w.reverse where
  toFun
    | .inl i => .inr (reverseWordIndex w i)
    | .inr i => i.elim0
  invFun
    | .inl i => i.elim0
    | .inr i => .inl ((reverseWordIndex w).symm i)
  left_inv x := by cases x with
    | inl i => simp
    | inr i => exact i.elim0
  right_inv x := by cases x with
    | inl i => exact i.elim0
    | inr i => simp

theorem topBottomIndex_order (w : List S) (i : BoundaryIndex w []) :
    boundaryOrderIndex [] w.reverse (topBottomIndex w i) =
      finCongr (by simp) (boundaryOrderIndex w [] i) := by
  cases i with
  | inr i => exact i.elim0
  | inl i =>
    apply Fin.ext
    change 0 + (reverseWordIndex w i).rev.val = i.val
    simp only [reverseWordIndex, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
      Fin.revPerm_apply, Fin.val_rev, List.length_reverse]
    have hi := i.isLt
    omega

theorem topBottomIndex_cyclic (w : List S) (i : BoundaryIndex w []) :
    boundaryCyclic [] w.reverse (topBottomIndex w i) = topBottomIndex w (boundaryCyclic w [] i) := by
  have hcast {m n : Nat} (h : m = n) (j : Fin m) :
      finRotate n (finCongr h j) = finCongr h (finRotate m j) := by subst n; rfl
  apply (boundaryOrderIndex [] w.reverse).injective
  rw [boundaryCyclic_index, topBottomIndex_order, topBottomIndex_order, boundaryCyclic_index, hcast]

theorem topBottomIndex_between (w : List S) (a b c : BoundaryIndex w []) :
    boundaryBetween [] w.reverse (topBottomIndex w a) (topBottomIndex w b) (topBottomIndex w c) ↔
      boundaryBetween w [] a b c := by
  simp only [boundaryBetween, topBottomIndex_order, Fin.sbtw_iff, Fin.lt_def, finCongr_apply, Fin.val_cast]

variable {w : List S} (G : PortGraph P w [])

def topBottomPorts : G.Dart ≃ Port P [] w.reverse G.Hub G.Joint G.hubLabel where
  toFun
    | .top i => .bottom (reverseWordIndex w i)
    | .bottom i => i.elim0
    | .hub h i => .hub h i
    | .joint j side => .joint j side
  invFun
    | .top i => i.elim0
    | .bottom i => .top ((reverseWordIndex w).symm i)
    | .hub h i => .hub h i
    | .joint j side => .joint j side
  left_inv x := by
    cases x with
    | top i => simp
    | bottom i => exact i.elim0
    | hub h i => rfl
    | joint j side => rfl
  right_inv x := by
    cases x with
    | top i => exact i.elim0
    | bottom i => simp
    | hub h i => rfl
    | joint j side => rfl

theorem topBottomPorts_label (x : G.Dart) :
    Port.label G.jointLabel (G.topBottomPorts x) = Port.label G.jointLabel x := by
  cases x with
  | top i => exact get_reverseWordIndex w i
  | bottom i => exact i.elim0
  | hub h i => rfl
  | joint j side => rfl

@[reducible] def topBottomGraph : PortGraph P [] w.reverse where
  Hub := G.Hub
  Joint := G.Joint
  hubFintype := G.hubFintype
  jointFintype := G.jointFintype
  hubLabel := G.hubLabel
  hubFlip := G.hubFlip
  jointLabel := G.jointLabel
  pairing := G.pairing.transport G.topBottomPorts _ G.topBottomPorts_label

theorem topBottom_pairing (x : G.Dart) :
    G.topBottomGraph.pairing.perm (G.topBottomPorts x) = G.topBottomPorts (G.pairing.perm x) := by
  change G.topBottomPorts (G.pairing.twin (G.topBottomPorts.symm (G.topBottomPorts x))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem topBottom_rotation (x : G.Dart) :
    G.topBottomGraph.rotation (G.topBottomPorts x) = G.topBottomPorts (G.rotation x) := by
  cases x with
  | top i => rfl
  | bottom i => exact i.elim0
  | hub h i => rfl
  | joint j side => rfl

theorem topBottom_circuitStep (x : G.Dart) :
    G.topBottomGraph.circuitStep (G.topBottomPorts x) = G.topBottomPorts (G.circuitStep x) := by
  change G.topBottomGraph.rotation (G.topBottomGraph.pairing.perm (G.topBottomPorts x)) = _
  rw [G.topBottom_pairing, G.topBottom_rotation]
  rfl

theorem topBottom_boundaryDart (i : BoundaryIndex w []) :
    G.topBottomPorts (G.boundaryDart i) = G.topBottomGraph.boundaryDart (topBottomIndex w i) := by
  cases i with
  | inl i => rfl
  | inr i => exact i.elim0

theorem topBottom_boundaryNext (i : BoundaryIndex w []) :
    G.topBottomGraph.boundaryNext (topBottomIndex w i) = topBottomIndex w (G.boundaryNext i) := by
  have hm : ∀ x, G.topBottomGraph.IsBoundary (G.topBottomPorts x) ↔ G.IsBoundary x := by
    intro x
    cases x with
    | top i => rfl
    | bottom i => exact i.elim0
    | hub h i => rfl
    | joint j side => rfl
  have hr := MarkedReturn.perm_preserved_of_commutes G.topBottomGraph.circuitStep
    G.topBottomGraph.IsBoundary G.circuitStep G.IsBoundary G.topBottomPorts G.topBottom_circuitStep hm
    (G.boundaryPorts i)
  have he : (⟨G.topBottomPorts (G.boundaryPorts i).val,
      (hm (G.boundaryPorts i).val).mpr (G.boundaryPorts i).property⟩ : Subtype G.topBottomGraph.IsBoundary) =
      G.topBottomGraph.boundaryPorts (topBottomIndex w i) := by
    cases i with
    | inl i => rfl
    | inr i => exact i.elim0
  rw [he, G.boundaryPorts_next, G.topBottomGraph.boundaryPorts_next] at hr
  apply G.topBottomGraph.boundaryDart.injective
  exact hr.symm.trans (G.topBottom_boundaryDart _)

theorem topBottom_boundaryNoncrossing (h : G.BoundaryNoncrossing) :
    G.topBottomGraph.BoundaryNoncrossing :=
  h.transport (topBottomIndex w) (topBottomIndex_cyclic w) G.topBottom_boundaryNext (topBottomIndex_between w)

theorem topBottom_boundarySeesComponents (h : G.BoundarySeesComponents) :
    G.topBottomGraph.BoundarySeesComponents := by
  intro x y
  obtain ⟨a, ha⟩ := G.topBottomGraph.boundaryPorts.surjective x
  obtain ⟨a, rfl⟩ := (topBottomIndex w).surjective a
  obtain ⟨b, hb⟩ := G.topBottomGraph.boundaryPorts.surjective y
  obtain ⟨b, rfl⟩ := (topBottomIndex w).surjective b
  rw [← ha, ← hb]
  have hc := connected_congr _ _ _ _ G.topBottomPorts G.topBottom_pairing G.topBottom_circuitStep
    (G.boundaryDart a) (G.boundaryDart b)
  have hf := FiniteReturn.sameCycle_congr _ _ G.topBottomPorts G.topBottom_circuitStep
    (G.boundaryDart a) (G.boundaryDart b)
  rw [G.topBottom_boundaryDart, G.topBottom_boundaryDart] at hc hf
  exact hc.symm.trans ((h (G.boundaryPorts a) (G.boundaryPorts b)).trans hf)

theorem topBottom_eulerDefect :
    eulerDefect G.topBottomGraph.pairing.perm G.topBottomGraph.circuitStep =
      eulerDefect G.pairing.perm G.circuitStep :=
  (eulerDefect_congr _ _ _ _ G.topBottomPorts G.topBottom_pairing G.topBottom_circuitStep).symm

namespace BoundaryQuadPath

variable {G} (q : G.BoundaryQuadPath)

def topBottom : G.topBottomGraph.BoundaryQuadPath where
  start := topBottomIndex w q.start
  finish := topBottomIndex w q.finish
  firstHub := q.firstHub
  secondHub := q.secondHub
  firstSlot := q.firstSlot
  secondSlot := q.secondSlot
  first_step := by
    rw [← G.topBottom_boundaryDart, G.topBottom_circuitStep, q.first_step]
    rfl
  second_step := (G.topBottom_circuitStep q.middleDart).trans (congrArg G.topBottomPorts q.second_step)
  last_step := (G.topBottom_circuitStep q.lastDart).trans
    ((congrArg G.topBottomPorts q.last_step).trans (G.topBottom_boundaryDart q.finish))
  boundary_adjacent := (topBottomIndex_cyclic w q.start).trans (congrArg (topBottomIndex w) q.boundary_adjacent)
  ends_distinct := fun he => q.ends_distinct ((topBottomIndex w).injective he)
  hubs_distinct := q.hubs_distinct

theorem topBottom_firstDart : q.topBottom.firstDart = G.topBottomPorts q.firstDart :=
  (G.topBottom_boundaryDart q.start).symm

theorem topBottom_middleDart : q.topBottom.middleDart = G.topBottomPorts q.middleDart := rfl

theorem topBottom_lastDart : q.topBottom.lastDart = G.topBottomPorts q.lastDart := rfl

end BoundaryQuadPath
end ThomGame.Pictures.PortGraph
