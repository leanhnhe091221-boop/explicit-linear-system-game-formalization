module

public import ThomGame.Pictures.CappedGraphRealization

/-! # Relabelling a port graph after adjoining one relation -/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv RibbonConnectivity

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
  (G : PortGraph P u v) (w : List S)

def adjoinPorts : G.Dart ≃ Port (P.adjoinRelation w 0) u v G.Hub G.Joint
    (fun h => some (G.hubLabel h)) where
  toFun
    | .top i => .top i
    | .bottom i => .bottom i
    | .hub h i => .hub h i
    | .joint j side => .joint j side
  invFun
    | .top i => .top i
    | .bottom i => .bottom i
    | .hub h i => .hub h i
    | .joint j side => .joint j side
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl

theorem adjoinPorts_label (x : G.Dart) :
    Port.label G.jointLabel (G.adjoinPorts w x) = Port.label G.jointLabel x := by cases x <;> rfl

@[reducible] def adjoinGraph : PortGraph (P.adjoinRelation w 0) u v where
  Hub := G.Hub
  Joint := G.Joint
  hubFintype := G.hubFintype
  jointFintype := G.jointFintype
  hubLabel h := some (G.hubLabel h)
  hubFlip := G.hubFlip
  jointLabel := G.jointLabel
  pairing := G.pairing.transport (G.adjoinPorts w) _ (G.adjoinPorts_label w)

theorem adjoin_pairing (x : G.Dart) :
    (G.adjoinGraph w).pairing.perm (G.adjoinPorts w x) = G.adjoinPorts w (G.pairing.perm x) := by
  change G.adjoinPorts w (G.pairing.twin ((G.adjoinPorts w).symm (G.adjoinPorts w x))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem adjoin_rotation (x : G.Dart) :
    (G.adjoinGraph w).rotation (G.adjoinPorts w x) = G.adjoinPorts w (G.rotation x) := by
  cases x <;> rfl

theorem adjoin_circuitStep (x : G.Dart) :
    (G.adjoinGraph w).circuitStep (G.adjoinPorts w x) = G.adjoinPorts w (G.circuitStep x) := by
  change (G.adjoinGraph w).rotation ((G.adjoinGraph w).pairing.perm (G.adjoinPorts w x)) = _
  rw [G.adjoin_pairing, G.adjoin_rotation]
  rfl

theorem adjoin_boundaryDart (i : BoundaryIndex u v) :
    G.adjoinPorts w (G.boundaryDart i) = (G.adjoinGraph w).boundaryDart i := by cases i <;> rfl

theorem adjoin_boundaryNext : (G.adjoinGraph w).boundaryNext = G.boundaryNext := by
  ext i
  have hm : ∀ x, (G.adjoinGraph w).IsBoundary (G.adjoinPorts w x) ↔ G.IsBoundary x := by
    intro x
    cases x <;> rfl
  have hr := MarkedReturn.perm_preserved_of_commutes (G.adjoinGraph w).circuitStep
    (G.adjoinGraph w).IsBoundary G.circuitStep G.IsBoundary (G.adjoinPorts w)
    (G.adjoin_circuitStep w) hm (G.boundaryPorts i)
  have he : (⟨G.adjoinPorts w (G.boundaryPorts i).val,
      (hm (G.boundaryPorts i).val).mpr (G.boundaryPorts i).property⟩ :
      Subtype (G.adjoinGraph w).IsBoundary) = (G.adjoinGraph w).boundaryPorts i := by cases i <;> rfl
  rw [he, G.boundaryPorts_next, (G.adjoinGraph w).boundaryPorts_next] at hr
  apply (G.adjoinGraph w).boundaryDart.injective
  exact hr.symm.trans (G.adjoin_boundaryDart w _)

theorem adjoin_boundaryNoncrossing (h : G.BoundaryNoncrossing) :
    (G.adjoinGraph w).BoundaryNoncrossing := by
  unfold BoundaryNoncrossing
  rw [G.adjoin_boundaryNext]
  exact h

theorem adjoin_boundarySeesComponents (h : G.BoundarySeesComponents) :
    (G.adjoinGraph w).BoundarySeesComponents := by
  intro x y
  obtain ⟨a, rfl⟩ := (G.adjoinGraph w).boundaryPorts.surjective x
  obtain ⟨b, rfl⟩ := (G.adjoinGraph w).boundaryPorts.surjective y
  have hc := connected_congr G.pairing.perm G.circuitStep (G.adjoinGraph w).pairing.perm
    (G.adjoinGraph w).circuitStep (G.adjoinPorts w) (G.adjoin_pairing w) (G.adjoin_circuitStep w)
    (G.boundaryDart a) (G.boundaryDart b)
  have hf := FiniteReturn.sameCycle_congr G.circuitStep (G.adjoinGraph w).circuitStep
    (G.adjoinPorts w) (G.adjoin_circuitStep w) (G.boundaryDart a) (G.boundaryDart b)
  rw [G.adjoin_boundaryDart, G.adjoin_boundaryDart] at hc hf
  exact hc.symm.trans ((h (G.boundaryPorts a) (G.boundaryPorts b)).trans hf)

theorem adjoin_eulerDefect :
    eulerDefect (G.adjoinGraph w).pairing.perm (G.adjoinGraph w).circuitStep =
      eulerDefect G.pairing.perm G.circuitStep :=
  (eulerDefect_congr _ _ _ _ (G.adjoinPorts w) (G.adjoin_pairing w) (G.adjoin_circuitStep w)).symm

end ThomGame.Pictures.PortGraph
