module

public import ThomGame.Pictures.ConnectedGraphRealization

/-!
# Exchanging the top and bottom boundary names of a port graph

Only the boundary port constructors are exchanged. Hub rotations and
edge pairings are transported unchanged. This is an equivalence of
rotation graphs, not a claim that the specified boundary circular order
is preserved. The actual boundary-return permutation is transported.
-/

@[expose] public section
namespace ThomGame.Pictures

open Equiv RibbonConnectivity

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}

namespace Port

variable {H J : Type} {hubLabel : H → R}

def swapBoundary : Port P u v H J hubLabel ≃ Port P v u H J hubLabel where
  toFun
    | .top i => .bottom i
    | .bottom i => .top i
    | .hub h i => .hub h i
    | .joint j b => .joint j b
  invFun
    | .top i => .bottom i
    | .bottom i => .top i
    | .hub h i => .hub h i
    | .joint j b => .joint j b
  left_inv a := by cases a <;> rfl
  right_inv a := by cases a <;> rfl

theorem swapBoundary_label (jointLabel : J → S) (a : Port P u v H J hubLabel) :
    label jointLabel (swapBoundary a) = label jointLabel a := by cases a <;> rfl

end Port

namespace PortGraph

variable (G : PortGraph P u v)

def swapBoundary : PortGraph P v u where
  Hub := G.Hub
  Joint := G.Joint
  hubLabel := G.hubLabel
  hubFlip := G.hubFlip
  jointLabel := G.jointLabel
  pairing := G.pairing.transport Port.swapBoundary _ (Port.swapBoundary_label G.jointLabel)

def swapBoundaryPorts : G.Dart ≃ G.swapBoundary.Dart := Port.swapBoundary

theorem swapBoundary_pairing (a : G.Dart) :
    G.swapBoundary.pairing.perm (G.swapBoundaryPorts a) = G.swapBoundaryPorts (G.pairing.perm a) := by
  change Port.swapBoundary (G.pairing.twin (Port.swapBoundary.symm (Port.swapBoundary a))) =
    Port.swapBoundary (G.pairing.twin a)
  rw [Equiv.symm_apply_apply]

theorem swapBoundary_rotation (a : G.Dart) :
    G.swapBoundary.rotation (G.swapBoundaryPorts a) = G.swapBoundaryPorts (G.rotation a) := by
  cases a <;> rfl

theorem swapBoundary_circuitStep (a : G.Dart) :
    G.swapBoundary.circuitStep (G.swapBoundaryPorts a) = G.swapBoundaryPorts (G.circuitStep a) := by
  rw [G.swapBoundary.circuitStep_apply, G.circuitStep_apply]
  change G.swapBoundary.rotation (G.swapBoundary.pairing.perm (G.swapBoundaryPorts a)) = _
  rw [G.swapBoundary_pairing, G.swapBoundary_rotation]
  rfl

theorem swapBoundary_boundaryDart (i : BoundaryIndex u v) :
    G.swapBoundaryPorts (G.boundaryDart i) =
      G.swapBoundary.boundaryDart (Equiv.sumComm _ _ i) := by cases i <;> rfl

theorem swapBoundary_next (i : BoundaryIndex u v) :
    G.swapBoundary.boundaryNext (Equiv.sumComm _ _ i) = Equiv.sumComm _ _ (G.boundaryNext i) := by
  have hm : ∀ a, G.swapBoundary.IsBoundary (G.swapBoundaryPorts a) ↔ G.IsBoundary a := by
    intro a
    cases a <;> rfl
  have hr := MarkedReturn.perm_preserved_of_commutes G.swapBoundary.circuitStep
    G.swapBoundary.IsBoundary G.circuitStep G.IsBoundary G.swapBoundaryPorts
    G.swapBoundary_circuitStep hm (G.boundaryPorts i)
  have he : (⟨G.swapBoundaryPorts (G.boundaryPorts i).val,
      (hm (G.boundaryPorts i).val).mpr (G.boundaryPorts i).property⟩ :
      Subtype G.swapBoundary.IsBoundary) =
      G.swapBoundary.boundaryPorts (Equiv.sumComm _ _ i) := by cases i <;> rfl
  rw [he, G.boundaryPorts_next, G.swapBoundary.boundaryPorts_next] at hr
  apply G.swapBoundary.boundaryDart.injective
  rw [← G.swapBoundary_boundaryDart]
  exact hr.symm

theorem swapBoundary_connected
    (hconn : ∀ a b : G.Dart, Connected G.rotation G.pairing.perm a b) :
    ∀ a b : G.swapBoundary.Dart, Connected G.swapBoundary.rotation G.swapBoundary.pairing.perm a b := by
  intro a b
  obtain ⟨a, rfl⟩ := G.swapBoundaryPorts.surjective a
  obtain ⟨b, rfl⟩ := G.swapBoundaryPorts.surjective b
  exact (hconn a b).map G.swapBoundaryPorts G.swapBoundary_rotation G.swapBoundary_pairing

theorem swapBoundary_rotationEuler
    (hEuler : RotationEuler.count G.rotation G.pairing.perm =
      2 * Nat.card (Component G.rotation G.pairing.perm)) :
    RotationEuler.count G.swapBoundary.rotation G.swapBoundary.pairing.perm =
      2 * Nat.card (Component G.swapBoundary.rotation G.swapBoundary.pairing.perm) := by
  rw [RotationEuler.count_congr _ _ G.swapBoundary.rotation G.swapBoundary.pairing.perm
      G.swapBoundaryPorts G.swapBoundary_rotation G.swapBoundary_pairing,
    Nat.card_congr (componentCongrEquiv _ _ G.swapBoundary.rotation G.swapBoundary.pairing.perm
      G.swapBoundaryPorts G.swapBoundary_rotation G.swapBoundary_pairing)] at hEuler
  exact hEuler

end PortGraph
end ThomGame.Pictures
