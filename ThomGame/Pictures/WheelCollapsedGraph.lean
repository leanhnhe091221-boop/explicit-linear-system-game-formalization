module

public import ThomGame.Pictures.WheelGraphAtlas
public import ThomGame.Finite.WheelRelationWords
public import ThomGame.Pictures.ConnectedGraphRealization

/-!
# The actual collapsed graph on original relation vertices

Every auxiliary wheel component becomes one vertex labelled by its
original relation. Its ports are the original ordinary-generator ports,
and its edge pairing is transported from the unchanged ordinary edges.
Uniform wheel orientation makes its rotation the proved face return.
-/

@[expose] public section
namespace ThomGame.Wheel.Family.GraphAtlas

open Pictures PortGraph Equiv RibbonConnectivity
open scoped Classical BigOperators

variable {R V R' V' : Type*} {F : Family R V}
  {rows : F.Row ≃ R'} {cols : F.Col ≃ V'}
  {G : SolutionGroup.RowGraph (F.system.reindex rows cols) [] []}
  (D : F.GraphAtlas rows cols G)

abbrev CollapsedPort := Port F.presentation [] [] D.Component Empty D.wheel

def collapsedPortIndices : D.CollapsedPort ≃ ((c : D.Component) × Fin (F.size (D.wheel c))) where
  toFun
    | .top i => i.elim0
    | .bottom i => i.elim0
    | .joint j _ => nomatch j
    | .hub c i => ⟨c, F.presentationIndex (D.wheel c) i⟩
  invFun x := .hub x.1 ((F.presentationIndex (D.wheel x.1)).symm x.2)
  left_inv p := by
    cases p with
    | top i => exact i.elim0
    | bottom i => exact i.elim0
    | joint j _ => exact j.elim
    | hub c i => exact congrArg (Port.hub c) ((F.presentationIndex (D.wheel c)).symm_apply_apply i)
  right_inv x := by
    rcases x with ⟨c, i⟩
    exact congrArg (Sigma.mk c) ((F.presentationIndex (D.wheel c)).apply_symm_apply i)

variable [IsEmpty G.Joint]

noncomputable def collapsedPortEquiv : D.CollapsedPort ≃ F.OrdinaryPort rows cols G :=
  D.collapsedPortIndices.trans D.outerPortEquiv

theorem collapsedPort_label (p : D.CollapsedPort) :
    F.ordinaryLabel rows cols G (D.collapsedPortEquiv p) = Port.label Empty.elim p := by
  cases p with
  | top i => exact i.elim0
  | bottom i => exact i.elim0
  | joint j _ => exact j.elim
  | hub c i =>
    change F.ordinaryLabel rows cols G ((D.lift c).ordinaryPort (F.presentationIndex (D.wheel c) i)) = _
    exact ((D.lift c).ordinaryPort_label _).trans (F.presentation_get (D.wheel c) i).symm

noncomputable def collapsedGraph : PortGraph F.presentation [] [] where
  Hub := D.Component
  Joint := Empty
  hubLabel := D.wheel
  hubFlip c := !(G.hubFlip ((D.lift c).hub 0 0))
  jointLabel := Empty.elim
  pairing := (F.ordinaryPairing rows cols G).transport D.collapsedPortEquiv.symm
    (Port.label Empty.elim) (fun x => by
      have he := D.collapsedPort_label (D.collapsedPortEquiv.symm x)
      rw [D.collapsedPortEquiv.apply_symm_apply] at he
      exact he.symm)

theorem collapsed_pairing (p : D.collapsedGraph.Dart) :
    D.collapsedPortEquiv (D.collapsedGraph.pairing.twin p) =
      (F.ordinaryPairing rows cols G).twin (D.collapsedPortEquiv p) :=
  D.collapsedPortEquiv.apply_symm_apply _

theorem collapsed_rotation
    (hu : ∀ (c : D.Component) (j : Fin (F.size (D.wheel c))) (k : Fin 3),
      G.hubFlip ((D.lift c).hub j k) = G.hubFlip ((D.lift c).hub 0 0))
    (p : D.collapsedGraph.Dart) :
    D.collapsedPortEquiv (D.collapsedGraph.rotation p) =
      F.ordinaryRotation rows cols G (D.collapsedPortEquiv p) := by
  cases p with
  | top i => exact i.elim0
  | bottom i => exact i.elim0
  | joint j _ => exact j.elim
  | hub c i =>
    rw [D.collapsedGraph.rotation_hub]
    change (D.lift c).ordinaryPort (F.presentationIndex (D.wheel c)
      ((if !(G.hubFlip ((D.lift c).hub 0 0)) then (finRotate _).symm else finRotate _) i)) =
        F.ordinaryRotation rows cols G ((D.lift c).ordinaryPort (F.presentationIndex (D.wheel c) i))
    rw [(D.lift c).ordinaryRotation_apply _ (hu c)]
    cases hf : G.hubFlip ((D.lift c).hub 0 0)
    · simp only [Bool.not_false, ite_true, Bool.false_eq_true, ite_false]
      exact congrArg (D.lift c).ordinaryPort (F.presentationIndex_rotate_symm (D.wheel c) i)
    · simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
      exact congrArg (D.lift c).ordinaryPort (F.presentationIndex_rotate (D.wheel c) i)

theorem collapsed_euler
    (hu : ∀ (c : D.Component) (j : Fin (F.size (D.wheel c))) (k : Fin 3),
      G.hubFlip ((D.lift c).hub j k) = G.hubFlip ((D.lift c).hub 0 0))
    (he : eulerDefect G.pairing.perm G.circuitStep = 0) :
    eulerDefect D.collapsedGraph.pairing.perm D.collapsedGraph.circuitStep = 0 := by
  apply D.collapsedGraph.rotationEuler_saturated_iff.mp
  have hr := D.collapsed_rotation hu
  have ht := D.collapsed_pairing
  rw [RotationEuler.count_congr D.collapsedGraph.rotation D.collapsedGraph.pairing.perm
    (F.ordinaryRotation rows cols G) (F.ordinaryPairing rows cols G).perm D.collapsedPortEquiv
    (fun p => (hr p).symm) (fun p => (ht p).symm)]
  have hc := Nat.card_congr (componentCongrEquiv D.collapsedGraph.rotation D.collapsedGraph.pairing.perm
    (F.ordinaryRotation rows cols G) (F.ordinaryPairing rows cols G).perm D.collapsedPortEquiv
    (fun p => (hr p).symm) (fun p => (ht p).symm))
  rw [hc]
  exact F.ordinaryRotation_saturated rows cols G he

theorem collapsed_sign : D.collapsedGraph.sign = G.sign := by
  change (∑ c : D.Component, F.parity (D.wheel c)) =
    ∑ h : G.Hub, (F.system.reindex rows cols).rhs (G.hubLabel h)
  exact D.rhs_sum.symm

end ThomGame.Wheel.Family.GraphAtlas
