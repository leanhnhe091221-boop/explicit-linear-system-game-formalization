module

public import ThomGame.Pictures.CircuitRegionGraph
public import ThomGame.Pictures.GraphCharge

/-! # Actual vertex counts and charge balance of a circuit region graph -/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open scoped BigOperators Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {G : PortGraph P [] []} (C : G.SimpleCircuit)
  (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
    2 * Nat.card (RibbonConnectivity.Component G.circuitStep G.pairing.perm))

include hEuler in
theorem regionGraph_character (s : Bool) (r : R) :
    (C.regionGraph hEuler s).character r =
      (Nat.card {h : G.Hub // C.InteriorVertex s (.inr (.inl h)) ∧ G.hubLabel h = r} : ZMod 2) := by
  unfold PortGraph.character
  congr 1
  exact Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun h : G.Hub => C.InteriorVertex s (.inr (.inl h))) (fun h => G.hubLabel h = r))

include hEuler in
theorem regionGraph_sign (s : Bool) :
    (C.regionGraph hEuler s).sign =
      ∑ h : C.InteriorHub s, P.parity (G.hubLabel h.val) := rfl

include hEuler in
theorem regionGraph_hub_card (s : Bool) :
    Nat.card (C.regionGraph hEuler s).Hub =
      Nat.card {h : G.Hub // C.InteriorVertex s (.inr (.inl h))} := rfl

include hEuler in
theorem regionGraph_charge_balance (s : Bool) (χ : S → ZMod 2) :
    (∑ h : C.InteriorHub s, ((P.word (G.hubLabel h.val)).map χ).sum) =
      ((C.frontierWord s).map χ).sum := by
  have hc := (C.regionGraph hEuler s).charge_balance χ
  simpa only [List.map_nil, List.sum_nil, add_zero] using hc

end ThomGame.Pictures.PortGraph.SimpleCircuit
