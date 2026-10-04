module

public import ThomGame.Pictures.ReducedMinimalRecovery
public import ThomGame.Pictures.MinimalRegionDiagrams

/-! # Germ and complementary region partition all hubs of a connected graph -/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open RibbonConnectivity
open scoped BigOperators Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {G : PortGraph P [] []}
  (C : G.SimpleCircuit) (hc : ∀ x y : G.Vertex, G.Reachable x y)

include hc in
theorem component_hub_sum_of_all_reachable {B : Type*} [AddCommMonoid B] (w : G.Hub → B) :
    (∑ h : C.ComponentHub, w h.val) = ∑ h : G.Hub, w h := by
  rw [subtype_sum_indicator]
  apply Finset.sum_congr rfl
  intro h _
  have hx : C.InCircuitComponent (.inr (.inl h)) :=
    (C.inCircuitComponent_iff_reachable _).mpr (hc _ _)
  simp only [hx, ite_true]

include hc in
theorem component_hub_card_of_all_reachable : Fintype.card C.ComponentHub = Fintype.card G.Hub := by
  simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] using
    C.component_hub_sum_of_all_reachable hc (fun _ => (1 : Nat))

variable (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
  2 * Nat.card (Component G.circuitStep G.pairing.perm))

include hc hEuler in
theorem germ_region_hub_card_of_connected (s : Bool) :
    Fintype.card (C.germGraph hEuler s).Hub + Fintype.card (C.regionGraph hEuler (!s)).Hub =
      Fintype.card G.Hub :=
  (C.germ_region_hub_card hEuler s).trans (C.component_hub_card_of_all_reachable hc)

include hc hEuler in
theorem germ_region_sign_of_connected (s : Bool) :
    (C.germGraph hEuler s).sign + (C.regionGraph hEuler (!s)).sign = G.sign :=
  (C.germGraph_region_sign hEuler s).trans
    (C.component_hub_sum_of_all_reachable hc (fun h => P.parity (G.hubLabel h)))

end ThomGame.Pictures.PortGraph.SimpleCircuit
