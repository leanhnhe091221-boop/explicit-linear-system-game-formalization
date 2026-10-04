module

public import ThomGame.Pictures.CircuitGermGraph

/-!
# Counts and signs of actual circuit germs

The germ on one side contains the circuit vertices and that side's
interior vertices. The opposite region completes the original circuit
component. The two germs together count the circuit vertices twice.
All conclusions refer to that component, not to unrelated components.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open scoped BigOperators Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {G : PortGraph P [] []} (C : G.SimpleCircuit)

theorem germ_hub_sum {B : Type*} [AddCommMonoid B] (s : Bool) (w : G.Hub → B) :
    (∑ h : C.GermHub s, w h.val) = (∑ h : C.CircuitHub, w h.val) +
      (∑ h : C.InteriorHub s, w h.val) := by
  rw [subtype_sum_indicator, subtype_sum_indicator, subtype_sum_indicator,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _
  let x : G.Vertex := .inr (.inl h)
  change (if C.GermVertex s x then w h else 0) =
    (if C.OnCircuitVertex x then w h else 0) + (if C.InteriorVertex s x then w h else 0)
  by_cases hc : C.OnCircuitVertex x
  · have hi : ¬ C.InteriorVertex s x := fun hi => hi.1 hc
    simp [GermVertex, hc, hi]
  · simp [GermVertex, hc]

theorem germ_hub_card (s : Bool) :
    Nat.card (C.GermHub s) = Nat.card C.CircuitHub + Nat.card (C.InteriorHub s) := by
  simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
    Nat.card_eq_fintype_card] using C.germ_hub_sum s (fun _ => (1 : Nat))

variable (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
  2 * Nat.card (RibbonConnectivity.Component G.circuitStep G.pairing.perm))

include hEuler in
theorem germ_region_hub_sum {B : Type*} [AddCommMonoid B] (s : Bool) (w : G.Hub → B) :
    (∑ h : C.GermHub s, w h.val) + (∑ h : C.InteriorHub (!s), w h.val) =
      ∑ h : C.ComponentHub, w h.val := by
  rw [C.germ_hub_sum, C.component_hub_sum hEuler]
  cases s
  · rfl
  · exact add_right_comm _ _ _

include hEuler in
theorem germ_pair_hub_sum {B : Type*} [AddCommMonoid B] (w : G.Hub → B) :
    (∑ h : C.GermHub false, w h.val) + (∑ h : C.GermHub true, w h.val) =
      (∑ h : C.ComponentHub, w h.val) + (∑ h : C.CircuitHub, w h.val) := by
  rw [C.germ_hub_sum, C.germ_hub_sum, C.component_hub_sum hEuler]
  ac_rfl

include hEuler in
theorem germGraph_character (s : Bool) (r : R) :
    (C.germGraph hEuler s).character r =
      (Nat.card {h : G.Hub // C.GermVertex s (.inr (.inl h)) ∧ G.hubLabel h = r} : ZMod 2) := by
  unfold PortGraph.character
  congr 1
  exact Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun h : G.Hub => C.GermVertex s (.inr (.inl h))) (fun h => G.hubLabel h = r))

include hEuler in
theorem germGraph_sign (s : Bool) :
    (C.germGraph hEuler s).sign =
      (∑ h : C.CircuitHub, P.parity (G.hubLabel h.val)) + (C.regionGraph hEuler s).sign :=
  C.germ_hub_sum s (fun h => P.parity (G.hubLabel h))

include hEuler in
theorem germGraph_character_partition [DecidableEq R] (s : Bool) (r : R) :
    (C.germGraph hEuler s).character r =
      (∑ h : C.CircuitHub, if G.hubLabel h.val = r then (1 : ZMod 2) else 0) +
        (C.regionGraph hEuler s).character r := by
  rw [PortGraph.character_eq_sum, PortGraph.character_eq_sum]
  exact C.germ_hub_sum s (fun h => if G.hubLabel h = r then (1 : ZMod 2) else 0)

include hEuler in
theorem germGraph_region_sign (s : Bool) :
    (C.germGraph hEuler s).sign + (C.regionGraph hEuler (!s)).sign =
      ∑ h : C.ComponentHub, P.parity (G.hubLabel h.val) :=
  C.germ_region_hub_sum hEuler s (fun h => P.parity (G.hubLabel h))

include hEuler in
theorem germGraph_region_character [DecidableEq R] (s : Bool) (r : R) :
    (C.germGraph hEuler s).character r + (C.regionGraph hEuler (!s)).character r =
      ∑ h : C.ComponentHub, if G.hubLabel h.val = r then (1 : ZMod 2) else 0 := by
  rw [PortGraph.character_eq_sum, PortGraph.character_eq_sum]
  exact C.germ_region_hub_sum hEuler s (fun h => if G.hubLabel h = r then (1 : ZMod 2) else 0)

include hEuler in
theorem germGraph_pair_sign :
    (C.germGraph hEuler false).sign + (C.germGraph hEuler true).sign =
      (∑ h : C.ComponentHub, P.parity (G.hubLabel h.val)) +
        (∑ h : C.CircuitHub, P.parity (G.hubLabel h.val)) :=
  C.germ_pair_hub_sum hEuler (fun h => P.parity (G.hubLabel h))

include hEuler in
/-- The componentwise parity step used in the stellar-cycle argument. -/
theorem exists_germGraph_sign_zero
    (hCircuit : (∑ h : C.CircuitHub, P.parity (G.hubLabel h.val)) = 0)
    (hComponent : (∑ h : C.ComponentHub, P.parity (G.hubLabel h.val)) = 1) :
    ∃ s, (C.germGraph hEuler s).sign = 0 := by
  have hs := C.germGraph_pair_sign hEuler
  rw [hCircuit, hComponent, add_zero] at hs
  rcases InvolutionDerivation.parity_cases (C.germGraph hEuler false).sign with hf | hf
  · exact ⟨false, hf⟩
  · rcases InvolutionDerivation.parity_cases (C.germGraph hEuler true).sign with ht | ht
    · exact ⟨true, ht⟩
    · have hz : (1 : ZMod 2) + 1 = 0 := by decide +kernel
      rw [hf, ht, hz] at hs
      exact (zero_ne_one hs).elim

include hEuler in
theorem germGraph_charge_balance (s : Bool) (χ : S → ZMod 2) :
    (∑ h : C.CircuitHub, ((P.word (G.hubLabel h.val)).map χ).sum) +
      (∑ h : C.InteriorHub s, ((P.word (G.hubLabel h.val)).map χ).sum) =
        ((C.frontierWord (!s)).map χ).sum := by
  rw [← C.germ_hub_sum s (fun h => ((P.word (G.hubLabel h)).map χ).sum)]
  have hc := (C.germGraph hEuler s).charge_balance χ
  simpa only [List.map_nil, List.sum_nil, zero_add] using hc

end ThomGame.Pictures.PortGraph.SimpleCircuit
