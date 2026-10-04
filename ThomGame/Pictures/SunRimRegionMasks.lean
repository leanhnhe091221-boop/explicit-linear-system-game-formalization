module

public import ThomGame.Pictures.SunRestoredRegions
public import ThomGame.Pictures.SunRimSectors

/-!
# The region formulas apply to the actual rim cut

The complement of a simple circuit's marked ports is an invariant edge
mask, and its retained-edge permutation is exactly the existing cut
pairing. Actual sun rim circuits never mark a spoke port, so restoring
the selected spoke recovers this cut pairing with no additional premise.
On the switched graph the transported marking is used; it is not assumed
to be a single new rim circuit in the split case.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv RibbonConnectivity
open scoped Classical

namespace SimpleCircuit

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
  {G : PortGraph P u v} (C : G.SimpleCircuit)

theorem cutPairing_eq_retainEdges : C.cutPairing =
    RotationEuler.retainEdges G.pairing.perm (fun x => ¬ C.Marked x)
      (fun x => not_congr (C.marked_twin_iff x)) := by
  ext x
  rw [RotationEuler.retainEdges_apply]
  by_cases hx : C.Marked x
  · rw [C.cutPairing_of_marked hx, ite_eq_right (not_not.mpr hx)]
  · rw [C.cutPairing_of_unmarked x hx, ite_eq_left hx]
    rfl

end SimpleCircuit

namespace SunSpoke

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) u v} (s : G.SunSpoke) (hn : 3 ≤ n)
  (hu : ∀ z ∈ u, ∃ j, z = Sum.inl j) (hv : ∀ z ∈ v, ∃ j, z = Sum.inl j)
  (a : G.SunRimDart hn)

theorem sun_rim_cut_restoration :
    let C := G.sunRimSimpleCircuit hn hu hv a
    CycleSurgery.splice
      (s.spokeDeletedPairing (fun x => ¬ C.Marked x) (fun x => not_congr (C.marked_twin_iff x)))
      (.hub s.left (0 : Fin 3)) (.hub s.right (0 : Fin 3)) = C.cutPairing := by
  dsimp only
  exact (s.spoke_restored_pairing _ _ (G.sunRimCircuit_spoke_unmarked hn hu hv a s.left)).trans
    (G.sunRimSimpleCircuit hn hu hv a).cutPairing_eq_retainEdges.symm

theorem sun_rim_switch_cut_restoration :
    let C := G.sunRimSimpleCircuit hn hu hv a
    let hM := fun x => not_congr (C.marked_twin_iff x)
    CycleSurgery.splice (s.switchSpokeDeletedPairing (fun x => ¬ C.Marked x) hM)
      (.hub s.left (0 : Fin 3)) (.hub s.right (0 : Fin 3)) =
      RotationEuler.retainEdges s.switch.pairing.perm (fun x => ¬ C.Marked (s.portSwap x))
        (s.switch_mask_invariant (fun x => ¬ C.Marked x) hM) := by
  dsimp only
  exact s.switch_spoke_restored_pairing _ _ (G.sunRimCircuit_spoke_unmarked hn hu hv a s.left)

theorem sun_rim_cut_connected_iff (x y : G.Dart) :
    let C := G.sunRimSimpleCircuit hn hu hv a
    let q := s.spokeDeletedPairing (fun z => ¬ C.Marked z) (fun z => not_congr (C.marked_twin_iff z))
    Connected G.circuitStep C.cutPairing x y ↔ Connected G.circuitStep q x y ∨
      (Connected G.circuitStep q x (G.circuitStep (.hub s.left (0 : Fin 3))) ∧
        Connected G.circuitStep q y (G.circuitStep (.hub s.right (0 : Fin 3)))) ∨
      (Connected G.circuitStep q x (G.circuitStep (.hub s.right (0 : Fin 3))) ∧
        Connected G.circuitStep q y (G.circuitStep (.hub s.left (0 : Fin 3)))) := by
  dsimp only
  rw [(G.sunRimSimpleCircuit hn hu hv a).cutPairing_eq_retainEdges]
  exact s.spoke_restored_connected_iff _ _ (G.sunRimCircuit_spoke_unmarked hn hu hv a s.left) x y

end SunSpoke
end ThomGame.Pictures.PortGraph
