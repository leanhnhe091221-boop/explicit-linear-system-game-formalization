module

public import ThomGame.Pictures.RetainedConnectivity
public import ThomGame.Pictures.SimpleCircuitSectors

/-!
# Deleting edges on one side preserves the opposite side

Side separation in an Euler-saturating graph prevents a path in one
side from using any of the additionally deleted ports in the other.
The result concerns actual dual paths and the same side base port.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open Equiv RibbonConnectivity
open scoped Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
  {G : PortGraph P u v} (C : G.SimpleCircuit)
  (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
    2 * Nat.card (Component G.circuitStep G.pairing.perm))
  (M : G.Dart → Prop) (hM : ∀ z, M (C.cutPairing z) ↔ M z) (side : Bool)
  (hcut : ∀ z, ¬ M z → C.OnSide (!side) z)

include hEuler hcut in
theorem opposite_deletion_connected_iff {x : G.Dart} (hx : C.OnSide side x) (y : G.Dart) :
    Connected G.circuitStep (RotationEuler.retainEdges C.cutPairing M hM) x y ↔
      Connected G.circuitStep C.cutPairing x y := by
  apply RotationEuler.connected_retainEdges_iff_of_component
  intro z hz
  left
  by_contra hm
  have hs : C.OnSide side z := hz.symm.trans hx
  have he := C.onSide_unique hEuler hs (hcut z hm)
  cases side <;> cases he

include hEuler hcut in
theorem opposite_deletion_onSide_iff (x : G.Dart) :
    Connected G.circuitStep (RotationEuler.retainEdges C.cutPairing M hM) x (C.port (0, side)) ↔
      C.OnSide side x := by
  have hc := C.opposite_deletion_connected_iff hEuler M hM side hcut
    (show C.OnSide side (C.port (0, side)) from Connected.refl _) x
  exact ⟨fun h => (hc.mp h.symm).symm, fun h => (hc.mpr h.symm).symm⟩

end ThomGame.Pictures.PortGraph.SimpleCircuit
