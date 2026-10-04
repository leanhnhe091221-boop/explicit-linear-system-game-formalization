module

public import ThomGame.Pictures.CircuitBoundarySide

/-!
# The boundary-opposite region depends only on the circuit's marked edges

A port is on the side opposite the boundary exactly when it belongs to
the circuit's ambient component and cannot reach any boundary port after
the cut. This description has no choice of orientation or starting port.
Circuits with the same markings therefore have the same interior ports.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open Equiv RibbonConnectivity
open scoped Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
  {G : PortGraph P u v} (C D : G.SimpleCircuit)

def CutInterior (x : G.Dart) : Prop :=
  Connected G.circuitStep G.pairing.perm x C.cutBase ∧
    ∀ y, G.IsBoundary y → ¬ Connected G.circuitStep C.cutPairing x y

theorem cutPairing_eq_of_marked (hm : ∀ x, C.Marked x ↔ D.Marked x) :
    C.cutPairing = D.cutPairing := by
  ext x
  rw [C.cutPairing_eq_retainEdges, D.cutPairing_eq_retainEdges,
    RotationEuler.retainEdges_apply, RotationEuler.retainEdges_apply, hm]

theorem bases_connected_of_marked (hm : ∀ x, C.Marked x ↔ D.Marked x) :
    Connected G.circuitStep G.pairing.perm D.cutBase C.cutBase :=
  (C.reclosed_connected_iff _ _).mp (C.reclosed_marked ((hm D.cutBase).mpr D.cutBase_marked))

theorem cutInterior_iff_of_marked (hm : ∀ x, C.Marked x ↔ D.Marked x) (x : G.Dart) :
    C.CutInterior x ↔ D.CutInterior x := by
  have he := C.bases_connected_of_marked D hm
  unfold CutInterior
  rw [C.cutPairing_eq_of_marked D hm]
  exact and_congr ⟨fun h => h.trans he.symm, fun h => h.trans he⟩ Iff.rfl

variable (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
  2 * Nat.card (Component G.circuitStep G.pairing.perm)) (hsees : G.BoundarySeesComponents)

include hEuler hsees in
theorem on_opposite_boundarySide_iff (h : C.MeetsBoundary) (x : G.Dart) :
    C.OnSide (!C.boundarySide h) x ↔ C.CutInterior x := by
  constructor
  · intro hx
    refine ⟨(C.onSide_union_iff_connected (C.boundarySide h) x).mp (Or.inr hx), ?_⟩
    intro y hy hxy
    exact C.opposite_boundarySide_has_no_boundary hEuler hsees h y hy (hxy.symm.trans hx)
  · rintro ⟨hc, hn⟩
    rcases (C.onSide_union_iff_connected (C.boundarySide h) x).mpr hc with hs | hs
    · obtain ⟨y, hy, hys⟩ := C.boundarySide_spec h
      exact (hn y hy (hs.trans hys.symm)).elim
    · exact hs

include hEuler hsees in
theorem opposite_boundarySide_iff_of_marked (hm : ∀ x, C.Marked x ↔ D.Marked x)
    (hC : C.MeetsBoundary) (hD : D.MeetsBoundary) (x : G.Dart) :
    C.OnSide (!C.boundarySide hC) x ↔ D.OnSide (!D.boundarySide hD) x :=
  (C.on_opposite_boundarySide_iff hEuler hsees hC x).trans
    ((C.cutInterior_iff_of_marked D hm x).trans
      (D.on_opposite_boundarySide_iff hEuler hsees hD x).symm)

end ThomGame.Pictures.PortGraph.SimpleCircuit
