module

public import ThomGame.Pictures.CircuitInterior
public import ThomGame.Pictures.ClosedComponents

/-!
# A cut side without a frontier is one actual face orbit

If every port at a circuit vertex on the selected cut side is marked,
the whole side consists of marked ports. Its cut pairing is therefore
fixed, and cut connectivity is exactly one orbit of the original face
permutation. These are statements about the actual port graph; they do
not prescribe the placement of other graph components or recorded circles.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open Equiv RibbonConnectivity

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
  {G : PortGraph P u v} (C : G.SimpleCircuit)

theorem onSide_iff_of_cut_connected {x y : G.Dart}
    (h : Connected G.circuitStep C.cutPairing x y) (side : Bool) :
    C.OnSide side x ↔ C.OnSide side y :=
  ⟨fun hx => h.symm.trans hx, fun hy => h.trans hy⟩

theorem cutInterior_iff_of_cut_connected {x y : G.Dart}
    (h : Connected G.circuitStep C.cutPairing x y) : C.CutInterior x ↔ C.CutInterior y := by
  constructor
  · rintro ⟨hx, hn⟩
    exact ⟨(C.cut_connected_old h).symm.trans hx, fun z hz hyz => hn z hz (h.trans hyz)⟩
  · rintro ⟨hy, hn⟩
    exact ⟨(C.cut_connected_old h).trans hy, fun z hz hxz => hn z hz (h.symm.trans hxz)⟩

/-- No frontier at the rim implies no unmarked port anywhere on that cut side. -/
theorem marked_of_closed_side (side : Bool)
    (hclosed : ∀ x, C.OnCircuitVertex x.vertex → C.OnSide side x → C.Marked x)
    {x : G.Dart} (hx : C.OnSide side x) : C.Marked x := by
  let M := fun z => C.OnSide side z ∧ C.Marked z
  have hp (z : G.Dart) (hz : M z) : M (G.circuitStep z) := by
    have hs := (C.onSide_iff_of_cut_connected (Connected.edge z) side).mp hz.1
    refine ⟨hs, hclosed _ ?_ hs⟩
    rw [G.vertex_circuitStep]
    exact C.marked_onCircuitVertex ((C.marked_twin_iff z).mpr hz.2)
  have hf (z : G.Dart) (hz : M z) : M (C.cutPairing z) := by
    rw [C.cutPairing_of_marked hz.2]
    exact hz
  exact (hx.symm.predicate_of_forward M hp hf ⟨Connected.refl _, ⟨(0, side), rfl⟩⟩).2

theorem onSide_iff_face_of_closed (side : Bool)
    (hclosed : ∀ x, C.OnCircuitVertex x.vertex → C.OnSide side x → C.Marked x)
    (x : G.Dart) : C.OnSide side x ↔ G.circuitStep.SameCycle x (C.port (0, side)) := by
  constructor
  · intro hx
    apply hx.sameCycle_of_fixed_on_component
    intro z hz
    exact C.cutPairing_of_marked (C.marked_of_closed_side side hclosed (hz.symm.trans hx))
  · intro hx
    exact (RotationEuler.connected_swap_iff _ _ _ _).mp
      (sameCycle_connected C.cutPairing G.circuitStep hx)

variable (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
  2 * Nat.card (Component G.circuitStep G.pairing.perm)) (hsees : G.BoundarySeesComponents)

include hEuler in
theorem onSide_iff_port_of_closed (side : Bool)
    (hclosed : ∀ x, C.OnCircuitVertex x.vertex → C.OnSide side x → C.Marked x)
    (x : G.Dart) : C.OnSide side x ↔ ∃ i, C.port (i, side) = x := by
  constructor
  · intro hx
    obtain ⟨⟨i, t⟩, rfl⟩ := C.marked_of_closed_side side hclosed hx
    have ht := (C.cut_marked_connected_iff hEuler (i, t) (0, side)).mp hx
    change t = side at ht
    subst t
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact C.cut_marked_connected_of_side (i, side) (0, side) rfl

/-- This side of the circuit is exactly one original face orbit,
with one selected port for each circuit edge. -/
def BoundsFaceOrbit (side : Bool) : Prop :=
  ∀ x, G.circuitStep.SameCycle x (C.port (0, side)) ↔ ∃ i, C.port (i, side) = x

include hEuler in
theorem boundsFaceOrbit_of_closed (side : Bool)
    (hclosed : ∀ x, C.OnCircuitVertex x.vertex → C.OnSide side x → C.Marked x) :
    C.BoundsFaceOrbit side := fun x =>
  (C.onSide_iff_face_of_closed side hclosed x).symm.trans
    (C.onSide_iff_port_of_closed hEuler side hclosed x)

noncomputable def faceOrbitEquiv (side : Bool) (hface : C.BoundsFaceOrbit side) :
    Fin C.length ≃ {x : G.Dart // G.circuitStep.SameCycle x (C.port (0, side))} :=
  Equiv.ofBijective (fun i => ⟨C.port (i, side), (hface _).mpr ⟨i, rfl⟩⟩)
    ⟨fun _ _ he => (Prod.mk.inj (C.port_injective (congrArg Subtype.val he))).1, by
      rintro ⟨x, hx⟩
      obtain ⟨i, hi⟩ := (hface x).mp hx
      exact ⟨i, Subtype.ext hi⟩⟩

theorem faceOrbit_card (side : Bool) (hface : C.BoundsFaceOrbit side) :
    Nat.card {x : G.Dart // G.circuitStep.SameCycle x (C.port (0, side))} = C.length := by
  rw [← Nat.card_congr (C.faceOrbitEquiv side hface), Nat.card_fin]

include hEuler hsees in
theorem marked_of_closed_interior (hb : C.MeetsBoundary)
    (hclosed : ∀ x, C.OnCircuitVertex x.vertex → C.CutInterior x → C.Marked x)
    {x : G.Dart} (hx : C.CutInterior x) : C.Marked x := by
  have he := C.on_opposite_boundarySide_iff hEuler hsees hb
  exact C.marked_of_closed_side (!C.boundarySide hb)
    (fun z hz hs => hclosed z hz ((he z).mp hs)) ((he x).mpr hx)

include hEuler hsees in
theorem cutInterior_iff_face_of_closed (hb : C.MeetsBoundary)
    (hclosed : ∀ x, C.OnCircuitVertex x.vertex → C.CutInterior x → C.Marked x)
    (x : G.Dart) : C.CutInterior x ↔
      G.circuitStep.SameCycle x (C.port (0, !C.boundarySide hb)) := by
  have he := C.on_opposite_boundarySide_iff hEuler hsees hb
  exact (he x).symm.trans (C.onSide_iff_face_of_closed (!C.boundarySide hb)
    (fun z hz hs => hclosed z hz ((he z).mp hs)) x)

include hEuler hsees in
theorem boundsFaceOrbit_of_closed_interior (hb : C.MeetsBoundary)
    (hclosed : ∀ x, C.OnCircuitVertex x.vertex → C.CutInterior x → C.Marked x) :
    C.BoundsFaceOrbit (!C.boundarySide hb) :=
  C.boundsFaceOrbit_of_closed hEuler (!C.boundarySide hb)
    (fun z hz hs => hclosed z hz ((C.on_opposite_boundarySide_iff hEuler hsees hb z).mp hs))

end ThomGame.Pictures.PortGraph.SimpleCircuit
