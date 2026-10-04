module

public import ThomGame.Pictures.SunComponentSpokes
public import ThomGame.Pictures.GraphBoundaryComponents

/-!
# A boundary-visible circuit component determines one boundary side

Boundary ports in the same graph component lie on one face when the
actual graph satisfies `BoundarySeesComponents`. They remain connected
after a circuit cut, so Euler separation makes their cut side unique.
The chosen side is only defined for a component with a boundary witness.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open Equiv RibbonConnectivity
open scoped Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
  {G : PortGraph P u v} (C : G.SimpleCircuit)

def MeetsBoundary : Prop :=
  ∃ x, G.IsBoundary x ∧ Connected G.circuitStep G.pairing.perm x C.cutBase

def HasBoundarySide (side : Bool) : Prop := ∃ x, G.IsBoundary x ∧ C.OnSide side x

theorem hasBoundarySide_iff_meetsBoundary : (∃ side, C.HasBoundarySide side) ↔ C.MeetsBoundary := by
  constructor
  · rintro ⟨side, x, hb, hs⟩
    exact ⟨x, hb, (C.onSide_union_iff_connected side x).mp (Or.inl hs)⟩
  · rintro ⟨x, hb, hc⟩
    rcases (C.onSide_union_iff_connected false x).mpr hc with hs | hs
    · exact ⟨false, x, hb, hs⟩
    · exact ⟨true, x, hb, hs⟩

theorem cut_connected_boundary (hsees : G.BoundarySeesComponents)
    {x y : G.Dart} (hx : G.IsBoundary x) (hy : G.IsBoundary y)
    (hc : Connected G.circuitStep G.pairing.perm x y) :
    Connected G.circuitStep C.cutPairing x y := by
  have hface := (hsees ⟨x, hx⟩ ⟨y, hy⟩).mp
    ((RotationEuler.connected_swap_iff _ _ x y).mp hc)
  exact (RotationEuler.connected_swap_iff _ _ x y).mp
    (sameCycle_connected C.cutPairing G.circuitStep hface)

variable (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
  2 * Nat.card (Component G.circuitStep G.pairing.perm))
  (hsees : G.BoundarySeesComponents)

include hEuler hsees in
theorem hasBoundarySide_unique {side other : Bool}
    (hs : C.HasBoundarySide side) (ht : C.HasBoundarySide other) : side = other := by
  obtain ⟨x, hx, hxs⟩ := hs
  obtain ⟨y, hy, hyt⟩ := ht
  have hxc := (C.onSide_union_iff_connected side x).mp (Or.inl hxs)
  have hyc := (C.onSide_union_iff_connected other y).mp (Or.inl hyt)
  have hxy := C.cut_connected_boundary hsees hx hy (hxc.trans hyc.symm)
  exact C.onSide_unique hEuler hxs (hxy.trans hyt)

noncomputable def boundarySide (h : C.MeetsBoundary) : Bool :=
  Classical.choose (C.hasBoundarySide_iff_meetsBoundary.mpr h)

theorem boundarySide_spec (h : C.MeetsBoundary) : C.HasBoundarySide (C.boundarySide h) :=
  Classical.choose_spec (C.hasBoundarySide_iff_meetsBoundary.mpr h)

include hEuler hsees in
theorem boundarySide_eq_of_witness (h : C.MeetsBoundary) {side : Bool}
    (hs : C.HasBoundarySide side) : C.boundarySide h = side :=
  C.hasBoundarySide_unique hEuler hsees (C.boundarySide_spec h) hs

include hEuler hsees in
theorem on_boundarySide_iff_component (h : C.MeetsBoundary) (x : G.Dart) (hx : G.IsBoundary x) :
    C.OnSide (C.boundarySide h) x ↔ Connected G.circuitStep G.pairing.perm x C.cutBase := by
  constructor
  · intro hs
    exact (C.onSide_union_iff_connected (C.boundarySide h) x).mp (Or.inl hs)
  · intro hc
    obtain ⟨side, hs⟩ : ∃ side, C.OnSide side x := by
      rcases (C.onSide_union_iff_connected false x).mpr hc with hs | hs
      · exact ⟨false, hs⟩
      · exact ⟨true, hs⟩
    have he := C.boundarySide_eq_of_witness hEuler hsees h ⟨x, hx, hs⟩
    exact he.symm ▸ hs

include hEuler hsees in
theorem opposite_boundarySide_has_no_boundary (h : C.MeetsBoundary)
    (x : G.Dart) (hx : G.IsBoundary x) : ¬ C.OnSide (!C.boundarySide h) x := by
  intro hs
  have he := C.boundarySide_eq_of_witness hEuler hsees h ⟨x, hx, hs⟩
  cases hb : C.boundarySide h <;> simp only [hb] at he <;> cases he

end ThomGame.Pictures.PortGraph.SimpleCircuit
