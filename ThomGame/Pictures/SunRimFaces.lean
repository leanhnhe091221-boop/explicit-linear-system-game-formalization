module

public import ThomGame.Pictures.SunReducedTermination
public import ThomGame.Pictures.CircuitFaces

/-!
# Terminal sun rims bound actual face orbits

In a graph without joints, absence of inward spokes rules out every
unmarked interior port. The interior is precisely one face orbit of the
original graph, and its actual spoke-edge count is zero. The statement
concerns each rim's ambient component; smoothing circles remain separate.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv RibbonConnectivity

variable {n : Nat} {b : Fin n → ZMod 2} {w : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) [] w} (hn : 3 ≤ n)
  (hw : ∀ z ∈ w, ∃ j, z = Sum.inl j)

theorem sunRimCircuit_marked_hub_iff (a : G.SunRimDart hn) (h : G.Hub)
    (hh : (G.sunRimSimpleCircuit hn (by simp) hw a).OnCircuitVertex (.inr (.inl h)))
    (i : Fin 3) :
    (G.sunRimSimpleCircuit hn (by simp) hw a).Marked (.hub h i) ↔ i ≠ 0 := by
  have hc := (G.sunRimCircuit_onHub_iff_connected hn (by simp) hw a h).mp hh
  have ht := (G.sunRimCircuit_marked_iff_connected hn (by simp) hw a
    (G.sunRimPort hn h true)).mpr hc
  have he := Connected.circuit (p := (G.sunRimPairing hn).perm)
    (f := (G.sunRimVertexPairing hn (by simp) hw).perm) (G.sunRimPort hn h true)
  change Connected _ _ _ ((G.sunRimVertexPairing hn (by simp) hw).twin _) at he
  rw [G.sunRimVertexPairing_port] at he
  have hf := (G.sunRimCircuit_marked_iff_connected hn (by simp) hw a
    (G.sunRimPort hn h false)).mpr (hc.trans he)
  fin_cases i
  · exact iff_of_false (G.sunRimCircuit_spoke_unmarked hn (by simp) hw a h) (by simp)
  · exact iff_of_true hf (by decide +kernel)
  · exact iff_of_true ht (by decide +kernel)

variable [IsEmpty G.Joint]

theorem noInteriorSunSpoke_closed_interior (hNo : G.NoInteriorSunSpoke hn hw)
    (a : G.SunRimDart hn) (x : G.Dart)
    (hv : (G.sunRimSimpleCircuit hn (by simp) hw a).OnCircuitVertex x.vertex)
    (hx : (G.sunRimSimpleCircuit hn (by simp) hw a).CutInterior x) :
    (G.sunRimSimpleCircuit hn (by simp) hw a).Marked x := by
  cases x with
  | top i => exact i.elim0
  | bottom i => exact (hx.2 (.bottom i) trivial (Connected.refl _)).elim
  | joint j side => exact isEmptyElim j
  | hub h i =>
    apply (G.sunRimCircuit_marked_hub_iff hn hw a h hv i).mpr
    intro hi
    subst i
    exact G.noInteriorSunSpoke_rim_hub hn hw hNo a h hv hx

variable (hEuler : eulerDefect G.pairing.perm G.circuitStep = 0)
  (hsees : G.BoundarySeesComponents)

include hEuler hsees in
theorem noInteriorSunSpoke_interior_marked (hNo : G.NoInteriorSunSpoke hn hw)
    (a : G.SunRimDart hn) (hb : (G.sunRimSimpleCircuit hn (by simp) hw a).MeetsBoundary)
    {x : G.Dart} (hx : (G.sunRimSimpleCircuit hn (by simp) hw a).CutInterior x) :
    (G.sunRimSimpleCircuit hn (by simp) hw a).Marked x :=
  (G.sunRimSimpleCircuit hn (by simp) hw a).marked_of_closed_interior
    (G.dualEuler_eq_twice_components hEuler) hsees hb
    (G.noInteriorSunSpoke_closed_interior hn hw hNo a) hx

include hEuler hsees in
theorem noInteriorSunSpoke_interior_iff_face (hNo : G.NoInteriorSunSpoke hn hw)
    (a : G.SunRimDart hn) (hb : (G.sunRimSimpleCircuit hn (by simp) hw a).MeetsBoundary)
    (x : G.Dart) :
    (G.sunRimSimpleCircuit hn (by simp) hw a).CutInterior x ↔
      G.circuitStep.SameCycle x ((G.sunRimSimpleCircuit hn (by simp) hw a).port
        (0, !(G.sunRimSimpleCircuit hn (by simp) hw a).boundarySide hb)) :=
  (G.sunRimSimpleCircuit hn (by simp) hw a).cutInterior_iff_face_of_closed
    (G.dualEuler_eq_twice_components hEuler) hsees hb
    (G.noInteriorSunSpoke_closed_interior hn hw hNo a) x

include hEuler hsees in
theorem noInteriorSunSpoke_interior_spoke_count (hNo : G.NoInteriorSunSpoke hn hw)
    (a : G.SunRimDart hn) (hb : (G.sunRimSimpleCircuit hn (by simp) hw a).MeetsBoundary) :
    G.sunInteriorSpokeCount hn (by simp) hw a hb = 0 := by
  let C := G.sunRimSimpleCircuit hn (by simp) hw a
  have hEmpty : IsEmpty (G.SunSideSpokeEdge hn (by simp) hw a (!C.boundarySide hb)) := by
    refine ⟨?_⟩
    rintro ⟨e, x, _, hs, hi⟩
    have hx := (C.on_opposite_boundarySide_iff (G.dualEuler_eq_twice_components hEuler)
      hsees hb x).mp hi
    exact G.sunRimCircuit_spokeLabel_unmarked hn (by simp) hw a hs
      (G.noInteriorSunSpoke_interior_marked hn hw hEuler hsees hNo a hb hx)
  exact Nat.card_eq_zero.mpr (Or.inl hEmpty)

include hEuler hsees in
theorem noInteriorSunSpoke_total_interior_count (hNo : G.NoInteriorSunSpoke hn hw)
    (hb : ∀ a : G.SunRimDart hn, (G.sunRimSimpleCircuit hn (by simp) hw a).MeetsBoundary) :
    G.sunTotalInteriorSpokeCount hn (by simp) hw hEuler hsees hb = 0 :=
  (G.sunTotalInteriorSpokeCount_eq_zero_iff hn (by simp) hw hEuler hsees hb).mpr
    (fun a => G.noInteriorSunSpoke_interior_spoke_count hn hw hEuler hsees hNo a (hb a))

include hEuler hsees in
theorem noInteriorSunSpoke_boundsFaceOrbit (hNo : G.NoInteriorSunSpoke hn hw)
    (a : G.SunRimDart hn) (hb : (G.sunRimSimpleCircuit hn (by simp) hw a).MeetsBoundary) :
    (G.sunRimSimpleCircuit hn (by simp) hw a).BoundsFaceOrbit
      (!(G.sunRimSimpleCircuit hn (by simp) hw a).boundarySide hb) :=
  (G.sunRimSimpleCircuit hn (by simp) hw a).boundsFaceOrbit_of_closed_interior
    (G.dualEuler_eq_twice_components hEuler) hsees hb
    (G.noInteriorSunSpoke_closed_interior hn hw hNo a)

/-- Every unoriented rim has a side that is exactly an original face orbit. -/
def SunRimsBoundFaceOrbits (G : PortGraph (sunPresentation n b) [] w) : Prop :=
  ∀ a : G.SunRimDart hn, ∃ side, (G.sunRimSimpleCircuit hn (by simp) hw a).BoundsFaceOrbit side

include hEuler hsees in
theorem noInteriorSunSpoke_rims_bound_faces (hNo : G.NoInteriorSunSpoke hn hw)
    (hb : G.HubsReachBoundary) : G.SunRimsBoundFaceOrbits hn hw := by
  intro a
  have hbound := (G.sunRimSimpleCircuit hn (by simp) hw a).meetsBoundary_of_hubsReachBoundary hb
  exact ⟨_, G.noInteriorSunSpoke_boundsFaceOrbit hn hw hEuler hsees hNo a hbound⟩

end ThomGame.Pictures.PortGraph
