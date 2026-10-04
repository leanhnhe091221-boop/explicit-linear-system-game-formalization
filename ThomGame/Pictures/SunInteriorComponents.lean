module

public import ThomGame.Pictures.CircuitInterior
public import ThomGame.Pictures.SunInteriorSpokeCount
public import ThomGame.Pictures.SunBoundaryAccessibility

/-!
# Interior spoke counts on actual unoriented rim components

Changing the starting dart or orientation of a rim preserves its marked
edges and hence its boundary-opposite spoke subset. The count therefore
descends to the actual rim component quotient. Summing this function
counts each rim once, with no choice of rooted traversal. Each summand
still concerns only the rim's own ambient graph component.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv RibbonConnectivity
open scoped Classical BigOperators

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  (G : PortGraph (sunPresentation n b) u v) (hn : 3 ≤ n)
  (hu : ∀ z ∈ u, ∃ j, z = Sum.inl j) (hv : ∀ z ∈ v, ∃ j, z = Sum.inl j)
  (hEuler : eulerDefect G.pairing.perm G.circuitStep = 0) (hsees : G.BoundarySeesComponents)

include hEuler hsees in
theorem sunInteriorSpokeCount_eq_of_connected (a z : G.SunRimDart hn)
    (haz : Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm a z)
    (ha : (G.sunRimSimpleCircuit hn hu hv a).MeetsBoundary)
    (hz : (G.sunRimSimpleCircuit hn hu hv z).MeetsBoundary) :
    G.sunInteriorSpokeCount hn hu hv a ha = G.sunInteriorSpokeCount hn hu hv z hz := by
  have hs := (G.sunRimSimpleCircuit hn hu hv a).opposite_boundarySide_iff_of_marked
    (G.sunRimSimpleCircuit hn hu hv z) (G.dualEuler_eq_twice_components hEuler) hsees
    (G.sunRimCircuit_marked_iff_of_connected hn hu hv a z haz) ha hz
  exact G.pairing.edge_subset_card G.pairing (Equiv.refl _) (fun _ => rfl)
    (G.SunSideSpoke hn hu hv a (!(G.sunRimSimpleCircuit hn hu hv a).boundarySide ha))
    (G.SunSideSpoke hn hu hv z (!(G.sunRimSimpleCircuit hn hu hv z).boundarySide hz))
    (fun x => and_congr Iff.rfl (hs x))

noncomputable instance sunRimComponentFintype : Fintype (G.SunRimComponent hn hu hv) := by
  unfold SunRimComponent
  exact Fintype.ofFinite _

variable (hb : ∀ a : G.SunRimDart hn, (G.sunRimSimpleCircuit hn hu hv a).MeetsBoundary)

noncomputable def sunRimInteriorCount : G.SunRimComponent hn hu hv → Nat :=
  Quotient.lift (fun a => G.sunInteriorSpokeCount hn hu hv a (hb a))
    (fun a z haz => G.sunInteriorSpokeCount_eq_of_connected hn hu hv hEuler hsees a z haz (hb a) (hb z))

theorem sunRimInteriorCount_component (a : G.SunRimDart hn) :
    G.sunRimInteriorCount hn hu hv hEuler hsees hb
      (component (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm a) =
      G.sunInteriorSpokeCount hn hu hv a (hb a) := rfl

noncomputable def sunTotalInteriorSpokeCount : Nat :=
  ∑ c : G.SunRimComponent hn hu hv, G.sunRimInteriorCount hn hu hv hEuler hsees hb c

theorem sunTotalInteriorSpokeCount_eq_zero_iff :
    G.sunTotalInteriorSpokeCount hn hu hv hEuler hsees hb = 0 ↔
      ∀ a : G.SunRimDart hn, G.sunInteriorSpokeCount hn hu hv a (hb a) = 0 := by
  unfold sunTotalInteriorSpokeCount
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h a
    exact h (component (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm a)
      (Finset.mem_univ _)
  · intro h c _
    exact Quotient.inductionOn c h

end ThomGame.Pictures.PortGraph
