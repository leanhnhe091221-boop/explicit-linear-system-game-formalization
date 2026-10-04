module

public import ThomGame.Pictures.SunInteriorComponents
public import ThomGame.Pictures.UnselectedComponents
public import ThomGame.Finite.TwoPointSum

/-!
# The total contribution of unselected rims is preserved

The actual switch induces a bijection of all rim components except the
one or two selected components. Corresponding components have the same
interior spoke count. Their finite sums are consequently equal; no
assumption about the number of other rims is required.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SunSpoke

open Equiv RibbonConnectivity
open scoped Classical BigOperators

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) u v} (s : G.SunSpoke) (hn : 3 ≤ n)
  (hu : ∀ z ∈ u, ∃ j, z = Sum.inl j) (hv : ∀ z ∈ v, ∃ j, z = Sum.inl j)

abbrev UnselectedRimComponent :=
  {c : G.SunRimComponent hn hu hv //
    c ≠ component (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
      (G.sunRimPort hn s.left true) ∧
    c ≠ component (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
      (G.sunRimPort hn s.right true)}

theorem switch_rim_away_iff (x : G.SunRimDart hn) :
    (¬ Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
        x (G.sunRimPort hn s.left true) ∧
      ¬ Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
        x (G.sunRimPort hn s.right true)) ↔
    (¬ Connected (s.switch.sunRimPairing hn).perm (s.switch.sunRimVertexPairing hn hu hv).perm
        x (G.sunRimPort hn s.left true) ∧
      ¬ Connected (s.switch.sunRimPairing hn).perm (s.switch.sunRimVertexPairing hn hu hv).perm
        x (G.sunRimPort hn s.right true)) :=
  away_iff_of_rootUnion _ _ _ _ _ _ (fun z => (s.switch_selected_rim_union hn hu hv z).symm) x

noncomputable def unselectedRimEquiv :
    s.UnselectedRimComponent hn hu hv ≃ s.switchedSpoke.UnselectedRimComponent hn hu hv :=
  unselectedComponentEquiv _ _ _ _ _ _ (s.switch_rim_away_iff hn hu hv)
    (fun _ ha hb y => s.switch_rim_connected_away hn hu hv ha hb y)

theorem unselectedRimEquiv_out (c : s.UnselectedRimComponent hn hu hv) :
    (s.unselectedRimEquiv hn hu hv c).val =
      component (s.switch.sunRimPairing hn).perm (s.switch.sunRimVertexPairing hn hu hv).perm c.val.out := rfl

variable (hEuler : eulerDefect G.pairing.perm G.circuitStep = 0)
  (hf : G.hubFlip s.left = G.hubFlip s.right) (hsees : G.BoundarySeesComponents)
  (hNewEuler : eulerDefect s.switch.pairing.perm s.switch.circuitStep = 0)
  (hNewSees : s.switch.BoundarySeesComponents)
  (hb : ∀ a : G.SunRimDart hn, (G.sunRimSimpleCircuit hn hu hv a).MeetsBoundary)
  (hbNew : ∀ a : s.switch.SunRimDart hn, (s.switch.sunRimSimpleCircuit hn hu hv a).MeetsBoundary)

include hf in
theorem unselected_rim_interior_count (c : s.UnselectedRimComponent hn hu hv) :
    G.sunRimInteriorCount hn hu hv hEuler hsees hb c.val =
      s.switch.sunRimInteriorCount hn hu hv hNewEuler hNewSees hbNew
        (s.unselectedRimEquiv hn hu hv c).val := by
  have haway := unselected_out (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
    (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true) c
  have ho := congrArg (G.sunRimInteriorCount hn hu hv hEuler hsees hb) (Quotient.out_eq c.val)
  change G.sunInteriorSpokeCount hn hu hv c.val.out (hb c.val.out) =
    G.sunRimInteriorCount hn hu hv hEuler hsees hb c.val at ho
  rw [s.unselectedRimEquiv_out]
  exact ho.symm.trans (s.switch_interior_spoke_count_away hn hu hv hEuler hf hsees
    c.val.out haway.1 haway.2 (hb c.val.out) (hbNew c.val.out)).symm

include hf in
theorem unselected_rim_interior_sum :
    (∑ c : s.UnselectedRimComponent hn hu hv,
      G.sunRimInteriorCount hn hu hv hEuler hsees hb c.val) =
    ∑ c : s.switchedSpoke.UnselectedRimComponent hn hu hv,
      s.switch.sunRimInteriorCount hn hu hv hNewEuler hNewSees hbNew c.val :=
  Fintype.sum_equiv (s.unselectedRimEquiv hn hu hv) _ _
    (s.unselected_rim_interior_count hn hu hv hEuler hf hsees hNewEuler hNewSees hb hbNew)

end ThomGame.Pictures.PortGraph.SunSpoke
