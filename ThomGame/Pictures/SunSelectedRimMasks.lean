module

public import ThomGame.Pictures.SunRimMembership
public import ThomGame.Pictures.ComponentUnionSwitch

/-!
# The selected rims have exactly the same union of marked ports

The actual edge attachment swap may split one rim into two or join two
rims into one. The union of the components through the two selected rim
ports is unchanged as a set of raw ports. Consequently the transported
cut mask is precisely the union of the new selected rim markings.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SunSpoke

open Equiv RibbonConnectivity
open scoped Classical

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) u v} (s : G.SunSpoke) (hn : 3 ≤ n)
  (hu : ∀ z ∈ u, ∃ j, z = Sum.inl j) (hv : ∀ z ∈ v, ∃ j, z = Sum.inl j)

theorem switch_selected_rim_union (x : G.SunRimDart hn) :
    (Connected (s.switch.sunRimPairing hn).perm (s.switch.sunRimVertexPairing hn hu hv).perm
        (G.sunRimPort hn s.left true) x ∨
      Connected (s.switch.sunRimPairing hn).perm (s.switch.sunRimVertexPairing hn hu hv).perm
        (G.sunRimPort hn s.right true) x) ↔
    (Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
        (G.sunRimPort hn s.left true) x ∨
      Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
        (G.sunRimPort hn s.right true) x) := by
  have hq : (s.switch.sunRimVertexPairing hn hu hv).perm = (G.sunRimVertexPairing hn hu hv).perm := by
    ext z
    exact s.switch_rimVertexPairing hn hu hv z
  rw [hq]
  exact rootUnion_conjugate_iff (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
    (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true)
    (s.switch.sunRimPairing hn).perm (s.switch_rimPairing hn) x

def SelectedRimMarked (x : G.Dart) : Prop :=
  (G.sunRimSimpleCircuit hn hu hv (G.sunRimPort hn s.left true)).Marked x ∨
    (G.sunRimSimpleCircuit hn hu hv (G.sunRimPort hn s.right true)).Marked x

def SwitchSelectedRimMarked (x : G.Dart) : Prop :=
  (s.switch.sunRimSimpleCircuit hn hu hv (G.sunRimPort hn s.left true)).Marked x ∨
    (s.switch.sunRimSimpleCircuit hn hu hv (G.sunRimPort hn s.right true)).Marked x

theorem switch_selected_marked_iff (x : G.Dart) :
    s.SwitchSelectedRimMarked hn hu hv x ↔ s.SelectedRimMarked hn hu hv x := by
  by_cases hx : Port.label G.jointLabel x ∈ Set.range (Hypergraph.sunCycle n hn).edge
  · let z : G.SunRimDart hn := ⟨x, hx⟩
    exact (or_congr
      (s.switch.sunRimCircuit_marked_iff_connected hn hu hv (G.sunRimPort hn s.left true) z)
      (s.switch.sunRimCircuit_marked_iff_connected hn hu hv (G.sunRimPort hn s.right true) z)).trans
      ((s.switch_selected_rim_union hn hu hv z).trans (or_congr
        (G.sunRimCircuit_marked_iff_connected hn hu hv (G.sunRimPort hn s.left true) z).symm
        (G.sunRimCircuit_marked_iff_connected hn hu hv (G.sunRimPort hn s.right true) z).symm))
  · constructor
    · rintro (h | h)
      · exact (hx (s.switch.sunRimCircuit_marked_rim hn hu hv _ h)).elim
      · exact (hx (s.switch.sunRimCircuit_marked_rim hn hu hv _ h)).elim
    · rintro (h | h)
      · exact (hx (G.sunRimCircuit_marked_rim hn hu hv _ h)).elim
      · exact (hx (G.sunRimCircuit_marked_rim hn hu hv _ h)).elim

theorem selected_marked_portSwap_iff (x : G.Dart) :
    s.SelectedRimMarked hn hu hv (s.portSwap x) ↔ s.SelectedRimMarked hn hu hv x := by
  have hl : s.SelectedRimMarked hn hu hv (.hub s.left (2 : Fin 3)) :=
    Or.inl ⟨(0, false), rfl⟩
  have hr : s.SelectedRimMarked hn hu hv (.hub s.right (2 : Fin 3)) :=
    Or.inr ⟨(0, false), rfl⟩
  change s.SelectedRimMarked hn hu hv (swap _ _ x) ↔ _
  exact Iff.of_eq (Pairing.label_swap (propext (iff_of_true hl hr)) x)

theorem switch_selected_marked_transport (x : G.Dart) :
    s.SwitchSelectedRimMarked hn hu hv x ↔ s.SelectedRimMarked hn hu hv (s.portSwap x) :=
  (s.switch_selected_marked_iff hn hu hv x).trans (s.selected_marked_portSwap_iff hn hu hv x).symm

/-- In the same-rim case the old single marking is the union of the two
new selected markings. Separation itself is supplied by Euler saturation
and equal hub orientations in `SunRimComponents`. -/
theorem switch_selected_marked_of_same_rim
    (hc : Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
      (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true)) (x : G.Dart) :
    s.SwitchSelectedRimMarked hn hu hv x ↔
      (G.sunRimSimpleCircuit hn hu hv (G.sunRimPort hn s.left true)).Marked x := by
  apply (s.switch_selected_marked_iff hn hu hv x).trans
  have he := G.sunRimCircuit_marked_iff_of_connected hn hu hv
    (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true) hc x
  constructor
  · rintro (h | h)
    · exact h
    · exact he.mpr h
  · exact Or.inl

/-- Joining distinct rims replaces their old marking union by one new
actual rim marking. -/
theorem switch_selected_marked_of_join
    (hc : ¬ Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
      (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true)) (x : G.Dart) :
    s.SelectedRimMarked hn hu hv x ↔
      (s.switch.sunRimSimpleCircuit hn hu hv (G.sunRimPort hn s.left true)).Marked x := by
  apply (s.switch_selected_marked_iff hn hu hv x).symm.trans
  have he := s.switch.sunRimCircuit_marked_iff_of_connected hn hu hv
    (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true) (s.switch_rim_joins hn hu hv hc) x
  constructor
  · rintro (h | h)
    · exact h
    · exact he.mpr h
  · exact Or.inl

end ThomGame.Pictures.PortGraph.SunSpoke
