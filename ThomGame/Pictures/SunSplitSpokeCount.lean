module

public import ThomGame.Pictures.SunSplitRimSides
public import ThomGame.Pictures.SunSideSpokes
public import ThomGame.Finite.ThreeWayPartition

/-!
# The actual spoke-edge redistribution formula for a same-rim split

The original spoke side is partitioned into the two new opposite-spoke
sides and the single selected edge. Counts are subtypes of the actual
edge quotients, so each edge is counted once. These are specified Boolean
sides; placing disconnected components and choosing a global outer side
are still separate tasks needed for the full normalization measure.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SunSpoke

open Equiv RibbonConnectivity
open scoped Classical

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) u v} (s : G.SunSpoke) (hn : 3 ≤ n)
  (hu : ∀ z ∈ u, ∃ j, z = Sum.inl j) (hv : ∀ z ∈ v, ∃ j, z = Sum.inl j)

def SplitLeftSpoke (x : G.Dart) : Prop :=
  s.switch.SunSideSpoke hn hu hv (G.sunRimPort hn s.left true)
    (s.switch.hubFlip s.left) (s.portSwap x)

def SplitRightSpoke (x : G.Dart) : Prop :=
  s.switch.SunSideSpoke hn hu hv (G.sunRimPort hn s.right true)
    (s.switch.hubFlip s.right) (s.portSwap x)

theorem splitLeftSpoke_twin_iff (x : G.Dart) :
    s.SplitLeftSpoke hn hu hv (G.pairing.twin x) ↔ s.SplitLeftSpoke hn hu hv x := by
  unfold SplitLeftSpoke
  rw [← s.switch_twin_portSwap]
  exact s.switch.sunSideSpoke_twin_iff hn hu hv _ _ _

theorem splitRightSpoke_twin_iff (x : G.Dart) :
    s.SplitRightSpoke hn hu hv (G.pairing.twin x) ↔ s.SplitRightSpoke hn hu hv x := by
  unfold SplitRightSpoke
  rw [← s.switch_twin_portSwap]
  exact s.switch.sunSideSpoke_twin_iff hn hu hv _ _ _

theorem switch_hasSunSpokeLabel_portSwap (x : G.Dart) :
    s.switch.HasSunSpokeLabel (s.portSwap x) ↔ G.HasSunSpokeLabel x := by
  change (∃ j, Port.label G.jointLabel (s.portSwap x) = Sum.inl j) ↔
    ∃ j, Port.label G.jointLabel x = Sum.inl j
  rw [s.portSwap_label]

theorem not_kept_iff_spoke_edge (x : G.Dart) :
    ¬ s.Kept x ↔ G.pairing.edge x = G.pairing.edge (.hub s.left (0 : Fin 3)) := by
  rw [G.pairing.edge_eq_iff, s.paired]
  simp only [Kept, not_and_or, not_not]

theorem omitted_hasSunSpokeLabel (x : G.Dart) (hx : ¬ s.Kept x) : G.HasSunSpokeLabel x := by
  have he := (s.not_kept_iff_spoke_edge x).mp hx
  rw [G.pairing.edge_eq_iff, s.paired] at he
  rcases he with rfl | rfl
  · exact ⟨G.hubLabel s.left, rfl⟩
  · exact ⟨G.hubLabel s.right, rfl⟩

variable (hEuler : eulerDefect G.pairing.perm G.circuitStep = 0)
  (hf : G.hubFlip s.left = G.hubFlip s.right)

include hEuler hf in
theorem switch_dualEuler : RotationEuler.count s.switch.circuitStep s.switch.pairing.perm =
    2 * Nat.card (Component s.switch.circuitStep s.switch.pairing.perm) :=
  s.switch.dualEuler_eq_twice_components (s.switch.rotationEuler_saturated_iff.mp
    (s.switch_saturated hf (G.rotationEuler_saturated_iff.mpr hEuler)))

include hEuler hf in
theorem splitLeftSpoke_kept {x : G.Dart} (hx : s.SplitLeftSpoke hn hu hv x) : s.Kept x := by
  have hk : s.Kept (s.portSwap x) := s.switchedSpoke.leftRim_opposite_side_kept hn hu hv
    (s.switch_dualEuler hEuler hf) hx.2
  exact (s.portSwap_kept_iff x).mp hk

include hEuler hf in
theorem splitRightSpoke_kept {x : G.Dart} (hx : s.SplitRightSpoke hn hu hv x) : s.Kept x := by
  have hk : s.Kept (s.portSwap x) := s.switchedSpoke.rightRim_opposite_side_kept hn hu hv
    (s.switch_dualEuler hEuler hf) hx.2
  exact (s.portSwap_kept_iff x).mp hk

variable (hc : Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
  (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true))

include hEuler hf hc in
theorem split_spoke_partition (x : G.Dart) :
    G.SunSideSpoke hn hu hv (G.sunRimPort hn s.left true) (!G.hubFlip s.left) x ↔
      s.SplitLeftSpoke hn hu hv x ∨ s.SplitRightSpoke hn hu hv x ∨
        G.pairing.edge x = G.pairing.edge (.hub s.left (0 : Fin 3)) := by
  constructor
  · rintro ⟨hl, hs⟩
    by_cases hk : s.Kept x
    · have hlabel := (s.switch_hasSunSpokeLabel_portSwap x).mpr hl
      rcases (s.split_opposite_sides_union hn hu hv hEuler hf hc ⟨x, hk⟩).mp hs with hx | hx
      · exact Or.inl ⟨hlabel, hx⟩
      · exact Or.inr (Or.inl ⟨hlabel, hx⟩)
    · exact Or.inr (Or.inr ((s.not_kept_iff_spoke_edge x).mp hk))
  · rintro (hx | hx | hx)
    · exact ⟨(s.switch_hasSunSpokeLabel_portSwap x).mp hx.1,
        (s.split_opposite_sides_union hn hu hv hEuler hf hc
          ⟨x, s.splitLeftSpoke_kept hn hu hv hEuler hf hx⟩).mpr (Or.inl hx.2)⟩
    · exact ⟨(s.switch_hasSunSpokeLabel_portSwap x).mp hx.1,
        (s.split_opposite_sides_union hn hu hv hEuler hf hc
          ⟨x, s.splitRightSpoke_kept hn hu hv hEuler hf hx⟩).mpr (Or.inr hx.2)⟩
    · have hk := (s.not_kept_iff_spoke_edge x).mpr hx
      exact ⟨s.omitted_hasSunSpokeLabel x hk, s.leftRim_omitted_onSide hn hu hv x hk⟩

include hEuler hf hc in
theorem split_spokes_disjoint (x : G.Dart) :
    ¬ (s.SplitLeftSpoke hn hu hv x ∧ s.SplitRightSpoke hn hu hv x) := by
  rintro ⟨hl, hr⟩
  exact s.split_opposite_sides_disjoint hn hu hv hEuler hf hc
    ⟨x, s.splitLeftSpoke_kept hn hu hv hEuler hf hl⟩ ⟨hl.2, hr.2⟩

include hEuler hf hc in
theorem split_spoke_edge_partition (c : G.Edge) :
    G.pairing.EdgePred
        (G.SunSideSpoke hn hu hv (G.sunRimPort hn s.left true) (!G.hubFlip s.left)) c ↔
      G.pairing.EdgePred (s.SplitLeftSpoke hn hu hv) c ∨
      G.pairing.EdgePred (s.SplitRightSpoke hn hu hv) c ∨
      c = G.pairing.edge (.hub s.left (0 : Fin 3)) := by
  refine Quotient.inductionOn c fun x => ?_
  change G.pairing.EdgePred
    (G.SunSideSpoke hn hu hv (G.sunRimPort hn s.left true) (!G.hubFlip s.left)) (G.pairing.edge x) ↔
    G.pairing.EdgePred (s.SplitLeftSpoke hn hu hv) (G.pairing.edge x) ∨
    G.pairing.EdgePred (s.SplitRightSpoke hn hu hv) (G.pairing.edge x) ∨
    G.pairing.edge x = G.pairing.edge (.hub s.left (0 : Fin 3))
  rw [G.sunSideSpoke_edge_iff,
    G.pairing.edgePred_edge_iff _ (s.splitLeftSpoke_twin_iff hn hu hv),
    G.pairing.edgePred_edge_iff _ (s.splitRightSpoke_twin_iff hn hu hv)]
  exact s.split_spoke_partition hn hu hv hEuler hf hc x

include hEuler hf hc in
theorem split_spoke_edges_disjoint (c : G.Edge) :
    ¬ (G.pairing.EdgePred (s.SplitLeftSpoke hn hu hv) c ∧
      G.pairing.EdgePred (s.SplitRightSpoke hn hu hv) c) := by
  refine Quotient.inductionOn c fun x => ?_
  change ¬ (G.pairing.EdgePred (s.SplitLeftSpoke hn hu hv) (G.pairing.edge x) ∧
    G.pairing.EdgePred (s.SplitRightSpoke hn hu hv) (G.pairing.edge x))
  rw [G.pairing.edgePred_edge_iff _ (s.splitLeftSpoke_twin_iff hn hu hv),
    G.pairing.edgePred_edge_iff _ (s.splitRightSpoke_twin_iff hn hu hv)]
  exact s.split_spokes_disjoint hn hu hv hEuler hf hc x

include hEuler hf hc in
/-- The same-rim split redistributes actual edges, with the selected spoke
as the only extra edge in the original specified side. -/
theorem split_spoke_count :
    G.sunSideSpokeCount hn hu hv (G.sunRimPort hn s.left true) (!G.hubFlip s.left) =
      s.switch.sunSideSpokeCount hn hu hv (G.sunRimPort hn s.left true) (s.switch.hubFlip s.left) +
      s.switch.sunSideSpokeCount hn hu hv (G.sunRimPort hn s.right true) (s.switch.hubFlip s.right) + 1 := by
  let M := G.pairing.EdgePred
    (G.SunSideSpoke hn hu hv (G.sunRimPort hn s.left true) (!G.hubFlip s.left))
  let L := G.pairing.EdgePred (s.SplitLeftSpoke hn hu hv)
  let R := G.pairing.EdgePred (s.SplitRightSpoke hn hu hv)
  let e := G.pairing.edge (.hub s.left (0 : Fin 3))
  have hL : ¬ L e := by
    intro h
    have hx := (G.pairing.edgePred_edge_iff _ (s.splitLeftSpoke_twin_iff hn hu hv) _).mp h
    exact (s.splitLeftSpoke_kept hn hu hv hEuler hf hx).1 rfl
  have hR : ¬ R e := by
    intro h
    have hx := (G.pairing.edgePred_edge_iff _ (s.splitRightSpoke_twin_iff hn hu hv) _).mp h
    exact (s.splitRightSpoke_kept hn hu hv hEuler hf hx).1 rfl
  have hcount := Finite.card_partition_two_singleton M L R e
    (s.split_spoke_edge_partition hn hu hv hEuler hf hc)
    (s.split_spoke_edges_disjoint hn hu hv hEuler hf hc) hL hR
  have hLc : Nat.card {c : G.Edge // L c} =
      s.switch.sunSideSpokeCount hn hu hv (G.sunRimPort hn s.left true) (s.switch.hubFlip s.left) :=
    G.pairing.edge_subset_card s.switch.pairing s.portSwap s.switch_twin_portSwap
      (s.SplitLeftSpoke hn hu hv)
      (s.switch.SunSideSpoke hn hu hv (G.sunRimPort hn s.left true) (s.switch.hubFlip s.left))
      (fun _ => Iff.rfl)
  have hRc : Nat.card {c : G.Edge // R c} =
      s.switch.sunSideSpokeCount hn hu hv (G.sunRimPort hn s.right true) (s.switch.hubFlip s.right) :=
    G.pairing.edge_subset_card s.switch.pairing s.portSwap s.switch_twin_portSwap
      (s.SplitRightSpoke hn hu hv)
      (s.switch.SunSideSpoke hn hu hv (G.sunRimPort hn s.right true) (s.switch.hubFlip s.right))
      (fun _ => Iff.rfl)
  exact hcount.trans (congrArg₂ (fun l r => l + r + 1) hLc hRc)

include hEuler hf hc in
theorem split_spoke_count_lt :
    s.switch.sunSideSpokeCount hn hu hv (G.sunRimPort hn s.left true) (s.switch.hubFlip s.left) +
      s.switch.sunSideSpokeCount hn hu hv (G.sunRimPort hn s.right true) (s.switch.hubFlip s.right) <
      G.sunSideSpokeCount hn hu hv (G.sunRimPort hn s.left true) (!G.hubFlip s.left) := by
  rw [s.split_spoke_count hn hu hv hEuler hf hc]
  omega

end ThomGame.Pictures.PortGraph.SunSpoke

namespace ThomGame.Pictures.PortGraph.SunMinimalState

open RibbonConnectivity

variable {n : Nat} {b : Fin n → ZMod 2} {w : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) [] w} (h : G.SunMinimalState)
  (s : G.SunSpoke) (hn : 3 ≤ n) (hw : ∀ z ∈ w, ∃ j, z = Sum.inl j)

include h in
theorem split_spoke_count
    (hc : Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn (by simp) hw).perm
      (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true)) :
    G.sunSideSpokeCount hn (by simp) hw (G.sunRimPort hn s.left true) (!G.hubFlip s.left) =
      s.switch.sunSideSpokeCount hn (by simp) hw (G.sunRimPort hn s.left true) (s.switch.hubFlip s.left) +
      s.switch.sunSideSpokeCount hn (by simp) hw (G.sunRimPort hn s.right true) (s.switch.hubFlip s.right) + 1 :=
  s.split_spoke_count hn (by simp) hw h.euler (h.same_flip s) hc

end ThomGame.Pictures.PortGraph.SunMinimalState
