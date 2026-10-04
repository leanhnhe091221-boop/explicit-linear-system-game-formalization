module

public import ThomGame.Pictures.CircuitSideDeletion
public import ThomGame.Pictures.SunRimRegionMasks

/-!
# The two sides of the selected left rim after deleting its spoke

The spoke lies on side `!hubFlip left` of the rim based at its second
rim port. Deleting it preserves the opposite side exactly. Its original
side is the union of the components reaching the two deleted endpoints.
Their separation, and the choice of a global outer region, are distinct
questions not assumed by this union formula.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SunSpoke

open Equiv RibbonConnectivity
open scoped Classical

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) u v} (s : G.SunSpoke) (hn : 3 ≤ n)
  (hu : ∀ z ∈ u, ∃ j, z = Sum.inl j) (hv : ∀ z ∈ v, ∃ j, z = Sum.inl j)

noncomputable def leftRim : G.SimpleCircuit :=
  G.sunRimSimpleCircuit hn hu hv (G.sunRimPort hn s.left true)

noncomputable def leftRimDeletedPairing : Perm G.Dart :=
  s.spokeDeletedPairing (fun x => ¬ (s.leftRim hn hu hv).Marked x)
    (fun x => not_congr ((s.leftRim hn hu hv).marked_twin_iff x))

theorem leftRim_cut_kept_iff (x : G.Dart) :
    s.Kept ((s.leftRim hn hu hv).cutPairing x) ↔ s.Kept x := by
  rw [(s.leftRim hn hu hv).cutPairing_eq_retainEdges]
  exact RotationEuler.retainEdges_preserves G.pairing.perm
    (fun z => ¬ (s.leftRim hn hu hv).Marked z)
    (fun z => not_congr ((s.leftRim hn hu hv).marked_twin_iff z)) s.Kept s.twin_kept_iff x

theorem leftRimDeletedPairing_eq : s.leftRimDeletedPairing hn hu hv =
    RotationEuler.retainEdges (s.leftRim hn hu hv).cutPairing s.Kept
      (s.leftRim_cut_kept_iff hn hu hv) := by
  ext x
  change s.spokeDeletedPairing _ _ x = _
  rw [s.spokeDeletedPairing_apply, RotationEuler.retainEdges_apply,
    (s.leftRim hn hu hv).cutPairing_eq_retainEdges, RotationEuler.retainEdges_apply]
  by_cases hk : s.Kept x <;> by_cases hm : (s.leftRim hn hu hv).Marked x <;>
    simp only [hk, hm, not_true_eq_false, not_false_eq_true, and_true,
      and_false, ite_true, ite_false]
  rfl

theorem leftRim_spoke_onSide_left :
    (s.leftRim hn hu hv).OnSide (!G.hubFlip s.left) (.hub s.left (0 : Fin 3)) := by
  have hs := G.sunRimCircuit_spoke_onSide hn hu hv (G.sunRimPort hn s.left true) 0 s.left true rfl
  simpa only [leftRim, Bool.xor_true] using hs

theorem leftRim_spoke_onSide_right :
    (s.leftRim hn hu hv).OnSide (!G.hubFlip s.left) (.hub s.right (0 : Fin 3)) := by
  have hs := ((s.leftRim hn hu hv).onSide_twin_iff
    (G.sunRimCircuit_spoke_unmarked hn hu hv (G.sunRimPort hn s.left true) s.left)
    (!G.hubFlip s.left)).mpr (s.leftRim_spoke_onSide_left hn hu hv)
  exact (congrArg ((s.leftRim hn hu hv).OnSide (!G.hubFlip s.left)) s.paired).mp hs

theorem leftRim_omitted_onSide (x : G.Dart) (hx : ¬ s.Kept x) :
    (s.leftRim hn hu hv).OnSide (!G.hubFlip s.left) x := by
  by_cases hl : x = .hub s.left (0 : Fin 3)
  · subst x
    exact s.leftRim_spoke_onSide_left hn hu hv
  · have hr : x = .hub s.right (0 : Fin 3) := by
      by_contra hr
      exact hx ⟨hl, hr⟩
    subst x
    exact s.leftRim_spoke_onSide_right hn hu hv

theorem leftRim_opposite_spoke_side_iff
    (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
      2 * Nat.card (Component G.circuitStep G.pairing.perm)) (x : G.Dart) :
    Connected G.circuitStep (s.leftRimDeletedPairing hn hu hv)
        x ((s.leftRim hn hu hv).port (0, G.hubFlip s.left)) ↔
      (s.leftRim hn hu hv).OnSide (G.hubFlip s.left) x := by
  rw [s.leftRimDeletedPairing_eq]
  exact (s.leftRim hn hu hv).opposite_deletion_onSide_iff hEuler s.Kept
    (s.leftRim_cut_kept_iff hn hu hv) (G.hubFlip s.left) (s.leftRim_omitted_onSide hn hu hv) x

/-- The original spoke side is exactly the union of the two endpoint
regions after deletion; the two regions may still coincide. -/
theorem leftRim_spoke_side_union (x : G.Dart) :
    (s.leftRim hn hu hv).OnSide (!G.hubFlip s.left) x ↔
      Connected G.circuitStep (s.leftRimDeletedPairing hn hu hv) x (.hub s.left (0 : Fin 3)) ∨
      Connected G.circuitStep (s.leftRimDeletedPairing hn hu hv) x (.hub s.right (0 : Fin 3)) := by
  have hs := s.leftRim_spoke_onSide_left hn hu hv
  have hc : (s.leftRim hn hu hv).OnSide (!G.hubFlip s.left) x ↔
      Connected G.circuitStep (s.leftRim hn hu hv).cutPairing x (.hub s.left (0 : Fin 3)) :=
    ⟨fun h => h.trans hs.symm, fun h => h.trans hs⟩
  apply hc.trans
  have he : CycleSurgery.splice (s.leftRimDeletedPairing hn hu hv)
      (.hub s.left (0 : Fin 3)) (.hub s.right (0 : Fin 3)) = (s.leftRim hn hu hv).cutPairing :=
    s.sun_rim_cut_restoration hn hu hv (G.sunRimPort hn s.left true)
  have hfix : s.leftRimDeletedPairing hn hu hv (.hub s.left (0 : Fin 3)) = .hub s.left (0 : Fin 3) :=
    s.spokeDeletedPairing_fixed _ _ _ (fun h => h.1 rfl)
  rw [← he, connected_splice_iff_of_seam G.circuitStep (s.leftRimDeletedPairing hn hu hv)
    (seam_of_fixed _ _ hfix)]
  constructor
  · rintro (h | ⟨h, _⟩ | ⟨h, _⟩)
    · exact Or.inl h
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨h, Connected.refl _⟩)

theorem leftRim_deleted_spoke_not_opposite
    (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
      2 * Nat.card (Component G.circuitStep G.pairing.perm)) (x : G.Dart) (hx : ¬ s.Kept x) :
    ¬ Connected G.circuitStep (s.leftRimDeletedPairing hn hu hv)
      x ((s.leftRim hn hu hv).port (0, G.hubFlip s.left)) := by
  intro hc
  have hs := (s.leftRim_opposite_spoke_side_iff hn hu hv hEuler x).mp hc
  have he := (s.leftRim hn hu hv).onSide_unique hEuler hs (s.leftRim_omitted_onSide hn hu hv x hx)
  cases hh : G.hubFlip s.left <;> simp only [hh] at he <;> cases he

end ThomGame.Pictures.PortGraph.SunSpoke
