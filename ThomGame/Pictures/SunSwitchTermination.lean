module

public import ThomGame.Pictures.SunTotalInteriorDescent

/-!
# A finite sequence of actual inward-spoke switches reaches a terminal graph

The measure is the sum of the actual boundary-opposite spoke counts over
unoriented rim components. The trace records that every selected spoke
belongs to the cut interior, and every such step strictly decreases the
measure. Its endpoint has no internal hub-to-hub spoke directed into its
own rim. This is a termination theorem for the port-graph surgery, not
yet a geometric facial-cover or constellation normalization theorem.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open RibbonConnectivity
open scoped Classical

variable {n : Nat} {b : Fin n → ZMod 2} {w : List (Fin n ⊕ Fin n)}
  (hn : 3 ≤ n) (hw : ∀ z ∈ w, ∃ j, z = Sum.inl j)

def NoInteriorSunSpoke (G : PortGraph (sunPresentation n b) [] w) : Prop :=
  ∀ s : G.SunSpoke, ¬ (s.leftRim hn (by simp) hw).CutInterior (.hub s.left (0 : Fin 3))

namespace SunSpoke

theorem switch_rims_meetBoundary {G : PortGraph (sunPresentation n b) [] w}
    (s : G.SunSpoke)
    (hb : ∀ a : G.SunRimDart hn, (G.sunRimSimpleCircuit hn (by simp) hw a).MeetsBoundary) :
    ∀ a : s.switch.SunRimDart hn, (s.switch.sunRimSimpleCircuit hn (by simp) hw a).MeetsBoundary :=
  fun a => (s.switch_rim_meetsBoundary_iff hn (by simp) hw a).mpr (hb a)

end SunSpoke

namespace SunSwitchTrace

noncomputable def Inward {G H : PortGraph (sunPresentation n b) [] w}
    (t : SunSwitchTrace G H) : Prop :=
  match t with
  | .refl _ => True
  | .step s tail => (s.leftRim hn (by simp) hw).CutInterior (.hub s.left (0 : Fin 3)) ∧
      Inward tail

theorem rims_meetBoundary {G H : PortGraph (sunPresentation n b) [] w}
    (t : SunSwitchTrace G H)
    (hb : ∀ a : G.SunRimDart hn, (G.sunRimSimpleCircuit hn (by simp) hw a).MeetsBoundary) :
    ∀ a : H.SunRimDart hn, (H.sunRimSimpleCircuit hn (by simp) hw a).MeetsBoundary := by
  induction t with
  | refl _ => exact hb
  | step s _ ih => exact ih (s.switch_rims_meetBoundary hn hw hb)

theorem isEmpty_joints {G H : PortGraph (sunPresentation n b) [] w}
    (t : SunSwitchTrace G H) (hJ : IsEmpty G.Joint) : IsEmpty H.Joint := by
  induction t with
  | refl _ => exact hJ
  | step _ _ ih => exact ih hJ

end SunSwitchTrace

namespace SunMinimalState

variable {G : PortGraph (sunPresentation n b) [] w} (h : G.SunMinimalState)
  (hb : ∀ a : G.SunRimDart hn, (G.sunRimSimpleCircuit hn (by simp) hw a).MeetsBoundary)

include h in
theorem switch_interior_measure_lt (s : G.SunSpoke)
    (hi : (s.leftRim hn (by simp) hw).CutInterior (.hub s.left (0 : Fin 3))) :
    s.switch.sunTotalInteriorSpokeCount hn (by simp) hw (h.switch s).euler (h.switch s).sees
      (s.switch_rims_meetBoundary hn hw hb) <
      G.sunTotalInteriorSpokeCount hn (by simp) hw h.euler h.sees hb := by
  exact s.total_interior_spoke_count_lt hn (by simp) hw h.euler (h.same_flip s) h.sees
    (h.switch s).euler (h.switch s).sees hb (s.switch_rims_meetBoundary hn hw hb)
    (((s.leftRim hn (by simp) hw).on_opposite_boundarySide_iff
      (G.dualEuler_eq_twice_components h.euler) h.sees (hb (G.sunRimPort hn s.left true)) _).mpr hi)

include h hb in
theorem exists_no_interior_spoke :
    ∃ (H : PortGraph (sunPresentation n b) [] w) (t : SunSwitchTrace G H),
      t.Inward hn hw ∧ H.NoInteriorSunSpoke hn hw := by
  generalize hk : G.sunTotalInteriorSpokeCount hn (by simp) hw h.euler h.sees hb = k
  induction k using Nat.strong_induction_on generalizing G with
  | h k ih =>
    by_cases hdone : G.NoInteriorSunSpoke hn hw
    · exact ⟨G, .refl G, trivial, hdone⟩
    · obtain ⟨s, hs⟩ : ∃ s : G.SunSpoke,
          (s.leftRim hn (by simp) hw).CutInterior (.hub s.left (0 : Fin 3)) := by
        simpa only [NoInteriorSunSpoke, not_forall, not_not] using hdone
      have hlt := h.switch_interior_measure_lt hn hw hb s hs
      rw [hk] at hlt
      obtain ⟨H, tail, htail, hterminal⟩ := ih _ hlt (h.switch s) (s.switch_rims_meetBoundary hn hw hb) rfl
      exact ⟨H, .step s tail, ⟨hs, htail⟩, hterminal⟩

end SunMinimalState

namespace SunSwitchTrace

theorem inward_length_bound {G H : PortGraph (sunPresentation n b) [] w}
    (t : SunSwitchTrace G H) (h : G.SunMinimalState)
    (hb : ∀ a : G.SunRimDart hn, (G.sunRimSimpleCircuit hn (by simp) hw a).MeetsBoundary)
    (hi : t.Inward hn hw) :
    H.sunTotalInteriorSpokeCount hn (by simp) hw (t.minimalState h).euler (t.minimalState h).sees
        (t.rims_meetBoundary hn hw hb) + t.length ≤
      G.sunTotalInteriorSpokeCount hn (by simp) hw h.euler h.sees hb := by
  induction t with
  | refl G => exact Nat.le_refl _
  | @step G H s tail ih =>
    have hlt := h.switch_interior_measure_lt hn hw hb s hi.1
    have htail := ih (h.switch s) (s.switch_rims_meetBoundary hn hw hb) hi.2
    change H.sunTotalInteriorSpokeCount hn (by simp) hw _ _ _ + (tail.length + 1) ≤ _
    omega

end SunSwitchTrace
end ThomGame.Pictures.PortGraph
