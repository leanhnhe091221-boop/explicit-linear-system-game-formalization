module

public import ThomGame.Pictures.GraphSmoothing

/-!
# Finite sequences eliminating all degree-two junctions

Each step is the actual port-pairing surgery. The trace records every removed
isolated circle by its label. Boundary words and relation vertices, including
their cyclic orientations, are preserved. No planar embedding is assumed.
-/

@[expose] public section
namespace ThomGame.Pictures

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}

inductive Smoothing : PortGraph P u v → PortGraph P u v → List S → Type (max 1 u_1 u_2)
  | refl (G : PortGraph P u v) : Smoothing G G []
  | step {G H : PortGraph P u v} {circles : List S} (j : G.Joint)
      (tail : Smoothing (G.smooth j) H circles) :
      Smoothing G H (G.smoothCircles j ++ circles)

namespace Smoothing

variable {G H : PortGraph P u v} {circles : List S}

noncomputable def steps : {G H : PortGraph P u v} → {circles : List S} → Smoothing G H circles → Nat
  | _, _, _, .refl _ => 0
  | _, _, _, .step _ tail => tail.steps + 1

noncomputable def hubEquiv : {G H : PortGraph P u v} → {circles : List S} →
    Smoothing G H circles → G.Hub ≃ H.Hub
  | _, _, _, .refl _ => Equiv.refl _
  | _, _, _, .step _ tail => tail.hubEquiv

theorem hubLabel (d : Smoothing G H circles) (h : G.Hub) :
    H.hubLabel (d.hubEquiv h) = G.hubLabel h := by
  induction d with
  | refl _ => rfl
  | step j tail ih => exact ih h

theorem hubFlip (d : Smoothing G H circles) (h : G.Hub) :
    H.hubFlip (d.hubEquiv h) = G.hubFlip h := by
  induction d with
  | refl _ => rfl
  | step j tail ih => exact ih h

theorem sign (d : Smoothing G H circles) : H.sign = G.sign := by
  induction d with
  | refl _ => rfl
  | step j tail ih => exact ih

theorem hub_card (d : Smoothing G H circles) : Fintype.card H.Hub = Fintype.card G.Hub :=
  (Fintype.card_congr d.hubEquiv).symm

theorem joint_card (d : Smoothing G H circles) :
    Fintype.card H.Joint + d.steps = Fintype.card G.Joint := by
  induction d with
  | refl _ => rfl
  | @step G H circles j tail ih =>
    have h := G.smooth_joint_card j
    change Fintype.card H.Joint + (tail.steps + 1) = _
    omega

theorem edge_card (d : Smoothing G H circles) :
    Fintype.card H.Edge + d.steps = Fintype.card G.Edge := by
  induction d with
  | refl _ => rfl
  | @step G H circles j tail ih =>
    have h := G.smooth_edge_card j
    change Fintype.card H.Edge + (tail.steps + 1) = _
    omega

theorem circles_length_le (d : Smoothing G H circles) : circles.length ≤ d.steps := by
  induction d with
  | refl _ => exact Nat.le_refl 0
  | @step G H circles j tail ih =>
    have hj : (G.smoothCircles j).length ≤ 1 := by
      unfold PortGraph.smoothCircles
      split <;> simp
    change (G.smoothCircles j ++ circles).length ≤ tail.steps + 1
    rw [List.length_append]
    omega

/-- Every finite port graph admits a finite, fully specified smoothing trace. -/
theorem exists_without_junctions (G : PortGraph P u v) :
    ∃ (H : PortGraph P u v) (circles : List S),
      Nonempty (Smoothing G H circles) ∧ IsEmpty H.Joint := by
  classical
  generalize hn : Fintype.card G.Joint = n
  induction n using Nat.strong_induction_on generalizing G with
  | h n ih =>
    by_cases hG : Nonempty G.Joint
    · obtain ⟨j⟩ := hG
      have hlt : Fintype.card (G.smooth j).Joint < n := by
        rw [← hn]
        exact G.smooth_joint_card_lt j
      obtain ⟨H, circles, ⟨d⟩, hempty⟩ := ih _ hlt (G.smooth j) rfl
      exact ⟨H, G.smoothCircles j ++ circles, ⟨d.step j⟩, hempty⟩
    · exact ⟨G, [], ⟨.refl G⟩, not_nonempty_iff.mp hG⟩

theorem steps_of_no_junctions (d : Smoothing G H circles) [IsEmpty H.Joint] :
    d.steps = Fintype.card G.Joint := by
  simpa using d.joint_card

end Smoothing

namespace Diagram

theorem exists_smoothed_graph (d : Diagram P u v) :
    ∃ (H : PortGraph P u v) (circles : List S),
      Nonempty (Smoothing d.graph H circles) ∧ IsEmpty H.Joint ∧
        H.sign = d.sign ∧ Fintype.card H.Hub = d.size := by
  obtain ⟨H, circles, ⟨h⟩, hempty⟩ := Smoothing.exists_without_junctions d.graph
  exact ⟨H, circles, ⟨h⟩, hempty, h.sign.trans d.graph_sign, h.hub_card.trans d.graph_hub_card⟩

end Diagram
end ThomGame.Pictures
