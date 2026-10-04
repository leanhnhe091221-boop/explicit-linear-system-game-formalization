module

public import ThomGame.Pictures.SunSwitch
public import ThomGame.Pictures.TwoStepReturn

/-!
# Face returns under the equal-orientation sun switch

Each omitted spoke port immediately leads to a retained rim port. Thus
deleting these two ports loses no face orbit. The retained face-return
permutations before and after the switch are conjugate by the actual
exchange of the two rim attachments. Full face-cycle lengths need not
be preserved.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SunSpoke

open Equiv
open scoped Classical

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) u v} (s : G.SunSpoke)

theorem step_spoke_left : G.circuitStep (.hub s.left (0 : Fin 3)) = G.rotation (.hub s.right (0 : Fin 3)) := by
  rw [G.circuitStep_apply, s.paired]

theorem step_spoke_right : G.circuitStep (.hub s.right (0 : Fin 3)) = G.rotation (.hub s.left (0 : Fin 3)) := by
  rw [G.circuitStep_apply, s.paired_right]

theorem switch_step_spoke_left :
    s.switch.circuitStep (.hub s.left (0 : Fin 3)) = s.switch.rotation (.hub s.right (0 : Fin 3)) := by
  rw [s.switch.circuitStep_apply, s.switch_paired]

theorem switch_step_spoke_right :
    s.switch.circuitStep (.hub s.right (0 : Fin 3)) = s.switch.rotation (.hub s.left (0 : Fin 3)) := by
  rw [s.switch.circuitStep_apply, s.switch_paired_right]

theorem step_spoke_left_kept : s.Kept (G.circuitStep (.hub s.left (0 : Fin 3))) := by
  rw [s.step_spoke_left]
  exact ⟨sun_rotation_spoke_ne_spoke _ _, sun_rotation_spoke_ne_spoke _ _⟩

theorem step_spoke_right_kept : s.Kept (G.circuitStep (.hub s.right (0 : Fin 3))) := by
  rw [s.step_spoke_right]
  exact ⟨sun_rotation_spoke_ne_spoke _ _, sun_rotation_spoke_ne_spoke _ _⟩

theorem switch_step_spoke_left_kept : s.Kept (s.switch.circuitStep (.hub s.left (0 : Fin 3))) := by
  rw [s.switch_step_spoke_left]
  exact ⟨sun_rotation_spoke_ne_spoke _ _, sun_rotation_spoke_ne_spoke _ _⟩

theorem switch_step_spoke_right_kept : s.Kept (s.switch.circuitStep (.hub s.right (0 : Fin 3))) := by
  rw [s.switch_step_spoke_right]
  exact ⟨sun_rotation_spoke_ne_spoke _ _, sun_rotation_spoke_ne_spoke _ _⟩

theorem return_val (x : Subtype s.Kept) :
    (MarkedReturn.perm G.circuitStep s.Kept x).val =
      if G.circuitStep x.val = .hub s.left (0 : Fin 3) then G.rotation (.hub s.right (0 : Fin 3))
      else if G.circuitStep x.val = .hub s.right (0 : Fin 3) then G.rotation (.hub s.left (0 : Fin 3))
      else G.circuitStep x.val := by
  refine (MarkedReturn.pair_return_val G.circuitStep _ _
    s.step_spoke_left_kept s.step_spoke_right_kept x).trans ?_
  simp only [s.step_spoke_left, s.step_spoke_right]

theorem switch_return_val (x : Subtype s.Kept) :
    (MarkedReturn.perm s.switch.circuitStep s.Kept x).val =
      if s.switch.circuitStep x.val = .hub s.left (0 : Fin 3) then s.switch.rotation (.hub s.right (0 : Fin 3))
      else if s.switch.circuitStep x.val = .hub s.right (0 : Fin 3) then s.switch.rotation (.hub s.left (0 : Fin 3))
      else s.switch.circuitStep x.val := by
  refine (MarkedReturn.pair_return_val s.switch.circuitStep _ _
    s.switch_step_spoke_left_kept s.switch_step_spoke_right_kept x).trans ?_
  simp only [s.switch_step_spoke_left, s.switch_step_spoke_right]

theorem bypass_rotation (hf : G.hubFlip s.left = G.hubFlip s.right) (y : G.Dart) (hy : s.Kept y) :
    (if s.switch.rotation (s.portSwap y) = .hub s.left (0 : Fin 3) then s.switch.rotation (.hub s.right (0 : Fin 3))
      else if s.switch.rotation (s.portSwap y) = .hub s.right (0 : Fin 3) then s.switch.rotation (.hub s.left (0 : Fin 3))
      else s.switch.rotation (s.portSwap y)) =
    s.portSwap (if G.rotation y = .hub s.left (0 : Fin 3) then G.rotation (.hub s.right (0 : Fin 3))
      else if G.rotation y = .hub s.right (0 : Fin 3) then G.rotation (.hub s.left (0 : Fin 3))
      else G.rotation y) := by
  cases y with
  | top i => simp [rotation, portSwap, swap_apply_def]
  | bottom i => simp [rotation, portSwap, swap_apply_def]
  | joint j side => simp [rotation, portSwap, swap_apply_def]
  | hub h i =>
    change Fin 3 at i
    by_cases hl : h = s.left
    · subst h
      fin_cases i
      · exact (hy.1 rfl).elim
      all_goals
        cases hh : G.hubFlip s.left
        all_goals
          have hk := hf.symm.trans hh
          simp [sun_rotation_hub, portSwap, swap_apply_def, switch, hh, hk,
            s.distinct, Ne.symm s.distinct, sun_hub_eq_iff] <;> decide +kernel
    · by_cases hr : h = s.right
      · subst h
        fin_cases i
        · exact (hy.2 rfl).elim
        all_goals
          cases hh : G.hubFlip s.left
          all_goals
            have hk := hf.symm.trans hh
            simp [sun_rotation_hub, portSwap, swap_apply_def, switch, hh, hk,
              s.distinct, Ne.symm s.distinct, sun_hub_eq_iff] <;> decide +kernel
      · have hvl : (Port.hub h i : G.Dart).vertex ≠ .inr (.inl s.left) := by
          simpa only [Port.vertex, ne_eq, Sum.inr.injEq, Sum.inl.injEq] using hl
        have hvr : (Port.hub h i : G.Dart).vertex ≠ .inr (.inl s.right) := by
          simpa only [Port.vertex, ne_eq, Sum.inr.injEq, Sum.inl.injEq] using hr
        have hrl : (G.rotation (.hub h i)).vertex ≠ .inr (.inl s.left) := by
          rwa [G.vertex_rotation]
        have hrr : (G.rotation (.hub h i)).vertex ≠ .inr (.inl s.right) := by
          rwa [G.vertex_rotation]
        have hpl : G.rotation (.hub h i) ≠ .hub s.left (0 : Fin 3) :=
          fun he => hrl (congrArg Port.vertex he)
        have hpr : G.rotation (.hub h i) ≠ .hub s.right (0 : Fin 3) :=
          fun he => hrr (congrArg Port.vertex he)
        rw [s.portSwap_of_vertex_away hvl hvr, s.switch_rotation_away hvl hvr]
        simp only [hpl, hpr, ite_false]
        exact (s.portSwap_of_vertex_away hrl hrr).symm

theorem return_congr (hf : G.hubFlip s.left = G.hubFlip s.right) (x : Subtype s.Kept) :
    MarkedReturn.perm s.switch.circuitStep s.Kept (s.keptSwap x) =
      s.keptSwap (MarkedReturn.perm G.circuitStep s.Kept x) := by
  apply Subtype.ext
  change (MarkedReturn.perm s.switch.circuitStep s.Kept (s.keptSwap x)).val =
    s.portSwap (MarkedReturn.perm G.circuitStep s.Kept x).val
  rw [s.switch_return_val, s.return_val]
  change (if s.switch.rotation (s.switch.pairing.twin (s.portSwap x.val)) = _ then _ else
    if s.switch.rotation (s.switch.pairing.twin (s.portSwap x.val)) = _ then _ else
      s.switch.rotation (s.switch.pairing.twin (s.portSwap x.val))) = _
  rw [s.switch_twin_portSwap]
  exact s.bypass_rotation hf (G.pairing.twin x.val) (s.twin_kept x.property)

noncomputable def faceOrbitEquiv (hf : G.hubFlip s.left = G.hubFlip s.right) :
    FiniteReturn.Orbit G.circuitStep ≃ FiniteReturn.Orbit s.switch.circuitStep :=
  (MarkedReturn.orbitEquivOfHits G.circuitStep s.Kept
    (MarkedReturn.pair_orbits_hit G.circuitStep _ _ s.step_spoke_left_kept s.step_spoke_right_kept)).symm.trans
      ((FiniteReturn.orbitEquiv _ _ s.keptSwap (s.return_congr hf)).trans
        (MarkedReturn.orbitEquivOfHits s.switch.circuitStep s.Kept
          (MarkedReturn.pair_orbits_hit s.switch.circuitStep _ _
            s.switch_step_spoke_left_kept s.switch_step_spoke_right_kept)))

theorem switch_face_card (hf : G.hubFlip s.left = G.hubFlip s.right) :
    Nat.card (FiniteReturn.Orbit s.switch.circuitStep) = Nat.card (FiniteReturn.Orbit G.circuitStep) :=
  (Nat.card_congr (s.faceOrbitEquiv hf)).symm

end ThomGame.Pictures.PortGraph.SunSpoke
