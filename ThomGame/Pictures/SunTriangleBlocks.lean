module

public import ThomGame.Pictures.TriangleCancellationBlock
public import ThomGame.Pictures.SunSwitch

/-! # The actual three-port cycles at every slot of a sun hub -/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv CyclicBlock CycleSurgery
open scoped Classical

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  (G : PortGraph (sunPresentation n b) u v)

def sunSlotRotation (h : G.Hub) : Perm (Fin 3) :=
  if G.hubFlip h then (finRotate 3).symm else finRotate 3

theorem sun_slot_rotation_hub (h : G.Hub) (i : Fin 3) :
    G.rotation (.hub h i) = .hub h (G.sunSlotRotation h i) := rfl

theorem sun_same_hubLabel_port_label {h k : G.Hub} (hl : G.hubLabel h = G.hubLabel k)
    (i : Fin 3) : Port.label G.jointLabel (.hub h i : G.Dart) = Port.label G.jointLabel (.hub k i : G.Dart) := by
  fin_cases i <;> simp [Port.label, sunPresentation, hl]

theorem sun_slotRotation_opposite {h k : G.Hub} (hf : G.hubFlip h ≠ G.hubFlip k) :
    G.sunSlotRotation k = (G.sunSlotRotation h).symm := by
  change (if G.hubFlip k then (finRotate 3).symm else finRotate 3) =
    (if G.hubFlip h then (finRotate 3).symm else finRotate 3).symm
  cases hh : G.hubFlip h <;> cases hk : G.hubFlip k <;>
    simp_all

theorem sun_hub_cycleWord (r : Perm G.Dart)
    (hr : ∀ (h : G.Hub) (i : Fin 3), r (.hub h i) = G.rotation (.hub h i)) (h : G.Hub) (i : Fin 3) :
    IsCycleWord r [.hub h i, .hub h (G.sunSlotRotation h i), .hub h ((G.sunSlotRotation h).symm i)] := by
  have hm1 : (-1 : Fin 3) = 2 := by decide +kernel
  refine ⟨?_, by simp, ?_⟩
  · cases hf : G.hubFlip h <;> fin_cases i <;>
      simp [sunSlotRotation, hf, sun_hub_eq_iff] <;> decide +kernel
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    all_goals apply (hr h _).trans
    all_goals rw [G.sun_slot_rotation_hub]
    all_goals cases hf : G.hubFlip h <;> fin_cases i <;>
      simp [sunSlotRotation, hf, List.formPerm, swap_apply_def, sun_hub_eq_iff,
        finRotate_apply, finRotate_symm_apply, hm1]

theorem exists_sun_triangle_cancel_block {T : Type*} (Q : InvolutionPresentation T (Fin n ⊕ Fin n))
    (r : Perm G.Dart) (hr : ∀ (h : G.Hub) (i : Fin 3), r (.hub h i) = G.rotation (.hub h i))
    (h k : G.Hub) (i : Fin 3)
    (he : G.pairing.twin (.hub h i) = .hub k i)
    (hl : G.hubLabel h = G.hubLabel k) (hf : G.hubFlip h ≠ G.hubFlip k)
    (hsep : ¬ r.SameCycle (.hub h i) (G.pairing.twin (.hub h i))) :
    ∃ B : DiagramBlock Q (Port.label G.jointLabel)
        (splice r (.hub h i) (G.pairing.twin (.hub h i)))
        (splice G.pairing.perm (.hub h i) (G.pairing.twin (.hub h i))),
      (.hub h i : G.Dart) ∈ B.ports ∧ B.diagram.labels = [] := by
  have hA := G.sun_hub_cycleWord r hr h i
  have hB : IsCycleWord r [G.pairing.twin (.hub h i),
      .hub k (G.sunSlotRotation k i), .hub k ((G.sunSlotRotation k).symm i)] := by
    rw [he]
    exact G.sun_hub_cycleWord r hr k i
  have hrot := G.sun_slotRotation_opposite hf
  have hx : Port.label G.jointLabel (.hub h (G.sunSlotRotation h i) : G.Dart) =
      Port.label G.jointLabel (.hub k ((G.sunSlotRotation k).symm i) : G.Dart) := by
    rw [hrot, Equiv.symm_symm]
    exact G.sun_same_hubLabel_port_label hl _
  have hy : Port.label G.jointLabel (.hub h ((G.sunSlotRotation h).symm i) : G.Dart) =
      Port.label G.jointLabel (.hub k (G.sunSlotRotation k i) : G.Dart) := by
    rw [hrot]
    exact G.sun_same_hubLabel_port_label hl _
  exact ⟨triangleCancellationBlock Q (Port.label G.jointLabel) r G.pairing.perm
      G.pairing.involutive G.pairing.ne_self _ _ _ _ _ hA hB hsep hx hy,
    List.mem_cons_self, triangleCancellationBlock_labels _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _⟩

end ThomGame.Pictures.PortGraph
