module

public import ThomGame.Pictures.RowEdgeCancellation
public import ThomGame.Pictures.CycleIntersectionTurns
public import ThomGame.Pictures.FacialCircuitMarked
public import ThomGame.Pictures.CircuitHubPorts

/-!
# Facial rims in an actual minimal odd row graph are label covers

At equally labelled hubs the paired slots agree. A facial rim forces
opposite hub orientations: otherwise forward and backward face turns
would put all three row slots on a cycle which has only two. The genuine
two-hub cancellation then contradicts minimality. This proves the closed
minimal odd row-graph instance of Slofstra Proposition 9.4.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv
open scoped Classical

variable {R S : Type*} [DecidableEq R] [DecidableEq S] {A : SparseSystem R S}
  (G : SolutionGroup.RowGraph A [] []) [IsEmpty G.Joint]

omit [DecidableEq R] [DecidableEq S] [IsEmpty G.Joint] in
theorem row_same_label_paired_slot (h k : G.Hub) (i j : Fin 3)
    (he : G.pairing.twin (.hub h i) = .hub k j) (hl : G.hubLabel h = G.hubLabel k) : i = j := by
  have hp := G.pairing.label_twin (.hub h i)
  rw [he] at hp
  simp only [SolutionGroup.rowGraph_port_label, ← hl] at hp
  exact (A.column_injective _ hp).symm

variable (γ : Hypergraph.Cycle A.hypergraph) (a : G.RimDart γ)

omit [IsEmpty G.Joint] in
theorem rim_facial_port_flip_ne (side : Bool)
    (hf : (G.rimSimpleCircuit γ (by simp) (by simp) a).BoundsFaceOrbit side)
    (h k : G.Hub) (i : Fin 3)
    (he : G.pairing.twin (.hub h i) = .hub k i) (hl : G.hubLabel h = G.hubLabel k)
    (hp : ∃ j, (G.rimSimpleCircuit γ (by simp) (by simp) a).port (j, side) = .hub h i) :
    G.hubFlip h ≠ G.hubFlip k := by
  intro hflip
  let C := G.rimSimpleCircuit γ (by simp) (by simp) a
  have horbit : G.circuitStep.SameCycle (.hub h i) (C.port (0, side)) := (hf _).mpr hp
  have hmarked : C.Marked (.hub h i) := by
    obtain ⟨j, hj⟩ := hp
    exact ⟨(j, side), hj⟩
  have hprev : G.circuitStep.SameCycle (G.circuitStep.symm (.hub h i)) (C.port (0, side)) := by
    apply Perm.sameCycle_apply_left.mp
    simpa only [Equiv.apply_symm_apply] using horbit
  have hmark (x : G.Dart) (hx : G.circuitStep.SameCycle x (C.port (0, side))) : C.Marked x := by
    obtain ⟨j, hj⟩ := (hf _).mp hx
    exact ⟨(j, side), hj⟩
  have hnext := G.rimSimpleCircuit_marked_label γ a (hmark _ horbit.apply_left)
  rw [G.circuitStep_apply, he, G.row_slot_rotation_hub,
    SolutionGroup.rowGraph_port_label, ← hl] at hnext
  have hback : C.Marked (G.rotation.symm (.hub h i)) := by
    apply (C.marked_twin_iff _).mp
    exact hmark _ hprev
  have hback' := G.rimSimpleCircuit_marked_label γ a hback
  change Port.label G.jointLabel (.hub h ((G.rowSlotRotation h).symm i) : G.Dart) ∈ _ at hback'
  rw [SolutionGroup.rowGraph_port_label] at hback'
  have hstart := G.rimSimpleCircuit_marked_label γ a hmarked
  rw [SolutionGroup.rowGraph_port_label] at hstart
  have hrot : G.rowSlotRotation k = G.rowSlotRotation h := by simp only [rowSlotRotation, hflip]
  rw [hrot] at hnext
  have hexhaust : ∀ j : Fin 3, j = i ∨ j = G.rowSlotRotation h i ∨ j = (G.rowSlotRotation h).symm i := by
    cases hh : G.hubFlip h <;> fin_cases i <;> intro j <;> fin_cases j <;>
      simp [rowSlotRotation, hh] <;> decide +kernel
  have hall (j : Fin 3) : A.column (G.hubLabel h) j ∈ Set.range γ.edge := by
    rcases hexhaust j with rfl | rfl | rfl
    · exact hstart
    · exact hnext
    · exact hback'
  obtain ⟨v, hv⟩ := G.rimSimpleCircuit_hub_label γ a h (C.marked_onCircuitVertex hmarked)
  have hcard := γ.row_rim_card v
  have hall' : ∀ j : Fin 3, A.column (γ.vertex v) j ∈ Set.range γ.edge := by
    rw [hv]
    exact hall
  simp only [hall', Fintype.card_subtype_true, Fintype.card_fin] at hcard
  omega

namespace ClosedMinimalOddState

variable {G} (H : G.ClosedMinimalOddState)

include H in
theorem rim_isLabelCover_of_facial
    (hf : ∃ side, (G.rimSimpleCircuit γ (by simp) (by simp) a).BoundsFaceOrbit side) :
    (G.rimSimpleCircuit γ (by simp) (by simp) a).IsLabelCover := by
  let C := G.rimSimpleCircuit γ (by simp) (by simp) a
  obtain ⟨side, hface⟩ := hf
  intro j
  obtain ⟨h, p, _, hj, _, _⟩ := C.exists_hub_ports j
  let k := C.hubAt (finRotate C.length j)
  obtain ⟨q, hq⟩ := C.port_eq_hubAt (finRotate C.length j) true
  have ht : G.pairing.twin (C.dart j) = .hub k q := by
    simpa only [SimpleCircuit.port, SimpleCircuit.incoming, Equiv.symm_apply_apply] using hq
  have he : G.pairing.twin (.hub h p) = .hub k q := (congrArg G.pairing.twin hj).symm.trans ht
  have hlabels : G.hubLabel h ≠ G.hubLabel k := by
    intro hl
    have hpq := G.row_same_label_paired_slot h k p q he hl
    subst q
    have hflip := H.row_same_flip_of_same_label_edge h k p he hl
    have hm : C.Marked (.hub h p) := ⟨(j, false), hj⟩
    rcases (C.marked_iff_side_or_twin side _).mp hm with hp | hp
    · exact G.rim_facial_port_flip_ne γ a side hface h k p he hl hp hflip
    · have he' : G.pairing.twin (.hub k p) = .hub h p :=
        (congrArg G.pairing.twin he).symm.trans (G.pairing.involutive _)
      rw [he] at hp
      exact G.rim_facial_port_flip_ne γ a side hface k h p he' hl.symm hp hflip.symm
  exact ⟨h, k, p, q, hj, ht, fun hk => hlabels (congrArg G.hubLabel hk), hlabels⟩

end ClosedMinimalOddState
end ThomGame.Pictures.PortGraph
