module

public import ThomGame.Pictures.RimFaceOrientation

/-!
# Positive rim turns propagate the actual hub orientation

When the retained incoming slot is the predecessor of the outgoing slot,
the intrinsic side of a facial rim is exactly the original hub flip.
One actual rim step therefore equates the flips of its endpoint hubs.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv

variable {R S : Type*} [DecidableEq R] [DecidableEq S] {A : SparseSystem R S}
  (G : SolutionGroup.RowGraph A [] []) [IsEmpty G.Joint]
  (γ : Hypergraph.Cycle A.hypergraph)

theorem rimFaceSide_positive_turn (h : G.Hub) (p : Fin 3)
    (hp : Port.label G.jointLabel (.hub h p : G.Dart) ∈ Set.range γ.edge)
    (hi : Port.label G.jointLabel (.hub h ((finRotate 3).symm p) : G.Dart) ∈ Set.range γ.edge) :
    G.rimFaceSide γ ⟨.hub h p, hp⟩ = G.hubFlip h := by
  let x : G.RimDart γ := ⟨.hub h p, hp⟩
  let y : G.RimDart γ := ⟨.hub h ((finRotate 3).symm p), hi⟩
  have hne : y ≠ x := by
    intro he
    have hh := (G.row_hub_eq_iff.mp (congrArg Subtype.val he)).2
    have hn : ∀ i : Fin 3, (finRotate 3).symm i ≠ i := by decide +kernel
    exact hn p hh
  have hs := (G.rimSwitch_unique γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim x y rfl hne).symm
  apply G.rimFaceSide_eq_of_corner γ
  cases hf : G.hubFlip h
  · change G.rotation (G.rimSwitch γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim x).val = x.val
    rw [hs]
    change G.rotation (.hub h ((finRotate 3).symm p)) = .hub h p
    rw [G.row_slot_rotation_hub]
    exact congrArg (fun i : Fin 3 => (.hub h i : G.Dart))
      (by simp [rowSlotRotation, hf])
  · change G.rotation x.val = (G.rimSwitch γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim x).val
    rw [hs]
    change G.rotation (.hub h p) = .hub h ((finRotate 3).symm p)
    rw [G.row_slot_rotation_hub]
    exact congrArg (fun i : Fin 3 => (.hub h i : G.Dart))
      (by simp [rowSlotRotation, hf])

theorem hubFlip_eq_of_facial_rim_step
    (hf : ∀ a : G.RimDart γ,
      ∃ side, (G.rimSimpleCircuit γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim a).BoundsFaceOrbit side)
    (h k : G.Hub) (p q : Fin 3)
    (hp : Port.label G.jointLabel (.hub h p : G.Dart) ∈ Set.range γ.edge)
    (hpi : Port.label G.jointLabel (.hub h ((finRotate 3).symm p) : G.Dart) ∈ Set.range γ.edge)
    (hq : Port.label G.jointLabel (.hub k q : G.Dart) ∈ Set.range γ.edge)
    (hqi : Port.label G.jointLabel (.hub k ((finRotate 3).symm q) : G.Dart) ∈ Set.range γ.edge)
    (ht : G.pairing.twin (.hub h p) = .hub k ((finRotate 3).symm q)) :
    G.hubFlip h = G.hubFlip k := by
  let x : G.RimDart γ := ⟨.hub h p, hp⟩
  let y : G.RimDart γ := ⟨.hub k q, hq⟩
  have hn : y ≠ (G.rimPairing γ).twin x := by
    intro he
    have hh : (.hub k q : G.Dart) = .hub k ((finRotate 3).symm q) :=
      (congrArg Subtype.val he).trans ht
    have hneq : ∀ i : Fin 3, i ≠ (finRotate 3).symm i := by decide +kernel
    exact hneq q (G.row_hub_eq_iff.mp hh).2
  have hv : y.val.vertex = ((G.rimPairing γ).twin x).val.vertex :=
    (congrArg Port.vertex ht).symm
  have hw : G.rimWalk γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim x = y :=
    (G.rimSwitch_unique γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim
      ((G.rimPairing γ).twin x) y hv hn).symm
  have hc : (G.rimWalk γ γ.empty_boundary_no_rim γ.empty_boundary_no_rim).SameCycle x y :=
    hw ▸ Perm.SameCycle.rfl.apply_right
  exact (G.rimFaceSide_positive_turn γ h p hp hpi).symm.trans
    ((G.rimFaceSide_sameCycle γ hf hc).trans (G.rimFaceSide_positive_turn γ k q hq hqi))

end ThomGame.Pictures.PortGraph
