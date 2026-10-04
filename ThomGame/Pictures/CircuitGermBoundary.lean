module

public import ThomGame.Pictures.CircuitGermConnectivity
public import ThomGame.Pictures.GraphBoundaryComponents

/-!
# The actual boundary-return order of a circuit germ

The outer sector of the twisted rim rotation embeds into the germ face
by exiting each original port across its edge. A marked successor takes
one face step; an outward successor takes two, through its original port.
The resulting boundary successor follows the stored frontier enumeration
forward, explicitly recording the direction of the current convention.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open Equiv RibbonConnectivity MarkedReturn
open scoped Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {G : PortGraph P [] []}
    (C : G.SimpleCircuit)
    (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
      2 * Nat.card (Component G.circuitStep G.pairing.perm))

theorem marked_edgeTwist_iff (a : G.Dart) : C.Marked (C.edgeTwist a) ↔ C.Marked a := by
  by_cases ha : C.Marked a
  · rw [C.edgeTwist_of_marked ha, C.marked_twin_iff]
  · rw [C.edgeTwist_of_unmarked a ha]

theorem sector_next {s : Bool} {a : G.Dart} (ha : C.Sector s a) :
    C.Sector s ((C.edgeTwist * G.rotation) a) := ha.apply_right

theorem sector_germVertex {s : Bool} {a : G.Dart} (ha : C.Sector s a) :
    C.GermVertex s a.vertex :=
  Or.inl ((C.onCircuitVertex_iff_sector a).mpr ⟨s, ha⟩)

noncomputable def germSectorExit (s : Bool) (a : Subtype (C.Sector s)) :
    (C.germGraph hEuler s).Dart :=
  (C.germGraph hEuler s).pairing.twin
    (C.germInternalPort hEuler s ⟨a.val, C.sector_germVertex a.property⟩)

include hEuler in
theorem germInternalPort_not_boundary (s : Bool)
    (a : {a : G.Dart // C.GermVertex s a.vertex}) :
    ¬ (C.germGraph hEuler s).IsBoundary (C.germInternalPort hEuler s a) := by
  rcases a with ⟨a, ha⟩
  cases a with
  | top i => exact i.elim0
  | bottom i => exact i.elim0
  | hub h i =>
    rw [C.germInternalPort_hub hEuler s ⟨h, ha⟩]
    exact fun h => h
  | joint j b =>
    rw [C.germInternalPort_joint hEuler s ⟨j, ha⟩]
    exact fun h => h

include hEuler in
theorem germSectorExit_outward (s : Bool) (a : Subtype (C.Sector s)) (ha : ¬ C.Marked a.val) :
    C.germSectorExit hEuler s a = .bottom ((C.boundaryEnumeration (!s)).symm
      ⟨a.val, by simpa only [Frontier, Bool.not_not] using And.intro a.property ha⟩) :=
  C.germGraph_twin_internal_outward hEuler s _
    (by simpa only [Frontier, Bool.not_not] using And.intro a.property ha)

include hEuler in
theorem germSectorExit_marked (s : Bool) (a : Subtype (C.Sector s)) (ha : C.Marked a.val) :
    C.germSectorExit hEuler s a = C.germInternalPort hEuler s
      ⟨G.pairing.twin a.val, Or.inl (C.marked_onCircuitVertex ((C.marked_twin_iff _).mpr ha))⟩ :=
  C.germGraph_twin_internal_uncut hEuler s _ (Or.inl ha)

include hEuler in
theorem germSectorExit_marked_not_boundary (s : Bool) (a : Subtype (C.Sector s))
    (ha : C.Marked a.val) : ¬ (C.germGraph hEuler s).IsBoundary (C.germSectorExit hEuler s a) := by
  rw [C.germSectorExit_marked hEuler s a ha]
  exact C.germInternalPort_not_boundary hEuler s _

include hEuler in
theorem germSectorExit_step (s : Bool) (a : Subtype (C.Sector s)) :
    (C.germGraph hEuler s).circuitStep (C.germSectorExit hEuler s a) =
      C.germInternalPort hEuler s ⟨G.rotation a.val,
        by rw [G.vertex_rotation]; exact C.sector_germVertex a.property⟩ := by
  rw [(C.germGraph hEuler s).circuitStep_apply]
  change (C.germGraph hEuler s).rotation
    ((C.germGraph hEuler s).pairing.twin ((C.germGraph hEuler s).pairing.twin _)) = _
  rw [(C.germGraph hEuler s).pairing.involutive, C.germInternalPort_rotation]

include hEuler in
theorem germSectorExit_next_marked (s : Bool) (a : Subtype (C.Sector s))
    (ha : C.Marked ((C.edgeTwist * G.rotation) a.val)) :
    (C.germGraph hEuler s).circuitStep (C.germSectorExit hEuler s a) =
      C.germSectorExit hEuler s ⟨(C.edgeTwist * G.rotation) a.val, C.sector_next a.property⟩ := by
  have hr : C.Marked (G.rotation a.val) := (C.marked_edgeTwist_iff _).mp ha
  rw [C.germSectorExit_step, C.germSectorExit_marked hEuler s _ ha]
  apply congrArg (C.germInternalPort hEuler s)
  apply Subtype.ext
  change G.rotation a.val = G.pairing.twin (C.edgeTwist (G.rotation a.val))
  rw [C.edgeTwist_of_marked hr, G.pairing.involutive]

include hEuler in
theorem germSectorExit_next_unmarked (s : Bool) (a : Subtype (C.Sector s))
    (ha : ¬ C.Marked ((C.edgeTwist * G.rotation) a.val)) :
    (C.germGraph hEuler s).circuitStep
      ((C.germGraph hEuler s).circuitStep (C.germSectorExit hEuler s a)) =
        C.germSectorExit hEuler s ⟨(C.edgeTwist * G.rotation) a.val, C.sector_next a.property⟩ := by
  have hr : ¬ C.Marked (G.rotation a.val) := fun hm => ha ((C.marked_edgeTwist_iff _).mpr hm)
  have he : (C.edgeTwist * G.rotation) a.val = G.rotation a.val := C.edgeTwist_of_unmarked _ hr
  have hfront : C.Frontier (!s) (G.rotation a.val) := by
    refine ⟨?_, hr⟩
    simpa only [Bool.not_not, he] using C.sector_next a.property
  rw [C.germSectorExit_step, (C.germGraph hEuler s).circuitStep_apply,
    C.germGraph_twin_internal_outward hEuler s _ hfront,
    C.germSectorExit_outward hEuler s _ ha]
  change Port.bottom _ = Port.bottom _
  apply congrArg Port.bottom
  apply congrArg (C.boundaryEnumeration (!s)).symm
  exact Subtype.ext he.symm

include hEuler in
theorem germSectorExit_hit (s : Bool) {a b : G.Dart}
    (h : Hit (C.edgeTwist * G.rotation) (C.Frontier (!s)) a b)
    (ha : C.Sector s a) (hb : C.Frontier (!s) b) :
    Hit (C.germGraph hEuler s).circuitStep (C.germGraph hEuler s).IsBoundary
      (C.germSectorExit hEuler s ⟨a, ha⟩)
      (C.germSectorExit hEuler s ⟨b, by simpa only [Bool.not_not] using hb.1⟩) := by
  induction h with
  | direct a =>
    apply Hit.skip _
    · rw [C.germSectorExit_step]
      exact C.germInternalPort_not_boundary hEuler s _
    · rw [← C.germSectorExit_next_unmarked hEuler s ⟨a, ha⟩ hb.2]
      exact Hit.direct _
  | skip a hn tail ih =>
    have hnext := C.sector_next ha
    have hm : C.Marked ((C.edgeTwist * G.rotation) a) := by
      by_contra hm
      apply hn
      exact ⟨by simpa only [Bool.not_not] using hnext, hm⟩
    apply Hit.skip _
    · rw [C.germSectorExit_next_marked hEuler s ⟨a, ha⟩ hm]
      exact C.germSectorExit_marked_not_boundary hEuler s _ hm
    · rw [C.germSectorExit_next_marked hEuler s ⟨a, ha⟩ hm]
      exact ih hnext hb

theorem boundaryEnumeration_return (s : Bool) (i : Fin (C.frontierWord s).length) :
    perm (C.edgeTwist * G.rotation) (C.Frontier s) (C.boundaryEnumeration s i) =
      C.boundaryEnumeration s (finRotate _ i) := by
  have hcast {m n : Nat} (h : m = n) (j : Fin m) :
      finRotate n (finCongr h j) = finCongr h (finRotate m j) := by
    subst n
    rfl
  change perm _ _ (C.frontierEnumeration s (finCongr (C.frontierWord_length s) i)) =
    C.frontierEnumeration s (finCongr (C.frontierWord_length s) (finRotate _ i))
  rw [C.frontierEnumeration_return, hcast]

include hEuler in
theorem germGraph_boundaryNext_bottom (s : Bool) (i : Fin (C.frontierWord (!s)).length) :
    (C.germGraph hEuler s).boundaryNext (.inr i) = .inr (finRotate _ i) := by
  have hp := hit_perm (C.edgeTwist * G.rotation) (C.Frontier (!s)) (C.boundaryEnumeration (!s) i)
  rw [C.boundaryEnumeration_return] at hp
  have hi := (C.boundaryEnumeration (!s) i).property
  have hj := (C.boundaryEnumeration (!s) (finRotate _ i)).property
  have hh := C.germSectorExit_hit hEuler s hp
    (by simpa only [Bool.not_not] using hi.1) hj
  rw [C.germSectorExit_outward hEuler s _ hi.2,
    C.germSectorExit_outward hEuler s _ hj.2] at hh
  change Hit (C.germGraph hEuler s).circuitStep (C.germGraph hEuler s).IsBoundary
    (.bottom ((C.boundaryEnumeration (!s)).symm (C.boundaryEnumeration (!s) i)))
    (.bottom ((C.boundaryEnumeration (!s)).symm
      (C.boundaryEnumeration (!s) (finRotate _ i)))) at hh
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at hh
  apply (C.germGraph hEuler s).boundaryDart.injective
  have hr := (eq_perm_of_hit (C.germGraph hEuler s).circuitStep
    (C.germGraph hEuler s).IsBoundary ((C.germGraph hEuler s).boundaryPorts (.inr i))
    (by trivial) hh).symm
  rw [(C.germGraph hEuler s).boundaryPorts_next] at hr
  exact hr

include hEuler in
theorem germGraph_boundary_one_cycle (s : Bool)
    (a b : BoundaryIndex [] (C.frontierWord (!s))) :
    (C.germGraph hEuler s).boundaryNext.SameCycle a b := by
  let e : Fin (C.frontierWord (!s)).length ↪ BoundaryIndex [] (C.frontierWord (!s)) :=
    Function.Embedding.inr
  have he : FiniteReturn.Advances (C.germGraph hEuler s).boundaryNext (finRotate _) e :=
    fun i => Or.inl (C.germGraph_boundaryNext_bottom hEuler s i).symm
  cases a with
  | inl i => exact i.elim0
  | inr i =>
    cases b with
    | inl j => exact j.elim0
    | inr j => exact he.expand (finRotate_sameCycle i j)

include hEuler in
theorem germGraph_boundarySeesComponents (s : Bool) :
    (C.germGraph hEuler s).BoundarySeesComponents :=
  (C.germGraph hEuler s).boundarySeesComponents_of_one_cycle (C.germGraph_boundary_one_cycle hEuler s)

end ThomGame.Pictures.PortGraph.SimpleCircuit
