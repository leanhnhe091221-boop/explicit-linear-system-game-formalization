module

public import ThomGame.Pictures.RimSharedFaceOrientation

/-!
# An oriented split preserves all facial rims of a constellation

Cycles avoiding the cut label are unchanged. Any other base cycle has
opposite facial sides to the selected cycle at both cuts, hence matching
sides of its own. This proves all new facial orbits without expanding
any particular finite constellation or row numbering.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.RowEdgeSwitch

open Equiv
open scoped Classical

variable {R S I : Type*} [DecidableEq R] [DecidableEq S] {A : SparseSystem R S}
  {G : SolutionGroup.RowGraph A [] []} [IsEmpty G.Joint] (s : G.RowEdgeSwitch)
  (Φ : I → Hypergraph.Cycle A.hypergraph)
  (hcommon : ∀ i j : I, i ≠ j → ∀ e f,
    e ∈ Set.range (Φ i).edge → e ∈ Set.range (Φ j).edge →
    f ∈ Set.range (Φ i).edge → f ∈ Set.range (Φ j).edge → e = f)
  (hf : ∀ i : I, ∀ a : G.RimDart (Φ i),
    ∃ side, (G.rimSimpleCircuit (Φ i) (Φ i).empty_boundary_no_rim (Φ i).empty_boundary_no_rim a).BoundsFaceOrbit side)

include hcommon hf in
theorem all_rim_faces_of_oriented (i : I)
    (ha : Port.label G.jointLabel s.first ∈ Set.range (Φ i).edge)
    (hsame : (G.rimWalk (Φ i) (Φ i).empty_boundary_no_rim (Φ i).empty_boundary_no_rim).SameCycle
      ⟨s.first, ha⟩ ⟨s.second, s.label_eq ▸ ha⟩) :
    ∀ m : I, ∀ b : s.graph.RimDart (Φ m),
      ∃ side, (s.graph.rimSimpleCircuit (Φ m) (Φ m).empty_boundary_no_rim (Φ m).empty_boundary_no_rim b).BoundsFaceOrbit side := by
  have hs := G.rimFaceSide_sameCycle (Φ i) (hf i) hsame
  intro m b
  by_cases hm : Port.label G.jointLabel s.first ∈ Set.range (Φ m).edge
  · have hms : G.rimFaceSide (Φ m) ⟨s.first, hm⟩ =
        G.rimFaceSide (Φ m) ⟨s.second, s.label_eq ▸ hm⟩ := by
      by_cases hmi : m = i
      · subst m
        exact hs
      · have hfirst := G.rimFaceSide_shared (Φ i) (Φ m) (hcommon i m (Ne.symm hmi))
          s.first ha hm (hf i) (hf m)
        have hsecond := G.rimFaceSide_shared (Φ i) (Φ m) (hcommon i m (Ne.symm hmi))
          s.second (s.label_eq ▸ ha) (s.label_eq ▸ hm) (hf i) (hf m)
        exact hfirst.trans ((congrArg Bool.not hs).trans hsecond.symm)
    exact s.rim_faces_of_same_side (Φ m) hm hms (hf m) b
  · apply s.rim_faces_of_refines (Φ m) ?_ (hf m) b
    intro x y hxy
    rw [s.rimWalk_of_avoids (Φ m) hm] at hxy
    exact hxy

end ThomGame.Pictures.PortGraph.RowEdgeSwitch
