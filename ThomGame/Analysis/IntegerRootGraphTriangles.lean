module

public import ThomGame.Analysis.IntegerHeisenbergTriangle
public import ThomGame.Analysis.IntegralShearLocalCodistance
public import ThomGame.Analysis.IntegerRootGraphCompression

/-! The Heisenberg triangle estimate applied to the actual six-root fixed fields. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis.IntegerRootGraph

open Compressor IntegralShear ThomGame.IntegerRootGraph
open scoped BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem decompositionSpace_edge_root_fixed (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (f : VertexHilbert H)
    (hf : f ∈ decompositionSpace ρ) (r : Root) (i : Fin 4) (s : Root) (hs : s ∈ graphEdgeRoots r i) :
    ρ (of s) (edgeDifference r i f) = edgeDifference r i f :=
  decompositionSpace_edge_mem ρ f hf r i
    ⟨of s, rootSubgroup_le_rootSpan (graphEdgeRoots r i) s hs (of_mem_rootSubgroup s)⟩

theorem vertexInvariants_across_eq_common (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (r : Root) :
    vertexInvariants ρ (across r) = unitaryCommonFixedSpace (ρ (of (right r))) (ρ (of r)) := by
  have ha : across (across r) = r := (show ∀ s : Root, across (across s) = s from by decide +kernel) r
  rw [vertexInvariants, graphVertexGroup_eq_pair, ha, rootPairSubgroup_invariants_eq,
    rootSubgroup_invariants_eq, rootSubgroup_invariants_eq]
  change _ = unitaryFixedSpace (ρ (of (right r))) ⊓ unitaryFixedSpace (ρ (of r))
  exact inf_comm _ _

variable [CompleteSpace H]

def rootEdgeEnergy (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (f : VertexHilbert H) : ℝ :=
  (1 / 2 : ℝ) * ∑ r : Root, ∑ i : Fin 4,
    ‖(unitaryFixedSpace (ρ (of r)))ᗮ.starProjection (edgeDifference r i f)‖ ^ 2

theorem root_triangle_energy (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (f : VertexHilbert H)
    (hf : f ∈ decompositionSpace ρ) (r : Root) :
    ‖f r - f (across r)‖ ^ 2 + ‖f (across r) - f (right r)‖ ^ 2 +
        2 * ‖f r - f (right r)‖ ^ 2 ≤
      5 * (‖(vertexInvariants ρ (across r)).starProjection (f r - f (across r))‖ ^ 2 +
        ‖(vertexInvariants ρ (across r)).starProjection (f (across r) - f (right r))‖ ^ 2) +
      3 * (‖(unitaryFixedSpace (ρ (of (right r))))ᗮ.starProjection (f r - f (right r))‖ ^ 2 +
        ‖(unitaryFixedSpace (ρ (of r)))ᗮ.starProjection (f r - f (right r))‖ ^ 2) := by
  have ha : edgeDifference r 0 f = f r - f (across r) := rfl
  have hbn : neighbor (across r) 3 = right r :=
    (show ∀ s : Root, neighbor (across s) 3 = right s from by decide +kernel) r
  have hb : edgeDifference (across r) 3 f = f (across r) - f (right r) := by
    rw [edgeDifference_apply, hbn]
  have haY := decompositionSpace_edge_root_fixed ρ f hf r 0 r
    ((show ∀ s : Root, s ∈ graphEdgeRoots s 0 from by decide +kernel) r)
  have haZ := decompositionSpace_edge_root_fixed ρ f hf r 0 (across r)
    ((show ∀ s : Root, across s ∈ graphEdgeRoots s 0 from by decide +kernel) r)
  have hbX := decompositionSpace_edge_root_fixed ρ f hf (across r) 3 (right r)
    ((show ∀ s : Root, right s ∈ graphEdgeRoots (across s) 3 from by decide +kernel) r)
  have hbZ := decompositionSpace_edge_root_fixed ρ f hf (across r) 3 (across r)
    ((show ∀ s : Root, across s ∈ graphEdgeRoots (across s) 3 from by decide +kernel) r)
  rw [ha] at haY haZ
  rw [hb] at hbX hbZ
  have hXZ : Commute (ρ (of (right r))) (ρ (of (across r))) :=
    (of_commute (right r) (across r)
      ((show ∀ s : Root, separated (right s) (across s) from by decide +kernel) r)).map ρ
  have h := unitaryHeisenberg_triangle_energy (ρ (of (right r))) (ρ (of r)) (ρ (of (across r)))
    (rootPair_unitary_heisenberg_relation ρ r) (rootPair_unitary_center_commute ρ r) hXZ
    (f r - f (across r)) (f (across r) - f (right r)) haY haZ hbX hbZ
  simpa only [sub_add_sub_cancel, vertexInvariants_across_eq_common] using h

end ThomGame.Analysis.IntegerRootGraph
