module

public import ThomGame.Analysis.IntegerHeisenbergProjectedCodistance
public import ThomGame.Analysis.IntegerRootGraphTriangles

/-! Strict local estimates for the actual four edge groups at each root vertex. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis.IntegerRootGraph

open Compressor IntegralShear ThomGame.IntegerRootGraph
open scoped BigOperators

theorem four_sum_formula {A : Type*} [AddCommMonoid A] (v : Fin 4 → A) :
    (∑ i : Fin 4, v i) = v 0 + v 1 + v 2 + v 3 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change v 0 + (v 1 + (v 2 + v 3)) = v 0 + v 1 + v 2 + v 3
  abel

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem root_vertex_four_sum_bound (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (r : Root) (v : Fin 4 → H)
    (hv : ∀ (i : Fin 4) (s : Root), s ∈ graphEdgeRoots r i → ρ (of s) (v i) = v i) :
    ‖(vertexInvariants ρ r)ᗮ.starProjection (∑ i : Fin 4, v i)‖ ^ 2 ≤
      2 * (∑ i : Fin 4, ‖v i‖ ^ 2) -
      2 * (∑ i : Fin 4, ‖(vertexInvariants ρ r).starProjection (v i)‖ ^ 2) -
      (1 / 4 : ℝ) * (∑ i : Fin 4, ‖(unitaryFixedSpace (ρ (of r)))ᗮ.starProjection (v i)‖ ^ 2) := by
  have ha : across (across r) = r := (show ∀ s : Root, across (across s) = s from by decide +kernel) r
  have hK : vertexInvariants ρ r =
      unitaryCommonFixedSpace (ρ (of (right (across r)))) (ρ (of (across r))) := by
    simpa only [ha] using vertexInvariants_across_eq_common ρ (across r)
  have hrel : ρ (of (across r)) * ρ (of (right (across r))) =
      ρ (of (right (across r))) * ρ (of r) * ρ (of (across r)) := by
    simpa only [ha] using rootPair_unitary_heisenberg_relation ρ (across r)
  have hYZ : Commute (ρ (of (across r))) (ρ (of r)) := by
    simpa only [ha] using rootPair_unitary_center_commute ρ (across r)
  have hXZ : Commute (ρ (of (right (across r)))) (ρ (of r)) :=
    (of_commute (right (across r)) r
      ((show ∀ s : Root, separated (right (across s)) s from by decide +kernel) r)).map ρ
  have h := unitaryHeisenberg_projected_four_sum
    (ρ (of (right (across r)))) (ρ (of (across r))) (ρ (of r)) hrel hYZ hXZ
    (v 3) (v 0) (v 2) (v 1)
    (hv 3 _ ((show ∀ s : Root, right (across s) ∈ graphEdgeRoots s 3 from by decide +kernel) r))
    (hv 3 _ ((show ∀ s : Root, s ∈ graphEdgeRoots s 3 from by decide +kernel) r))
    (hv 0 _ ((show ∀ s : Root, across s ∈ graphEdgeRoots s 0 from by decide +kernel) r))
    (hv 0 _ ((show ∀ s : Root, s ∈ graphEdgeRoots s 0 from by decide +kernel) r))
    (hv 2 _ ((show ∀ s : Root, right (across s) ∈ graphEdgeRoots s 2 from by decide +kernel) r))
    (hv 1 _ ((show ∀ s : Root, across s ∈ graphEdgeRoots s 1 from by decide +kernel) r))
  simp only [← hK] at h
  have hsum : v 3 + v 0 + v 2 + v 1 = ∑ i : Fin 4, v i := by
    rw [four_sum_formula]
    abel
  rw [hsum] at h
  simp only [four_sum_formula] at h ⊢
  linarith

theorem vertex_laplacian_refined_bound (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (f : VertexHilbert H)
    (hf : f ∈ decompositionSpace ρ) (r : Root) :
    ‖(vertexInvariants ρ r)ᗮ.starProjection (laplacian f r)‖ ^ 2 ≤
      2 * (∑ i : Fin 4, ‖edgeDifference r i f‖ ^ 2) -
      2 * (∑ i : Fin 4, ‖(vertexInvariants ρ r).starProjection (edgeDifference r i f)‖ ^ 2) -
      (1 / 4 : ℝ) * (∑ i : Fin 4,
        ‖(unitaryFixedSpace (ρ (of r)))ᗮ.starProjection (edgeDifference r i f)‖ ^ 2) := by
  rw [laplacian_sum_edgeDifference]
  exact root_vertex_four_sum_bound ρ r (fun i => edgeDifference r i f)
    (fun i s hs => decompositionSpace_edge_root_fixed ρ f hf r i s hs)

end ThomGame.Analysis.IntegerRootGraph
