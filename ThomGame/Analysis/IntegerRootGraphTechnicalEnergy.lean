module

public import ThomGame.Analysis.IntegerRootGraphTriangles

/-! Claim 5.7(a), with the actual directed edges and their half-sum normalization. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis.IntegerRootGraph

open Compressor IntegralShear ThomGame.IntegerRootGraph
open scoped BigOperators

theorem sum_across_reindex {A : Type*} [AddCommMonoid A] (f : Root → A) :
    ∑ r : Root, f (across r) = ∑ r : Root, f r := sum_neighbors_reindex f 0

theorem sum_right_reindex {A : Type*} [AddCommMonoid A] (f : Root → A) :
    ∑ r : Root, f (right r) = ∑ r : Root, f r := sum_neighbors_reindex f 1

theorem four_nonneg_two_le_sum (v : Fin 4 → ℝ) (hv : ∀ i, 0 ≤ v i) (i j : Fin 4) (hij : i ≠ j) :
    v i + v j ≤ ∑ k : Fin 4, v k := by
  have h := Finset.sum_le_sum_of_subset_of_nonneg
    (show ({i, j} : Finset (Fin 4)) ⊆ Finset.univ from Finset.subset_univ _)
    (fun k _ _ => hv k)
  simpa only [Finset.sum_pair hij] using h

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem edgeDifference_reverse (f : VertexHilbert H) (r : Root) (i : Fin 4) :
    edgeDifference (neighbor r i) (reverseIndex i) f = -edgeDifference r i f := by
  rw [edgeDifference_apply, neighbor_reverse, edgeDifference_apply, neg_sub]

theorem triangle_total_energy (f : VertexHilbert H) :
    (∑ r : Root, (‖f r - f (across r)‖ ^ 2 + ‖f (across r) - f (right r)‖ ^ 2 +
      2 * ‖f r - f (right r)‖ ^ 2)) = 2 * edgeEnergy f := by
  have h3 : (∑ r : Root, ‖f (across r) - f (right r)‖ ^ 2) =
      ∑ r : Root, ‖edgeDifference r 3 f‖ ^ 2 := by
    calc
      _ = ∑ r : Root, ‖edgeDifference (across r) 3 f‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro r _
        rw [edgeDifference_apply,
          (show ∀ s : Root, neighbor (across s) 3 = right s from by decide +kernel) r]
      _ = _ := sum_across_reindex (fun r => ‖edgeDifference r 3 f‖ ^ 2)
  have h2 : (∑ r : Root, ‖edgeDifference r 2 f‖ ^ 2) =
      ∑ r : Root, ‖f r - f (right r)‖ ^ 2 := by
    calc
      _ = ∑ r : Root, ‖edgeDifference (neighbor r 1) (reverseIndex 1) f‖ ^ 2 :=
        (sum_neighbors_reindex (fun r => ‖edgeDifference r 2 f‖ ^ 2) 1).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro r _
        rw [edgeDifference_reverse, norm_neg]
        rfl
  have hsum : (∑ r : Root, ∑ i : Fin 4, ‖edgeDifference r i f‖ ^ 2) =
      (∑ r : Root, ‖f r - f (across r)‖ ^ 2) +
      (∑ r : Root, ‖f r - f (right r)‖ ^ 2) +
      (∑ r : Root, ‖edgeDifference r 2 f‖ ^ 2) +
      (∑ r : Root, ‖edgeDifference r 3 f‖ ^ 2) := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Finset.sum_add_distrib, add_assoc]
    rfl
  change _ = 2 * ((1 / 2 : ℝ) * ∑ r : Root, ∑ i : Fin 4, ‖edgeDifference r i f‖ ^ 2)
  rw [hsum, h2, ← h3]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

variable [CompleteSpace H]

theorem triangle_vertex_energy_le (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (f : VertexHilbert H) :
    (∑ r : Root,
      (‖(vertexInvariants ρ (across r)).starProjection (f r - f (across r))‖ ^ 2 +
      ‖(vertexInvariants ρ (across r)).starProjection (f (across r) - f (right r))‖ ^ 2)) ≤
      2 * vertexEdgeEnergy ρ f := by
  let V : Root → Fin 4 → ℝ := fun r i => ‖(vertexInvariants ρ r).starProjection (edgeDifference r i f)‖ ^ 2
  have heq (r : Root) :
      ‖(vertexInvariants ρ (across r)).starProjection (f r - f (across r))‖ ^ 2 +
      ‖(vertexInvariants ρ (across r)).starProjection (f (across r) - f (right r))‖ ^ 2 =
      V (across r) 0 + V (across r) 3 := by
    have h0 : edgeDifference (across r) 0 f = -(f r - f (across r)) := by
      rw [edgeDifference_apply]
      change f (across r) - f (across (across r)) = _
      rw [(show ∀ s : Root, across (across s) = s from by decide +kernel) r, neg_sub]
    have h3 : edgeDifference (across r) 3 f = f (across r) - f (right r) := by
      rw [edgeDifference_apply,
        (show ∀ s : Root, neighbor (across s) 3 = right s from by decide +kernel) r]
    simp only [V, h0, h3, map_neg, norm_neg]
  calc
    _ = ∑ r : Root, (V (across r) 0 + V (across r) 3) := Finset.sum_congr rfl (fun r _ => heq r)
    _ = ∑ r : Root, (V r 0 + V r 3) := sum_across_reindex (fun r => V r 0 + V r 3)
    _ ≤ ∑ r : Root, ∑ i : Fin 4, V r i := by
      apply Finset.sum_le_sum
      intro r _
      exact four_nonneg_two_le_sum (V r) (fun _ => sq_nonneg _) 0 3 (by decide)
    _ = 2 * vertexEdgeEnergy ρ f := by unfold vertexEdgeEnergy V; ring

theorem triangle_root_energy_le (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (f : VertexHilbert H) :
    (∑ r : Root,
      (‖(unitaryFixedSpace (ρ (of (right r))))ᗮ.starProjection (f r - f (right r))‖ ^ 2 +
      ‖(unitaryFixedSpace (ρ (of r)))ᗮ.starProjection (f r - f (right r))‖ ^ 2)) ≤
      2 * rootEdgeEnergy ρ f := by
  let R : Root → Fin 4 → ℝ := fun r i =>
    ‖(unitaryFixedSpace (ρ (of r)))ᗮ.starProjection (edgeDifference r i f)‖ ^ 2
  have heq (r : Root) :
      ‖(unitaryFixedSpace (ρ (of (right r))))ᗮ.starProjection (f r - f (right r))‖ ^ 2 =
      R (right r) 2 := by
    have hr : edgeDifference (right r) 2 f = -(f r - f (right r)) := edgeDifference_reverse f r 1
    simp only [R, hr, map_neg, norm_neg]
  calc
    _ = ∑ r : Root, (R (right r) 2 + R r 1) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [heq]
      rfl
    _ = ∑ r : Root, (R r 2 + R r 1) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_right_reindex (fun r => R r 2)]
    _ ≤ ∑ r : Root, ∑ i : Fin 4, R r i := by
      apply Finset.sum_le_sum
      intro r _
      exact four_nonneg_two_le_sum (R r) (fun _ => sq_nonneg _) 2 1 (by decide)
    _ = 2 * rootEdgeEnergy ρ f := by unfold rootEdgeEnergy R; ring

theorem technical_energy_bound (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (f : VertexHilbert H)
    (hf : f ∈ decompositionSpace ρ) :
    edgeEnergy f ≤ 3 * rootEdgeEnergy ρ f + 5 * vertexEdgeEnergy ρ f := by
  have h := Finset.sum_le_sum (fun (r : Root) (_ : r ∈ Finset.univ) => root_triangle_energy ρ f hf r)
  rw [triangle_total_energy, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h
  have hv := triangle_vertex_energy_le ρ f
  have hr := triangle_root_energy_le ρ f
  linarith

end ThomGame.Analysis.IntegerRootGraph
