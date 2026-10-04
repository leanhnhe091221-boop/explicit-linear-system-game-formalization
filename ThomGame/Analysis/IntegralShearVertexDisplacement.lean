module

public import ThomGame.Analysis.IntegerRootGraphAngleGap
public import ThomGame.Analysis.IntegerHeisenbergFixedDistance
public import ThomGame.Analysis.UnitaryUniformFixedDistance
public import ThomGame.Analysis.IntegralShearRootDisplacement

/-! The six generators control the actual vertex invariant distances uniformly. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open Compressor IntegralShear ThomGame.Analysis.IntegerRootGraph
open scoped BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem integralShear_root_fixed_distance (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H))
    (ξ : H) (ε : ℝ) (hmove : ∀ s : Root, ‖ρ (of s) ξ - ξ‖ ≤ ε) (r : Root) :
    ‖ξ - (unitaryFixedSpace (ρ (of r))).starProjection ξ‖ ≤ 200 * ε := by
  apply unitaryFixedSpace_uniform_distance
  intro n
  have h := integralShear_root_uniform_displacement ρ ξ ε hmove r (n : ℤ)
  simpa only [rootElement, zpow_natCast, map_pow] using h

theorem integralShear_vertex_invariant_distance (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H))
    (ξ : H) (ε : ℝ) (hmove : ∀ s : Root, ‖ρ (of s) ξ - ξ‖ ≤ ε) (r : Root) :
    ‖ξ - (vertexInvariants ρ r).starProjection ξ‖ ≤ 600 * ε := by
  have ha : across (across r) = r := (show ∀ s : Root, across (across s) = s from by decide +kernel) r
  have hK : vertexInvariants ρ r =
      unitaryCommonFixedSpace (ρ (of (right (across r)))) (ρ (of (across r))) := by
    simpa only [ha] using vertexInvariants_across_eq_common ρ (across r)
  have hXZ : Commute (ρ (of (right (across r)))) (ρ (of (across (across r)))) :=
    (of_commute (right (across r)) (across (across r))
      ((show ∀ s : Root, separated (right (across s)) (across (across s)) from by decide +kernel) r)).map ρ
  have h := unitaryHeisenberg_common_fixed_distance
    (ρ (of (right (across r)))) (ρ (of (across r))) (ρ (of (across (across r))))
    (rootPair_unitary_heisenberg_relation ρ (across r))
    (rootPair_unitary_center_commute ρ (across r)) hXZ ξ
  simp only [← hK, ha] at h
  have hX := integralShear_root_fixed_distance ρ ξ ε hmove (right (across r))
  have hY := integralShear_root_fixed_distance ρ ξ ε hmove (across r)
  have hZ := integralShear_root_fixed_distance ρ ξ ε hmove r
  linarith

theorem integralShear_no_invariants_norm_le (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H))
    (hρ : hilbertUnitaryInvariants ρ = ⊥) (ξ : H) (ε : ℝ)
    (hmove : ∀ s : Root, ‖ρ (of s) ξ - ξ‖ ≤ ε) : ‖ξ‖ ≤ 2400 * ε := by
  have he : 0 ≤ ε := (norm_nonneg _).trans (hmove root12)
  have hgap := vertex_invariant_distances_gap ρ hρ ξ
  have hsum := Finset.sum_le_sum (fun (r : Root) (_ : r ∈ Finset.univ) =>
    pow_le_pow_left₀ (norm_nonneg _) (integralShear_vertex_invariant_distance ρ ξ ε hmove r) 2)
  simp only [Finset.sum_const, Finset.card_univ, ThomGame.IntegerRootGraph.vertex_card,
    nsmul_eq_mul, Nat.cast_ofNat] at hsum
  nlinarith [norm_nonneg ξ]

end ThomGame.Analysis
