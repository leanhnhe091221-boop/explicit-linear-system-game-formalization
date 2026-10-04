module

public import ThomGame.Analysis.MatrixResolventFamilyEnergy
public import ThomGame.Analysis.MatrixResolventRoundingThreshold

/-!
# Small-energy projection families with improved coverage

The input energy controls the actual resolvent differences. The common
spectral threshold therefore gives every conclusion of ALT Lemma 3.3,
with explicit energy constant 100. The complementary low cut is open
at gamma, so the proved coverage bound is stronger at that endpoint.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

theorem resolvent_rounding_small_energy {γ E : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hE : E ≤ 9376 * γ ^ 8) : Real.sqrt (E / (2 * γ)) / γ ≤ 100 * γ ^ 2 := by
  apply (div_le_iff₀ hγ).mpr
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  apply (div_le_iff₀ (show 0 < 2 * γ by positivity)).mpr
  have hp : γ ^ 8 ≤ γ ^ 7 := by
    calc
      _ = γ ^ 7 * γ := by ring
      _ ≤ γ ^ 7 * 1 := mul_le_mul_of_nonneg_left hγ1 (pow_nonneg hγ.le 7)
      _ = _ := mul_one _
  calc
    E ≤ 9376 * γ ^ 8 := hE
    _ ≤ 9376 * γ ^ 7 := mul_le_mul_of_nonneg_left hp (by norm_num)
    _ ≤ _ := by nlinarith [pow_nonneg hγ.le 7]

variable {d h : Nat} [NeZero d] [NeZero h]

omit [NeZero h] in
theorem matrixResolventDifferenceFamily_energy_gamma_le {γ : ℝ} {P : CMatrix d}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hP : IsStarProjection P)
    (F : Nat → CMatrix d) (hF : ∀ i, IsStarProjection (F i)) (U : Fin h → UnitaryMatrix d) (n : Nat)
    (henergy : matrixCoordinateEnergy U P + (∑ i ∈ Finset.range n, matrixCoordinateEnergy U (F i)) ≤ γ ^ 16) :
    (∑ i : Fin n, matrixCoordinateEnergy U (matrixResolventDifferenceFamily (γ ^ 2) P F i)) ≤ 9376 * γ ^ 8 := by
  have hlam1 : γ ^ 2 ≤ 1 := by nlinarith
  have he := matrixResolventDifferenceFamily_energy_fin_sum_le (sq_pos_of_pos hγ) hlam1 hP F hF U n
  have hc : (9376 / (γ ^ 2) ^ 4) * γ ^ 16 = 9376 * γ ^ 8 := by field_simp
  exact (he.trans (mul_le_mul_of_nonneg_left henergy (by positivity))).trans_eq hc

theorem exists_matrixResolventSmallEnergyRounding {γ : ℝ} {P : CMatrix d}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hP : IsStarProjection P)
    (F : Nat → CMatrix d) (hF : ∀ i, IsStarProjection (F i)) (U : Fin h → UnitaryMatrix d) (n : Nat)
    (htrace : (normalizedTrace P).re + (∑ i ∈ Finset.range n, (normalizedTrace (F i)).re) ≤ 3)
    (henergy : matrixCoordinateEnergy U P + (∑ i ∈ Finset.range n, matrixCoordinateEnergy U (F i)) ≤ γ ^ 16) :
    ∃ s ∈ Set.Icc γ (2 * γ),
      (∀ i : Fin n, IsStarProjection (matrixResolventSpectralProjection (γ ^ 2) P F s i) ∧
        (matrixResolventSpectralProjection (γ ^ 2) P F s i).rank ≤ (F i).rank) ∧
      (∑ i : Fin n, matrixCoordinateEnergy U (matrixResolventSpectralProjection (γ ^ 2) P F s i)) ≤ 100 * γ ^ 2 ∧
      (∑ i : Fin n, (normalizedTrace (matrixProjectionPartialSum P F i ^ 2 *
        matrixResolventSpectralProjection (γ ^ 2) P F s i)).re) ≤ 3 * γ ∧
      matrixFamilyCoverageDefect (fun i : Fin n => matrixResolventSpectralProjection (γ ^ 2) P F s i) ≤
        (normalizedTrace P).re + (normalizedTrace
          (1 - matrixSpectralCut (matrixProjectionPartialSum P F n) γ)).re + 7 * γ := by
  have hP0 : 0 ≤ (normalizedTrace P).re := (Complex.nonneg_iff.mp (normalizedTrace_nonneg P hP.nonneg)).1
  have ht : (∑ i ∈ Finset.range n, (normalizedTrace (F i)).re) ≤ 3 := by linarith
  obtain ⟨s, hs, hp, hw, hc, he⟩ := exists_matrixResolventSpectralRounding hγ hP F hF n ht U
  have hD := matrixResolventDifferenceFamily_energy_gamma_le hγ hγ1 hP F hF U n henergy
  exact ⟨s, hs, hp, he.trans (resolvent_rounding_small_energy hγ hγ1 hD), hw, hc⟩

theorem exists_matrixProjectionFamily_small_energy_coverage {γ : ℝ} {e : CMatrix d}
    (hγ : 0 < γ) (hγ4 : γ ≤ 1 / 4) (he : IsStarProjection e)
    (F : Nat → CMatrix d) (hF : ∀ i, IsStarProjection (F i)) (U : Fin h → UnitaryMatrix d) (n : Nat)
    (htrace : (normalizedTrace (1 - e)).re + (∑ i ∈ Finset.range n, (normalizedTrace (F i)).re) ≤ 3)
    (henergy : matrixCoordinateEnergy U (1 - e) + (∑ i ∈ Finset.range n, matrixCoordinateEnergy U (F i)) ≤ γ ^ 16) :
    ∃ Q : Fin n → CMatrix d,
      (∀ i, IsStarProjection (Q i) ∧ (Q i).rank ≤ (F i).rank) ∧
      (∑ i, matrixCoordinateEnergy U (Q i)) ≤ 100 * γ ^ 2 ∧
      (∑ i : Fin n, (normalizedTrace (matrixProjectionPartialSum (1 - e) F i ^ 2 * Q i)).re) ≤ 3 * γ ∧
      matrixFamilyCoverageDefect Q ≤ (normalizedTrace (1 - e)).re +
        (normalizedTrace (1 - matrixSpectralCut (matrixProjectionPartialSum (1 - e) F n) γ)).re + 7 * γ := by
  obtain ⟨s, _, hp, hq, hw, hc⟩ := exists_matrixResolventSmallEnergyRounding hγ (by linarith)
    he.one_sub F hF U n htrace henergy
  exact ⟨fun i => matrixResolventSpectralProjection (γ ^ 2) (1 - e) F s i, hp, hq, hw, hc⟩

end ThomGame.Analysis
