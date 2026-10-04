module

public import ThomGame.Analysis.MatrixSpectralRounding

/-!
# The spectral rounding step in projection improvement

Once a positive smoothed matrix has the two estimates in ALT (2.11),
an actual spectral cut satisfies all three conclusions of (2.8).
Obtaining (2.11) uniformly below a large projection is a separate task;
no such existence or exclusion statement is assumed here as an interface.
-/

@[expose] public section
namespace ThomGame.Analysis

open Set
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {d h : Nat} [NeZero h] {X P : CMatrix d}

theorem exists_matrixSpectralCut_thirds_energy_le (hX : X.PosSemidef)
    (U : Fin h → UnitaryMatrix d) :
    ∃ s ∈ Icc (1 / 3 : ℝ) (2 / 3), matrixCoordinateEnergy U (matrixSpectralCut X s) ≤
      6 * Real.sqrt ((normalizedTrace X).re * matrixCoordinateEnergy U X) := by
  obtain ⟨s, hs, he⟩ := exists_matrixFamilySpectralCut_energy_le
    (fun _ : Unit => X) (fun _ => hX) U (1 / 3) (2 / 3) (by norm_num) (by norm_num)
  simp only [Fintype.sum_unique] at he
  have ht : 0 ≤ (normalizedTrace X).re := (Complex.nonneg_iff.mp (normalizedTrace_nonneg X hX.nonneg)).1
  have hprod : 0 ≤ (normalizedTrace X).re * matrixCoordinateEnergy U X :=
    mul_nonneg ht (matrixCoordinateEnergy_nonneg U X)
  have hr : Real.sqrt (((normalizedTrace X).re / (2 * (1 / 3))) * matrixCoordinateEnergy U X) ≤
      2 * Real.sqrt ((normalizedTrace X).re * matrixCoordinateEnergy U X) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · norm_num
      nlinarith [Real.sq_sqrt hprod]
  refine ⟨s, hs, ?_⟩
  norm_num at he hr
  linarith

theorem exists_matrixProjection_improvement_of_estimates (hP : IsStarProjection P)
    (hX : X.PosSemidef) (U : Fin h → UnitaryMatrix d) (κ α : ℝ) (hκ : 0 < κ) (hα : 0 ≤ α)
    (ht : (normalizedTrace X).re = (normalizedTrace P).re)
    (hdist : hsNorm (X - P) ^ 2 ≤ 4 * κ⁻¹ * matrixCoordinateEnergy U P)
    (henergy : matrixCoordinateEnergy U X ≤ α ^ 2 * (normalizedTrace P).re / 36)
    (hthreshold : matrixCoordinateEnergy U P ≤ κ * (normalizedTrace P).re / 64) :
    ∃ F : CMatrix d, IsStarProjection F ∧
      hsNorm (F - P) ^ 2 ≤ 36 * κ⁻¹ * matrixCoordinateEnergy U P ∧
      (1 / 3 : ℝ) * (normalizedTrace P).re ≤ (normalizedTrace F).re ∧
      (normalizedTrace F).re ≤ (5 / 3 : ℝ) * (normalizedTrace P).re ∧
      matrixCoordinateEnergy U F ≤ α * (normalizedTrace P).re := by
  obtain ⟨s, hs, he⟩ := exists_matrixSpectralCut_thirds_energy_le hX U
  let F := matrixSpectralCut X s
  have hF : IsStarProjection F := matrixSpectralCut_isStarProjection hX.isHermitian s
  have htP : 0 ≤ (normalizedTrace P).re :=
    (Complex.nonneg_iff.mp (normalizedTrace_nonneg P hP.nonneg)).1
  have hd : hsNorm (F - P) ^ 2 ≤ 36 * κ⁻¹ * matrixCoordinateEnergy U P := by
    calc
      _ ≤ 9 * hsNorm (X - P) ^ 2 := matrixSpectralCut_distance_le hX.isHermitian hP s hs
      _ ≤ 9 * (4 * κ⁻¹ * matrixCoordinateEnergy U P) := mul_le_mul_of_nonneg_left hdist (by norm_num)
      _ = _ := by ring
  have hdt : hsNorm (F - P) ^ 2 ≤ (2 / 3 : ℝ) * (normalizedTrace P).re := by
    calc
      _ ≤ 36 * κ⁻¹ * matrixCoordinateEnergy U P := hd
      _ ≤ 36 * κ⁻¹ * (κ * (normalizedTrace P).re / 64) :=
        mul_le_mul_of_nonneg_left hthreshold (by positivity)
      _ = (9 / 16 : ℝ) * (normalizedTrace P).re := by
        calc
          _ = (9 / 16 : ℝ) * (κ⁻¹ * κ) * (normalizedTrace P).re := by ring
          _ = _ := by rw [inv_mul_cancel₀ hκ.ne', mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) htP
  have htrace := abs_le.mp ((matrixProjection_trace_difference_le hF hP).trans hdt)
  have hr : Real.sqrt ((normalizedTrace P).re * matrixCoordinateEnergy U X) ≤
      α * (normalizedTrace P).re / 6 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [mul_le_mul_of_nonneg_left henergy htP]
  refine ⟨F, hF, hd, ?_, ?_, ?_⟩
  · linarith [htrace.1]
  · linarith [htrace.2]
  · rw [ht] at he
    change matrixCoordinateEnergy U F ≤ _ at he
    linarith

end ThomGame.Analysis
