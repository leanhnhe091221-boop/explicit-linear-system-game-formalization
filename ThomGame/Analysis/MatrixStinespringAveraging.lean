module

public import ThomGame.Analysis.MatrixRelativeStinespring
public import ThomGame.Analysis.MatrixCommutantProjectionRounding

/-!
# Thom's orbit overlap bound from the original near inclusion

Unitaries of the represented algebra are lifted to actual unitaries
of B. Their compressed overlap is exactly ||E_A(u)|| squared, so the
averaging hypothesis follows from B being nearly contained in A.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d m : Nat}

theorem exists_matrixImage_unitary_preimage
    (ρ : CMatrix d →⋆ₐ[ℂ] CMatrix m) (hρ : Function.Injective ρ)
    (B : StarSubalgebra ℂ (CMatrix d)) (U : unitary (B.map ρ)) :
    ∃ u : unitary B, ρ (matrixSubalgebraUnitary B u).val = (matrixSubalgebraUnitary (B.map ρ) U).val := by
  have hu : ∃ X ∈ B, ρ X = (matrixSubalgebraUnitary (B.map ρ) U).val := U.val.property
  obtain ⟨X, hXB, hX⟩ := hu
  have hi : star X * X = 1 := by
    apply hρ
    rw [map_mul, map_star, map_one, hX]
    exact (matrixSubalgebraUnitary (B.map ρ) U).prop.1
  have hf : X * star X = 1 := by
    apply hρ
    rw [map_mul, map_star, map_one, hX]
    exact (matrixSubalgebraUnitary (B.map ρ) U).prop.2
  let u : unitary B := ⟨⟨X, hXB⟩, ⟨Subtype.ext hi, Subtype.ext hf⟩⟩
  exact ⟨u, hX⟩

theorem matrixStinespring_range_overlap (r : Nat) (V : Matrix (Fin m) (Fin d) ℂ)
    (R : CMatrix m) :
    matrixTraceReal r ((V * Vᴴ) * (R * (V * Vᴴ) * star R)) =
      rectHSNorm r (Vᴴ * R * V) ^ 2 := by
  let F := Vᴴ * R * V
  have ha : Fᴴ = Vᴴ * Rᴴ * V := by
    simp only [F, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  calc
    _ = matrixTraceReal r (V * (F * Vᴴ * Rᴴ)) := by
      congr 1
      simp only [F, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
    _ = matrixTraceReal r ((F * Vᴴ * Rᴴ) * V) := matrixTraceReal_mul_comm r _ _
    _ = matrixTraceReal r (F * Fᴴ) := by rw [ha]; simp only [Matrix.mul_assoc]
    _ = matrixTraceReal r (Fᴴ * F) := matrixTraceReal_mul_comm r _ _
    _ = _ := matrixTraceReal_gram r F

variable [NeZero d] [NeZero m]

theorem matrixTraceProjection_unitary_pythagoras (A : StarSubalgebra ℂ (CMatrix d))
    (U : UnitaryMatrix d) :
    hsNorm (U.val - matrixTraceProjection A U.val) ^ 2 = 1 - hsNorm (matrixTraceProjection A U.val) ^ 2 := by
  have hcross : normalizedTrace (star U.val * matrixTraceProjection A U.val) =
      normalizedTrace (star (matrixTraceProjection A U.val) * matrixTraceProjection A U.val) := by
    rw [← matrixTraceProjection_trace A (star U.val * matrixTraceProjection A U.val),
      matrixTraceProjection_mul_right A _ _ (matrixTraceProjection_mem A U.val), matrixTraceProjection_star]
  have hnorm : hsNorm U.val ^ 2 = 1 := by
    have he := normalizedTrace_gram U.val
    rw [U.prop.1, normalizedTrace_one] at he
    exact_mod_cast he.symm
  rw [hsNorm_sub_sq, hnorm, hcross, normalizedTrace_gram, Complex.ofReal_re]
  ring

omit [NeZero m] in
theorem matrixStinespring_nearInclusion_orbit_overlap
    (A B : StarSubalgebra ℂ (CMatrix d)) {ε : ℝ} (hε : 0 ≤ ε)
    (hBA : MatrixNearInclusion B A ε)
    (ρ : CMatrix d →⋆ₐ[ℂ] CMatrix m) (hρ : Function.Injective ρ)
    (V : Matrix (Fin m) (Fin d) ℂ) (hV : Vᴴ * V = 1)
    (hE : ∀ X, Vᴴ * ρ X * V = matrixTraceProjection A X)
    (U : unitary (B.map ρ)) :
    matrixTraceReal d (V * Vᴴ) - ε ^ 2 ≤
      matrixTraceReal d ((V * Vᴴ) * matrixUnitaryConjugation (matrixSubalgebraUnitary (B.map ρ) U) (V * Vᴴ)) := by
  obtain ⟨u, hu⟩ := exists_matrixImage_unitary_preimage ρ hρ B U
  let X := matrixSubalgebraUnitary B u
  have hnorm : matrixOpNorm X.val ≤ 1 := by
    exact le_of_eq (CStarRing.norm_coe_unitary X)
  obtain ⟨Y, hYA, hY⟩ := hBA X.val u.val.property hnorm
  have hb := (matrixTraceProjection_bestApproximation A X.val Y hYA).trans hY
  have hs := (sq_le_sq₀ (hsNorm_nonneg (X.val - matrixTraceProjection A X.val)) hε).mpr hb
  rw [matrixTraceProjection_unitary_pythagoras A X] at hs
  rw [matrixStinespring_range_trace V hV, matrixUnitaryConjugation_apply,
    matrixStinespring_range_overlap, ← hu, hE, rectHSNorm_eq_hsNorm]
  linarith

theorem exists_matrixStinespring_averaged_cut
    (A B : StarSubalgebra ℂ (CMatrix d)) {ε : ℝ} (hε : 0 ≤ ε)
    (hBA : MatrixNearInclusion B A ε)
    (ρ : CMatrix d →⋆ₐ[ℂ] CMatrix m) (hρ : Function.Injective ρ)
    (V : Matrix (Fin m) (Fin d) ℂ) (hV : Vᴴ * V = 1)
    (hE : ∀ X, Vᴴ * ρ X * V = matrixTraceProjection A X) :
    ∃ h Q : CMatrix m,
      h = matrixTraceProjection (StarSubalgebra.centralizer ℂ ((B.map ρ) : Set (CMatrix m))) (V * Vᴴ) ∧
      0 ≤ h ∧ h ≤ 1 ∧ matrixTraceReal d h = 1 ∧
      matrixTraceReal d (h - h * h) = rectHSNorm d (V * Vᴴ - h) ^ 2 ∧
      rectHSNorm d (V * Vᴴ - h) ^ 2 ≤ ε ^ 2 ∧
      Q = matrixHalfProjection h ∧ IsStarProjection Q ∧
      Q ∈ StarSubalgebra.centralizer ℂ ((B.map ρ) : Set (CMatrix m)) ∧
      rectHSNorm d (V * Vᴴ - Q) ^ 2 ≤ 2 * ε ^ 2 ∧
      |matrixTraceReal d Q - 1| ≤ 2 * ε ^ 2 ∧
      ∀ X ∈ StarSubalgebra.centralizer ℂ ((B.map ρ) : Set (CMatrix m)),
        (V * Vᴴ) * X = X * (V * Vᴴ) → h * X = X * h ∧ Q * X = X * Q := by
  simpa only [matrixStinespring_range_trace V hV] using
    exists_matrixCommutant_roundedProjection d (B.map ρ) (matrixStinespring_range_projection V hV)
      (ε ^ 2) (matrixStinespring_nearInclusion_orbit_overlap A B hε hBA ρ hρ V hV hE)

end ThomGame.Analysis
