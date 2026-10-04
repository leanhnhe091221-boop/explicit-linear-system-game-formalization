module

public import ThomGame.Analysis.CStarContractiveLift
public import ThomGame.Analysis.MatrixSubalgebraUnitaries

/-!
# Exact unit-ball images of finite matrix star representations

No faithfulness or positive target dimension is required. Continuous
functional calculus provides a contraction preimage of every contraction
in the range, with no loss in the operator norm.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator

variable {d m : Nat} (A : StarSubalgebra ℂ (CMatrix d))

theorem matrixStarRepresentation_contraction (ρ : A →⋆ₐ[ℂ] CMatrix m)
    (X : A) (hX : matrixOpNorm (X : CMatrix d) ≤ 1) : matrixOpNorm (ρ X) ≤ 1 := by
  let : IsClosed (A : Set (CMatrix d)) := A.toSubalgebra.toSubmodule.closed_of_finiteDimensional
  have hn : ‖X‖ ≤ 1 := hX
  have he := map_cstarRightNormClamp ρ 1 (by norm_num) X
  rw [cstarRightNormClamp_eq_self 1 (by norm_num) X hn] at he
  change ‖ρ X‖ ≤ 1
  rw [he]
  exact cstarRightNormClamp_norm_le 1 (by norm_num) (ρ X)

theorem matrixStarRepresentation_contraction_lift (ρ : A →⋆ₐ[ℂ] CMatrix m)
    (Y : CMatrix m) (hY : Y ∈ ρ.range) (hn : matrixOpNorm Y ≤ 1) :
    ∃ X : A, matrixOpNorm (X : CMatrix d) ≤ 1 ∧ ρ X = Y := by
  let : IsClosed (A : Set (CMatrix d)) := A.toSubalgebra.toSubmodule.closed_of_finiteDimensional
  obtain ⟨X, rfl⟩ := hY
  exact exists_cstar_exact_norm_lift ρ X 1 (by norm_num) hn

theorem matrixStarRepresentation_unitBall_image (ρ : A →⋆ₐ[ℂ] CMatrix m) :
    ρ '' {X : A | matrixOpNorm (X : CMatrix d) ≤ 1} =
      {Y : CMatrix m | Y ∈ ρ.range ∧ matrixOpNorm Y ≤ 1} := by
  ext Y
  constructor
  · rintro ⟨X, hX, rfl⟩
    exact ⟨⟨X, rfl⟩, matrixStarRepresentation_contraction A ρ X hX⟩
  · rintro ⟨hY, hn⟩
    exact matrixStarRepresentation_contraction_lift A ρ Y hY hn

end ThomGame.Analysis
