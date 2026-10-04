module

public import ThomGame.Analysis.MatrixRectangularUnitaryAction
public import ThomGame.Analysis.HilbertInvariantConvexHull

/-!
# Actual rectangular averaging into exact intertwiners

The fixed point in the closed convex unitary orbit is constructed in
the trace Hilbert space. Every uniform orbit-distance bound survives.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped Matrix.Norms.L2Operator

variable {d m : Nat} {B : StarSubalgebra ℂ (CMatrix d)}

theorem exists_matrixRectangular_average (r : Nat) [NeZero r]
    (ρ : B →⋆ₐ[ℂ] CMatrix m) (X V : Matrix (Fin m) (Fin d) ℂ) (c : ℝ)
    (hbound : ∀ U : unitary B, rectHSNorm r (matrixRectangularUnitaryAction ρ U X - V) ≤ c) :
    ∃ Y ∈ closedConvexHull ℝ (Set.range (fun U : unitary B => matrixRectangularUnitaryAction ρ U X)),
      (∀ b : B, ρ b * Y = Y * (b : CMatrix d)) ∧ rectHSNorm r (Y - V) ≤ c := by
  let : InnerProductSpace ℝ (FiniteRectMatrixHilbert r m d) := InnerProductSpace.rclikeToReal ℂ _
  let : CompleteSpace (FiniteRectMatrixHilbert r m d) := FiniteDimensional.complete ℂ _
  let : FiniteDimensional ℝ (FiniteRectMatrixHilbert r m d) := Module.Finite.trans (R := ℝ) ℂ _
  let H := finiteRectMatrixHilbertEquiv r m d
  let T (U : unitary B) : FiniteRectMatrixHilbert r m d →L[ℝ] FiniteRectMatrixHilbert r m d :=
    (matrixRectangularUnitaryActionHilbert r ρ U).toContinuousLinearMap.restrictScalars ℝ
  let O := Set.range (fun U : unitary B => T U (H X))
  have hinv (U : unitary B) : Set.MapsTo (T U) O O := by
    rintro z ⟨W, rfl⟩
    refine ⟨U * W, ?_⟩
    change H (matrixRectangularUnitaryAction ρ (U * W) X) =
      H (matrixRectangularUnitaryAction ρ U (matrixRectangularUnitaryAction ρ W X))
    rw [matrixRectangularUnitaryAction_mul]
  have hn (U : unitary B) (z : FiniteRectMatrixHilbert r m d) : ‖T U z‖ = ‖z‖ :=
    (matrixRectangularUnitaryActionHilbert r ρ U).norm_map z
  have hb : ∀ z ∈ O, ‖z - H V‖ ≤ c := by
    rintro z ⟨U, rfl⟩
    change ‖H (matrixRectangularUnitaryAction ρ U X) - H V‖ ≤ c
    rw [← map_sub]
    exact (finiteRectMatrixHilbert_norm r m d _).trans_le (hbound U)
  obtain ⟨y, hy, hfix, hdist⟩ := exists_fixed_near_of_invariant_set T O
    ⟨T 1 (H X), ⟨1, rfl⟩⟩ hinv hn (H V) c hb
  let Y := H.symm y
  let O' := Set.range (fun U : unitary B => matrixRectangularUnitaryAction ρ U X)
  let K : FiniteRectMatrixHilbert r m d →L[ℝ] Matrix (Fin m) (Fin d) ℂ :=
    (H.symm.toLinearMap.restrictScalars ℝ).toContinuousLinearMap
  have hsub : closedConvexHull ℝ O ⊆ K ⁻¹' closedConvexHull ℝ O' := by
    apply closedConvexHull_min
    · rintro z ⟨U, rfl⟩
      change matrixRectangularUnitaryAction ρ U X ∈ closedConvexHull ℝ O'
      exact subset_closedConvexHull ⟨U, rfl⟩
    · exact convex_closedConvexHull.linear_preimage K.toLinearMap
    · exact isClosed_closedConvexHull.preimage K.continuous
  refine ⟨Y, hsub hy, ?_, ?_⟩
  · apply matrixRectangular_intertwines_of_unitaries ρ Y
    intro U
    have he := congrArg H.symm (hfix U)
    change ρ U.val * Y * (U.val : CMatrix d)ᴴ = Y at he
    have hu : (U.val : CMatrix d)ᴴ * (U.val : CMatrix d) = 1 :=
      (matrixSubalgebraUnitary B U).prop.1
    have hm := congrArg (fun Z : Matrix (Fin m) (Fin d) ℂ => Z * (U.val : CMatrix d)) he
    simpa only [Matrix.mul_assoc, hu, Matrix.mul_one] using hm
  · rw [← finiteRectMatrixHilbert_norm r m d, map_sub]
    change ‖H (H.symm y) - H V‖ ≤ c
    rwa [H.apply_symm_apply]

end ThomGame.Analysis
