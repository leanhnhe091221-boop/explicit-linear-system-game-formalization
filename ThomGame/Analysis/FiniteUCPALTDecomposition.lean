module

public import ThomGame.Analysis.FiniteUCPProjectionImprovement
public import ThomGame.Analysis.MatrixALTPrunedDecomposition

/-!
# Finite ALT decomposition from arbitrary completely positive smoothing

The contraction estimates for a trace-preserving completely positive map now
feed directly into the existing finite ALT selection and pruning proofs.
All small-parameter conditions are explicit. The smoothing map need not
commute with the tuple's Markov operator.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra

variable {d h : Nat} [NeZero d] [NeZero h]

theorem exists_finiteUCP_ALT_orthogonalSelection (U : Fin h → UnitaryMatrix d)
    (Φ : CMatrix d →CP CMatrix d)
    (htrace : ∀ X, normalizedTrace (Φ X) = normalizedTrace X)
    {κ α β η : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hα : 0 < α)
    (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hηκ : η ≤ κ / 1024)
    (hsmall : (1 + 61440 / (κ * Real.sqrt κ)) * η ≤ 1)
    (hαη : α ≤ η ^ 4) (hexp : 9 * α ≤ Real.exp (-(η ^ 4)⁻¹))
    (hcontrol : FiniteUCPDefectControl U Φ.toLinearMap κ β)
    (hβα : β ≤ α ^ 2 / 64) :
    ∃ R : CMatrix d, IsStarProjection R ∧ matrixTraceReal d (1 - R) ≤ α ∧
      Nonempty (MatrixALTOrthogonalSelection U κ α η R) := by
  obtain ⟨R, hR, htraceR, hcorrect⟩ := exists_finiteUCP_projection_improvement
    U Φ htrace κ α β hκ hκ1 hα hcontrol hβα
  have hRtrace : matrixTraceReal d (1 - R) ≤ α := by
    simpa only [normalizedTrace_re, matrixTraceReal] using htraceR
  exact ⟨R, hR, hRtrace, exists_matrixALTOrthogonalSelection U hR hκ hκ1 hα.le
    hη hη8 hηκ hsmall hαη hexp hRtrace hcorrect⟩

/-- The constructed decomposition retains the original explicit trace/edit
bounds and the scalar block gap `κ ^ 2 / 2 ^ 28`. -/
theorem exists_finiteUCP_ALT_prunedDecomposition (U : Fin h → UnitaryMatrix d)
    (Φ : CMatrix d →CP CMatrix d)
    (htrace : ∀ X, normalizedTrace (Φ X) = normalizedTrace X)
    {κ α β η : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hα : 0 < α)
    (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hηκ : η ≤ κ / 1024)
    (hsmall : (1 + 61440 / (κ * Real.sqrt κ)) * η ≤ 1)
    (hαη : α ≤ η ^ 4) (hexp : 9 * α ≤ Real.exp (-(η ^ 4)⁻¹))
    (hcontrol : FiniteUCPDefectControl U Φ.toLinearMap κ β)
    (hβα : β ≤ α ^ 2 / 64) :
    Nonempty (MatrixALTPrunedDecomposition U κ η) := by
  obtain ⟨R, hR, _, ⟨selection⟩⟩ := exists_finiteUCP_ALT_orthogonalSelection
    U Φ htrace hκ hκ1 hα hη hη8 hηκ hsmall hαη hexp hcontrol hβα
  exact exists_matrixALT_prunedDecomposition U selection hR hκ hκ1

end ThomGame.Analysis
