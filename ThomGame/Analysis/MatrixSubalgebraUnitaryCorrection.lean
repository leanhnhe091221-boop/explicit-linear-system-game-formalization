module

public import ThomGame.Analysis.MatrixSubalgebraInvertibleDensity
public import ThomGame.Analysis.MatrixMarkovPoincare
public import Mathlib.Topology.Algebra.Star.Unitary

/-!
# Unitary correction inside a prescribed matrix subalgebra

Choose a closest unitary in the compact unitary group of the subalgebra.
Invertible matrices are dense in that same subalgebra; their polar
factors prove the Gram-defect estimate, with constant one, at the limit.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d]

omit [NeZero d] in
theorem matrixSubalgebra_unitaries_isCompact (A : StarSubalgebra ℂ (CMatrix d)) :
    IsCompact {U : CMatrix d | U ∈ A ∧ U ∈ unitary (CMatrix d)} := by
  apply (isCompact_closedBall (0 : CMatrix d) 1).of_isClosed_subset
    (A.toSubalgebra.toSubmodule.closed_of_finiteDimensional.inter isClosed_unitary)
  intro U hU
  simpa only [Metric.mem_closedBall, dist_zero_right, matrixOpNorm] using
    matrixOpNorm_unitary_le (⟨U, hU.2⟩ : UnitaryMatrix d)

theorem exists_matrixSubalgebraUnitary_close_of_gram (A : StarSubalgebra ℂ (CMatrix d))
    {X : CMatrix d} (hX : X ∈ A) :
    ∃ U : UnitaryMatrix d, U.val ∈ A ∧ hsNorm (X - U.val) ≤ hsNorm (Xᴴ * X - 1) := by
  have hne : ({U : CMatrix d | U ∈ A ∧ U ∈ unitary (CMatrix d)}).Nonempty :=
    ⟨1, A.one_mem, (unitary (CMatrix d)).one_mem⟩
  have hcont : Continuous (fun Y : CMatrix d => hsNorm (X - Y)) :=
    continuous_hsNorm.comp (continuous_const.sub continuous_id)
  obtain ⟨W, hW, hmin⟩ := (matrixSubalgebra_unitaries_isCompact A).exists_isMinOn hne
    hcont.continuousOn
  have hsub : {Y : CMatrix d | Y ∈ A ∧ IsUnit Y} ⊆
      {Y : CMatrix d | hsNorm (X - W) ≤ hsNorm (X - Y) + hsNorm (Yᴴ * Y - 1)} := by
    intro Y hY
    obtain ⟨V, hVA, hV⟩ := exists_matrixSubalgebraUnitary_close_of_isUnit A (X := Y) hY.1 hY.2
    calc
      hsNorm (X - W) ≤ hsNorm (X - V.val) := hmin ⟨hVA, V.property⟩
      _ ≤ hsNorm (X - Y) + hsNorm (Y - V.val) := by
        have he : X - V.val = (X - Y) + (Y - V.val) := (sub_add_sub_cancel X Y V.val).symm
        rw [he]
        exact hsNorm_add_le _ _
      _ ≤ hsNorm (X - Y) + hsNorm (Yᴴ * Y - 1) := add_le_add le_rfl hV
  have hc : IsClosed {Y : CMatrix d | hsNorm (X - W) ≤ hsNorm (X - Y) + hsNorm (Yᴴ * Y - 1)} :=
    isClosed_le continuous_const (hcont.add
      (continuous_hsNorm.comp ((continuous_star.mul continuous_id).sub continuous_const)))
  have hdist := closure_minimal hsub hc (matrixSubalgebra_mem_closure_isUnit A hX)
  exact ⟨⟨W, hW.2⟩, hW.1, by simpa only [Set.mem_ofPred_eq, sub_self, hsNorm_zero, zero_add] using hdist⟩

end ThomGame.Analysis
