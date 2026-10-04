module

public import ThomGame.Analysis.FiniteNoDriftStabilization

/-! The finite no-drift estimate forces the obstruction commutator to be close to one. -/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d]

theorem finiteNoDrift_distance_transfer (A₀ A : StarSubalgebra ℂ (CMatrix d))
    (X : CMatrix d) (hX : matrixOpNorm X ≤ 1) {α r : ℝ}
    (hXA : hsNorm (X - matrixTraceProjection A₀ X) ≤ α)
    (hA : MatrixNearInclusion A₀ A r) : hsNorm (X - matrixTraceProjection A X) ≤ α + r := by
  obtain ⟨Y, hYA, he⟩ := hA (matrixTraceProjection A₀ X) (matrixTraceProjection_mem A₀ X)
    ((matrixTraceProjection_matrixOpNorm_le A₀ X).trans hX)
  have ht := rectHSNorm_sub_triangle d X (matrixTraceProjection A₀ X) Y
  change hsNorm (X - Y) ≤ hsNorm (X - matrixTraceProjection A₀ X) +
    hsNorm (matrixTraceProjection A₀ X - Y) at ht
  exact (matrixTraceProjection_bestApproximation A X Y hYA).trans (ht.trans (add_le_add hXA he))

theorem finiteNoDriftFrame_distance {n : Nat} [NeZero n]
    (F : Matrix (Fin n) (Fin d) ℂ) (hF : Fᴴ * F = 1) (hdn : d ≤ n)
    (A : StarSubalgebra ℂ (CMatrix d)) (X : CMatrix d) (c : ℂ) :
    hsNorm (finiteNoDriftFrameValue F X c - matrixTraceProjection (matrixFrameScalarAlgebra A F hF)
      (finiteNoDriftFrameValue F X c)) ≤ hsNorm (X - matrixTraceProjection A X) := by
  have hY : finiteNoDriftFrameValue F (matrixTraceProjection A X) c ∈ matrixFrameScalarAlgebra A F hF :=
    (mem_matrixFrameScalarAlgebra A F hF _).mpr ⟨_, matrixTraceProjection_mem A X, c, rfl⟩
  have hb := matrixTraceProjection_bestApproximation (matrixFrameScalarAlgebra A F hF)
    (finiteNoDriftFrameValue F X c) _ hY
  rw [finiteNoDriftFrameValue_sub] at hb
  exact hb.trans (finiteNoDriftFrame_hsNorm_le F hF (NeZero.pos d) hdn _)

theorem finiteNoDrift_conjugate_reverse (A : StarSubalgebra ℂ (CMatrix d))
    (U : UnitaryMatrix d) {ε : ℝ}
    (hrev : MatrixNearInclusion A (matrixUnitaryPullbackAlgebra A U) ε)
    (X : CMatrix d) (hXA : X ∈ A) (hX : matrixOpNorm X ≤ 1) :
    ∃ Y ∈ A, matrixOpNorm Y ≤ 1 ∧ hsNorm (U.val * X * U.valᴴ - Y) ≤ ε := by
  obtain ⟨Z, hZA, hZn, he⟩ := matrixNearInclusion_contraction _ _ hrev X hXA hX
  let Y := (matrixUnitaryPullbackEquiv A U ⟨Z, hZA⟩ : CMatrix d)
  have hY : Y = U.val * Z * U.valᴴ := matrixUnitaryPullbackEquiv_coe A U ⟨Z, hZA⟩
  refine ⟨Y, (matrixUnitaryPullbackEquiv A U ⟨Z, hZA⟩).property, ?_, ?_⟩
  · rw [hY]
    have hn := finiteNoDrift_conjugation_contract U⁻¹ Z hZn
    change matrixOpNorm (U.valᴴᴴ * Z * U.valᴴ) ≤ 1 at hn
    simpa only [Matrix.conjTranspose_conjTranspose] using hn
  · rw [hY, ← sub_mul, ← mul_sub]
    change hsNorm (U.val * (X - Z) * (U⁻¹).val) ≤ ε
    rw [hsNorm_mul_unitary, hsNorm_unitary_mul]
    exact he

theorem finiteNoDrift_conjugate_point (A : StarSubalgebra ℂ (CMatrix d))
    (U T : UnitaryMatrix d) (C : CMatrix d) (hCn : matrixOpNorm C ≤ 1)
    {α ε ζ : ℝ} (hC : hsNorm (C - matrixTraceProjection A C) ≤ α)
    (hrev : MatrixNearInclusion A (matrixUnitaryPullbackAlgebra A U) ε)
    (hUT : hsNorm (T.val - U.val) ≤ ζ) :
    ∃ Y ∈ A, matrixOpNorm Y ≤ 1 ∧ hsNorm (T.val * C * T.valᴴ - Y) ≤ α + ε + 2 * ζ := by
  obtain ⟨Y, hYA, hYn, hYe⟩ := finiteNoDrift_conjugate_reverse A U hrev
    (matrixTraceProjection A C) (matrixTraceProjection_mem A C)
    ((matrixTraceProjection_matrixOpNorm_le A C).trans hCn)
  have h₁ : hsNorm (U.val * C * U.valᴴ - U.val * matrixTraceProjection A C * U.valᴴ) ≤ α := by
    rw [← sub_mul, ← mul_sub]
    change hsNorm (U.val * (C - matrixTraceProjection A C) * (U⁻¹).val) ≤ α
    rw [hsNorm_mul_unitary, hsNorm_unitary_mul]
    exact hC
  have h₂ := finiteNoDrift_conjugation_lipschitz T⁻¹ U⁻¹ C hCn
  change hsNorm (T.valᴴᴴ * C * T.valᴴ - U.valᴴᴴ * C * U.valᴴ) ≤ 2 * hsNorm (T.valᴴ - U.valᴴ) at h₂
  rw [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose,
    ← Matrix.conjTranspose_sub, hsNorm_conjTranspose] at h₂
  have ht := rectHSNorm_sub_triangle_three d (T.val * C * T.valᴴ) (U.val * C * U.valᴴ)
    (U.val * matrixTraceProjection A C * U.valᴴ) Y
  change hsNorm _ ≤ hsNorm _ + hsNorm _ + hsNorm _ at ht
  refine ⟨Y, hYA, hYn, ?_⟩
  linarith

theorem finiteNoDrift_obstruction_commutator (A : StarSubalgebra ℂ (CMatrix d))
    (U T H : UnitaryMatrix d) (C : CMatrix d) (hCn : matrixOpNorm C ≤ 1)
    {α ε θ ζ : ℝ} (hC : hsNorm (C - matrixTraceProjection A C) ≤ α)
    (hrev : MatrixNearInclusion A (matrixUnitaryPullbackAlgebra A U) ε)
    (hUT : hsNorm (T.val - U.val) ≤ ζ)
    (hH : ∀ X, X ∈ A → matrixOpNorm X ≤ 1 → hsNorm (X * H.val - H.val * X) ≤ θ) :
    hsNorm ((T.val * C * T.valᴴ) * H.val - H.val * (T.val * C * T.valᴴ)) ≤
      2 * α + 2 * ε + θ + 4 * ζ := by
  obtain ⟨Y, hYA, hYn, he⟩ := finiteNoDrift_conjugate_point A U T C hCn hC hrev hUT
  have hl := finiteNoDrift_commutator_lipschitz H (T.val * C * T.valᴴ) Y
  have hh := hH Y hYA hYn
  linarith

theorem finiteNoDrift_unitary_commutator_norm (U V : UnitaryMatrix d) :
    hsNorm ((U * V * U⁻¹ * V⁻¹).val - 1) = hsNorm (U.val * V.val - V.val * U.val) := by
  have hu : U.val * U.valᴴ = 1 := U.prop.2
  have hv : V.val * V.valᴴ = 1 := V.prop.2
  have he : (U.val * V.val - V.val * U.val) * U.valᴴ * V.valᴴ =
      (U * V * U⁻¹ * V⁻¹).val - 1 := by
    change (U.val * V.val - V.val * U.val) * U.valᴴ * V.valᴴ =
      U.val * V.val * U.valᴴ * V.valᴴ - 1
    rw [sub_mul, sub_mul]
    have hc : V.val * U.val * U.valᴴ * V.valᴴ = 1 := by
      rw [mul_assoc V.val U.val U.valᴴ, hu, mul_one, hv]
    rw [hc]
  rw [← he]
  change hsNorm ((U.val * V.val - V.val * U.val) * (U⁻¹).val * (V⁻¹).val) = _
  rw [hsNorm_mul_unitary, hsNorm_mul_unitary]

theorem finiteNoDrift_obstruction_word (A : StarSubalgebra ℂ (CMatrix d))
    (U T V H : UnitaryMatrix d) {α ε θ ζ : ℝ}
    (hC : hsNorm ((T⁻¹ * V).val - matrixTraceProjection A (T⁻¹ * V).val) ≤ α)
    (hrev : MatrixNearInclusion A (matrixUnitaryPullbackAlgebra A U) ε)
    (hUT : hsNorm (T.val - U.val) ≤ ζ)
    (hH : ∀ X, X ∈ A → matrixOpNorm X ≤ 1 → hsNorm (X * H.val - H.val * X) ≤ θ) :
    hsNorm ((H * (V * T⁻¹) * H⁻¹ * (V * T⁻¹)⁻¹).val - 1) ≤
      2 * α + 2 * ε + θ + 4 * ζ := by
  have he : T.val * (T⁻¹ * V).val * T.valᴴ = (V * T⁻¹).val := by
    change T.val * (T.valᴴ * V.val) * T.valᴴ = V.val * T.valᴴ
    rw [← mul_assoc T.val T.valᴴ V.val, show T.val * T.valᴴ = 1 from T.prop.2, one_mul]
  have hb := finiteNoDrift_obstruction_commutator A U T H (T⁻¹ * V).val
    (matrixOpNorm_unitary_le _) hC hrev hUT hH
  rw [he, hsNorm_sub_comm] at hb
  rw [finiteNoDrift_unitary_commutator_norm]
  exact hb

end ThomGame.Analysis
