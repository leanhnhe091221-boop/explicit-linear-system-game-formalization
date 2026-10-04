module

public import ThomGame.Analysis.FiniteNoDriftAlignment

/-! Finite extension by a scalar corner preserves the anchored estimate and its constant. -/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d n : Nat} (F : Matrix (Fin n) (Fin d) ℂ) (hF : Fᴴ * F = 1)

noncomputable def finiteNoDriftFrameValue (X : CMatrix d) (c : ℂ) : CMatrix n :=
  matrixFrameLift F X + c • (1 - F * Fᴴ)

include hF

theorem finiteNoDriftFrameValue_mul (X Y : CMatrix d) (c e : ℂ) :
    finiteNoDriftFrameValue F X c * finiteNoDriftFrameValue F Y e =
      finiteNoDriftFrameValue F (X * Y) (c * e) := by
  simp only [finiteNoDriftFrameValue, Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul,
    Matrix.smul_mul, matrixFrameLift_mul hF, matrixFrameLift_mul_complement F hF,
    matrixFrameLift_complement_mul F hF, smul_zero, add_zero, zero_add, smul_smul,
    (matrixFrame_final_projection F hF).one_sub.isIdempotentElem.eq]
  rw [mul_comm e c]

theorem finiteNoDriftFrameValue_star (X : CMatrix d) (c : ℂ) :
    (finiteNoDriftFrameValue F X c)ᴴ = finiteNoDriftFrameValue F Xᴴ (star c) := by
  change star (matrixFrameLift F X + c • (1 - F * Fᴴ)) =
    matrixFrameLift F Xᴴ + star c • (1 - F * Fᴴ)
  rw [star_add, star_smul, (matrixFrame_final_projection F hF).one_sub.isSelfAdjoint.star_eq]
  exact congrArg (fun Z : CMatrix n => Z + star c • (1 - F * Fᴴ)) (matrixFrameLift_star F X)

theorem finiteNoDriftFrameValue_compression (X : CMatrix d) (c : ℂ) :
    Fᴴ * finiteNoDriftFrameValue F X c * F = X := by
  rw [finiteNoDriftFrameValue, Matrix.mul_add, Matrix.add_mul, matrixFrameCompression_lift F hF,
    Matrix.mul_smul, matrixFrame_complement_adjoint F hF, smul_zero, Matrix.zero_mul, add_zero]

omit hF in
theorem finiteNoDriftFrameValue_sub (X Y : CMatrix d) (c : ℂ) :
    finiteNoDriftFrameValue F X c - finiteNoDriftFrameValue F Y c =
      matrixFrameLift F (X - Y) := by
  rw [finiteNoDriftFrameValue, finiteNoDriftFrameValue, matrixFrameLift_sub]
  abel

noncomputable def finiteNoDriftFrameUnitary (hF : Fᴴ * F = 1) (U : UnitaryMatrix d) : UnitaryMatrix n :=
  ⟨finiteNoDriftFrameValue F U.val 1, by
    constructor
    · change (finiteNoDriftFrameValue F U.val 1)ᴴ * finiteNoDriftFrameValue F U.val 1 = 1
      rw [finiteNoDriftFrameValue_star F hF, finiteNoDriftFrameValue_mul F hF]
      have hu : U.valᴴ * U.val = 1 := U.prop.1
      rw [hu]
      simp [finiteNoDriftFrameValue, matrixFrameLift_one]
    · change finiteNoDriftFrameValue F U.val 1 * (finiteNoDriftFrameValue F U.val 1)ᴴ = 1
      rw [finiteNoDriftFrameValue_star F hF, finiteNoDriftFrameValue_mul F hF]
      have hu : U.val * U.valᴴ = 1 := U.prop.2
      rw [hu]
      simp [finiteNoDriftFrameValue, matrixFrameLift_one]⟩

theorem finiteNoDriftFrame_commutator (U : UnitaryMatrix d) (X : CMatrix d) (c : ℂ) :
    finiteNoDriftFrameValue F X c * (finiteNoDriftFrameUnitary F hF U).val -
      (finiteNoDriftFrameUnitary F hF U).val * finiteNoDriftFrameValue F X c =
      matrixFrameLift F (X * U.val - U.val * X) := by
  change finiteNoDriftFrameValue F X c * finiteNoDriftFrameValue F U.val 1 -
    finiteNoDriftFrameValue F U.val 1 * finiteNoDriftFrameValue F X c = _
  rw [finiteNoDriftFrameValue_mul F hF, finiteNoDriftFrameValue_mul F hF,
    mul_one, one_mul, finiteNoDriftFrameValue_sub]

theorem finiteNoDriftFrame_conjugation (U : UnitaryMatrix d) (X : CMatrix d) (c : ℂ) :
    (finiteNoDriftFrameUnitary F hF U).valᴴ * finiteNoDriftFrameValue F X c *
      (finiteNoDriftFrameUnitary F hF U).val =
      finiteNoDriftFrameValue F (U.valᴴ * X * U.val) c := by
  change (finiteNoDriftFrameValue F U.val 1)ᴴ * finiteNoDriftFrameValue F X c *
    finiteNoDriftFrameValue F U.val 1 = _
  rw [finiteNoDriftFrameValue_star F hF, finiteNoDriftFrameValue_mul F hF,
    finiteNoDriftFrameValue_mul F hF]
  simp

theorem finiteNoDriftFrame_hsNorm_le (hd : 0 < d) (hdn : d ≤ n) (X : CMatrix d) :
    hsNorm (matrixFrameLift F X) ≤ hsNorm X := by
  exact (hsNorm_le_rectHSNorm_of_dimension_le hd hdn _).trans_eq
    ((matrixFrameLift_hsNorm d hF X).trans (rectHSNorm_eq_hsNorm X))

theorem finiteNoDriftFrame_commutator_bound [NeZero d] (hdn : d ≤ n)
    (D : StarSubalgebra ℂ (CMatrix d)) (U : UnitaryMatrix d) {ρ : ℝ}
    (hcomm : ∀ X, X ∈ D → matrixOpNorm X ≤ 1 → hsNorm (X * U.val - U.val * X) ≤ ρ) :
    ∀ X, X ∈ matrixFrameScalarAlgebra D F hF → matrixOpNorm X ≤ 1 →
      hsNorm (X * (finiteNoDriftFrameUnitary F hF U).val -
        (finiteNoDriftFrameUnitary F hF U).val * X) ≤ ρ := by
  intro X hXD hXn
  obtain ⟨Y, hY, c, rfl⟩ := (mem_matrixFrameScalarAlgebra D F hF X).mp hXD
  have hYn : matrixOpNorm Y ≤ 1 := by
    have hc := matrixFrameCompression_opNorm_le F hF (finiteNoDriftFrameValue F Y c)
    rw [finiteNoDriftFrameValue_compression F hF] at hc
    exact hc.trans hXn
  change hsNorm (finiteNoDriftFrameValue F Y c * (finiteNoDriftFrameUnitary F hF U).val -
    (finiteNoDriftFrameUnitary F hF U).val * finiteNoDriftFrameValue F Y c) ≤ ρ
  rw [finiteNoDriftFrame_commutator F hF]
  exact (finiteNoDriftFrame_hsNorm_le F hF (NeZero.pos d) hdn _).trans (hcomm Y hY hYn)

theorem finiteNoDriftFrame_forward [NeZero d] (hdn : d ≤ n)
    (A : StarSubalgebra ℂ (CMatrix d)) (U : UnitaryMatrix d) {η : ℝ}
    (hforward : MatrixNearInclusion (matrixUnitaryPullbackAlgebra A U) A η) :
    MatrixNearInclusion
      (matrixUnitaryPullbackAlgebra (matrixFrameScalarAlgebra A F hF) (finiteNoDriftFrameUnitary F hF U))
      (matrixFrameScalarAlgebra A F hF) η := by
  rintro X ⟨Y, hYA, rfl⟩ hXn
  obtain ⟨Z, hZA, c, rfl⟩ := (mem_matrixFrameScalarAlgebra A F hF Y).mp hYA
  change matrixOpNorm ((finiteNoDriftFrameUnitary F hF U).valᴴ * finiteNoDriftFrameValue F Z c *
    (finiteNoDriftFrameUnitary F hF U).val) ≤ 1 at hXn
  rw [finiteNoDriftFrame_conjugation F hF] at hXn
  have hn : matrixOpNorm (U.valᴴ * Z * U.val) ≤ 1 := by
    have hc := matrixFrameCompression_opNorm_le F hF (finiteNoDriftFrameValue F (U.valᴴ * Z * U.val) c)
    rw [finiteNoDriftFrameValue_compression F hF] at hc
    exact hc.trans hXn
  obtain ⟨W, hWA, he⟩ := hforward (U.valᴴ * Z * U.val) ⟨Z, hZA, rfl⟩ hn
  refine ⟨finiteNoDriftFrameValue F W c,
    (mem_matrixFrameScalarAlgebra A F hF _).mpr ⟨W, hWA, c, rfl⟩, ?_⟩
  change hsNorm ((finiteNoDriftFrameUnitary F hF U).valᴴ * finiteNoDriftFrameValue F Z c *
    (finiteNoDriftFrameUnitary F hF U).val - finiteNoDriftFrameValue F W c) ≤ η
  rw [finiteNoDriftFrame_conjugation F hF, finiteNoDriftFrameValue_sub]
  exact (finiteNoDriftFrame_hsNorm_le F hF (NeZero.pos d) hdn _).trans he

theorem finiteNoDriftFrame_anchor [NeZero d] [NeZero n] (hdn : d ≤ n)
    (A D : StarSubalgebra ℂ (CMatrix d)) {h : Nat} (U : Fin h → UnitaryMatrix d)
    {K ν : ℝ} (hν : 0 ≤ ν) (hanchor : FiniteNoDriftAnchor A D U K ν) :
    FiniteNoDriftAnchor (matrixFrameScalarAlgebra A F hF) (matrixFrameScalarAlgebra D F hF)
      (fun j => finiteNoDriftFrameUnitary F hF (U j)) K ν := by
  intro X hXA hXsa hXn r hr
  obtain ⟨Y, hYA, c, rfl⟩ := (mem_matrixFrameScalarAlgebra A F hF X).mp hXA
  have hYn : matrixOpNorm Y ≤ 1 := by
    have hc := matrixFrameCompression_opNorm_le F hF (finiteNoDriftFrameValue F Y c)
    rw [finiteNoDriftFrameValue_compression F hF] at hc
    exact hc.trans hXn
  have hYsa : IsSelfAdjoint Y := by
    have hc := congrArg (fun Z : CMatrix n => Fᴴ * Z * F) hXsa.star_eq
    have he : Fᴴ * (finiteNoDriftFrameValue F Y c)ᴴ * F = Yᴴ := by
      rw [finiteNoDriftFrameValue_star F hF, finiteNoDriftFrameValue_compression F hF]
    exact (show Yᴴ = Y by
      change Fᴴ * (finiteNoDriftFrameValue F Y c)ᴴ * F = Fᴴ * finiteNoDriftFrameValue F Y c * F at hc
      rw [he, finiteNoDriftFrameValue_compression F hF] at hc
      exact hc)
  have hYr : ∀ j, hsNorm (Y * (U j).val - (U j).val * Y) ≤ Real.sqrt ((n : ℝ) / d) * r := by
    intro j
    rw [matrixFrameLift_hsNorm_recover (NeZero.pos d) (NeZero.pos n) F hF]
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    have hrj := hr j
    change hsNorm (finiteNoDriftFrameValue F Y c * (finiteNoDriftFrameUnitary F hF (U j)).val -
      (finiteNoDriftFrameUnitary F hF (U j)).val * finiteNoDriftFrameValue F Y c) ≤ r at hrj
    simpa only [finiteNoDriftFrame_commutator F hF] using hrj
  have ha := hanchor Y hYA hYsa hYn (Real.sqrt ((n : ℝ) / d) * r) hYr
  have hZ : finiteNoDriftFrameValue F (matrixTraceProjection D Y) c ∈ matrixFrameScalarAlgebra D F hF :=
    (mem_matrixFrameScalarAlgebra D F hF _).mpr ⟨_, matrixTraceProjection_mem D Y, c, rfl⟩
  have hb := matrixTraceProjection_bestApproximation (matrixFrameScalarAlgebra D F hF)
    (finiteNoDriftFrameValue F Y c) _ hZ
  rw [finiteNoDriftFrameValue_sub, matrixFrameLift_hsNorm_rescale (NeZero.pos d) (NeZero.pos n) F hF] at hb
  have hscale : Real.sqrt ((d : ℝ) / n) * Real.sqrt ((n : ℝ) / d) = 1 := by
    rw [← Real.sqrt_mul (div_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg n))]
    have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
    have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    have he : (d : ℝ) / n * ((n : ℝ) / d) = 1 := by field_simp
    rw [he, Real.sqrt_one]
  have hsle : Real.sqrt ((d : ℝ) / n) ≤ 1 := by
    exact (Real.sqrt_le_one).mpr ((div_le_one (Nat.cast_pos.mpr (NeZero.pos n))).mpr (Nat.cast_le.mpr hdn))
  calc
    _ ≤ Real.sqrt ((d : ℝ) / n) * hsNorm (Y - matrixTraceProjection D Y) := hb
    _ ≤ Real.sqrt ((d : ℝ) / n) * (K * (Real.sqrt ((n : ℝ) / d) * r) + ν) :=
      mul_le_mul_of_nonneg_left ha (Real.sqrt_nonneg _)
    _ = K * r + Real.sqrt ((d : ℝ) / n) * ν := by
      calc
        _ = (Real.sqrt ((d : ℝ) / n) * Real.sqrt ((n : ℝ) / d)) * (K * r) +
          Real.sqrt ((d : ℝ) / n) * ν := by ring
        _ = _ := by rw [hscale, one_mul]
    _ ≤ K * r + ν := by
      have hm := mul_le_mul_of_nonneg_right hsle hν
      linarith

end ThomGame.Analysis
