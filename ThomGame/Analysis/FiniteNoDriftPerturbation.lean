module

public import ThomGame.Analysis.FiniteNoDriftReverse
public import ThomGame.Analysis.MatrixSubalgebraUnitaryCorrection
public import ThomGame.Analysis.MatrixCommutantConvexHull

/-! Quantitative correction of almost commuting unitaries and finite anchor transport. -/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d]

theorem finiteNoDrift_commutator_lipschitz (U : UnitaryMatrix d) (X Y : CMatrix d) :
    hsNorm (X * U.val - U.val * X) ≤
      hsNorm (Y * U.val - U.val * Y) + 2 * hsNorm (X - Y) := by
  have he : X * U.val - U.val * X =
      (Y * U.val - U.val * Y) + (X - Y) * U.val - U.val * (X - Y) := by noncomm_ring
  rw [he]
  have ha := hsNorm_add_le (Y * U.val - U.val * Y) ((X - Y) * U.val)
  have hb := hsNorm_add_le ((Y * U.val - U.val * Y) + (X - Y) * U.val) (-(U.val * (X - Y)))
  rw [hsNorm_mul_unitary] at ha
  rw [hsNorm_neg, hsNorm_unitary_mul] at hb
  change hsNorm ((Y * U.val - U.val * Y) + (X - Y) * U.val + -(U.val * (X - Y))) ≤ _
  linarith

theorem finiteNoDrift_commutator_unitary_lipschitz (U V : UnitaryMatrix d)
    (X : CMatrix d) (hX : matrixOpNorm X ≤ 1) :
    hsNorm (X * U.val - U.val * X) ≤
      hsNorm (X * V.val - V.val * X) + 2 * hsNorm (U.val - V.val) := by
  have he : X * U.val - U.val * X =
      (X * V.val - V.val * X) + X * (U.val - V.val) - (U.val - V.val) * X := by noncomm_ring
  have hl := (hsNorm_mul_le_left X (U.val - V.val)).trans
    (mul_le_mul_of_nonneg_right hX (hsNorm_nonneg _))
  have hr := (hsNorm_mul_le_right (U.val - V.val) X).trans
    (mul_le_mul_of_nonneg_left hX (hsNorm_nonneg _))
  have ha := hsNorm_add_le (X * V.val - V.val * X) (X * (U.val - V.val))
  have hb := hsNorm_add_le ((X * V.val - V.val * X) + X * (U.val - V.val))
    (-((U.val - V.val) * X))
  rw [hsNorm_neg] at hb
  rw [he]
  change hsNorm ((X * V.val - V.val * X) + X * (U.val - V.val) + -((U.val - V.val) * X)) ≤ _
  nlinarith

theorem finiteNoDrift_near_commutator_bound
    (D₀ D : StarSubalgebra ℂ (CMatrix d)) (U : UnitaryMatrix d) {r ρ : ℝ}
    (hnear : MatrixNearInclusion D D₀ r)
    (hcomm : ∀ X ∈ D₀, matrixOpNorm X ≤ 1 → hsNorm (X * U.val - U.val * X) ≤ ρ) :
    ∀ X ∈ D, matrixOpNorm X ≤ 1 → hsNorm (X * U.val - U.val * X) ≤ ρ + 2 * r := by
  intro X hXD hX
  obtain ⟨Y, hY, hn, hXY⟩ := matrixNearInclusion_contraction D D₀ hnear X hXD hX
  have hb := finiteNoDrift_commutator_lipschitz U X Y
  linarith [hcomm Y hY hn]

theorem finiteNoDrift_unitary_correction
    (D : StarSubalgebra ℂ (CMatrix d)) (U : UnitaryMatrix d) {ρ : ℝ}
    (hcomm : ∀ X ∈ D, matrixOpNorm X ≤ 1 → hsNorm (X * U.val - U.val * X) ≤ ρ) :
    ∃ V : UnitaryMatrix d, (∀ X ∈ D, V.val * X = X * V.val) ∧
      hsNorm (U.val - V.val) ≤ 3 * ρ := by
  let C := StarSubalgebra.centralizer ℂ (D : Set (CMatrix d))
  let X := matrixTraceProjection C U.val
  have hX : X ∈ C := matrixTraceProjection_mem C U.val
  have hn : matrixOpNorm X ≤ 1 :=
    (matrixTraceProjection_matrixOpNorm_le C U.val).trans (matrixOpNorm_unitary_le U)
  have he : hsNorm (U.val - X) ≤ ρ := matrixCommutantProjection_error_le D U.val ρ
    (fun V => hcomm (matrixSubalgebraUnitary D V).val V.val.property
      (matrixOpNorm_unitary_le _))
  obtain ⟨V, hVC, hVX⟩ := exists_matrixSubalgebraUnitary_close_of_gram C hX
  have hu : U.valᴴ * U.val = 1 := U.prop.1
  have hi : Xᴴ * X - 1 = Xᴴ * (X - U.val) + (Xᴴ - U.valᴴ) * U.val := by
    rw [mul_sub, sub_mul]
    rw [hu]
    abel
  have hXn : matrixOpNorm Xᴴ ≤ 1 := by simpa only [matrixOpNorm, Matrix.l2_opNorm_conjTranspose] using hn
  have hl := (hsNorm_mul_le_left Xᴴ (X - U.val)).trans
    (mul_le_mul_of_nonneg_right hXn (hsNorm_nonneg _))
  have hg := hsNorm_add_le (Xᴴ * (X - U.val)) ((Xᴴ - U.valᴴ) * U.val)
  rw [← hi, hsNorm_mul_unitary, ← Matrix.conjTranspose_sub, hsNorm_conjTranspose,
    hsNorm_sub_comm X U.val] at hg
  rw [hsNorm_sub_comm X U.val] at hl
  have ht := rectHSNorm_sub_triangle d U.val X V.val
  change hsNorm (U.val - V.val) ≤ hsNorm (U.val - X) + hsNorm (X - V.val) at ht
  refine ⟨V, fun Y hY => ((mem_matrixSubalgebraCommutant_iff D V.val).mp hVC Y hY).symm, ?_⟩
  nlinarith

theorem finiteNoDrift_anchor_transfer
    (A₀ D₀ A D : StarSubalgebra ℂ (CMatrix d)) {h : Nat}
    (U V : Fin h → UnitaryMatrix d) {rA rD ζ K ν : ℝ}
    (hA : MatrixNearInclusion A A₀ rA) (hD : MatrixNearInclusion D₀ D rD)
    (hUV : ∀ j, hsNorm ((U j).val - (V j).val) ≤ ζ)
    (hK : 0 ≤ K) (hanchor : FiniteNoDriftAnchor A₀ D₀ U K ν) :
    FiniteNoDriftAnchor A D V K (ν + rA + rD + 2 * K * (rA + ζ)) := by
  intro X hXA hXsa hX r hr
  let Y := matrixTraceProjection A₀ X
  have hYA : Y ∈ A₀ := matrixTraceProjection_mem A₀ X
  have hYn : matrixOpNorm Y ≤ 1 := (matrixTraceProjection_matrixOpNorm_le A₀ X).trans hX
  have hYsa : IsSelfAdjoint Y := by
    change star (matrixTraceProjection A₀ X) = matrixTraceProjection A₀ X
    rw [← matrixTraceProjection_star, hXsa.star_eq]
  have hXY : hsNorm (X - Y) ≤ rA := by
    obtain ⟨Z, hZ, hXZ⟩ := hA X hXA hX
    exact (matrixTraceProjection_bestApproximation A₀ X Z hZ).trans hXZ
  have hYcomm (j : Fin h) : hsNorm (Y * (U j).val - (U j).val * Y) ≤ r + 2 * (rA + ζ) := by
    have h₁ := finiteNoDrift_commutator_lipschitz (U j) Y X
    rw [hsNorm_sub_comm Y X] at h₁
    have h₂ := finiteNoDrift_commutator_unitary_lipschitz (U j) (V j) X hX
    linarith [hUV j, hr j]
  have hp := hanchor Y hYA hYsa hYn _ hYcomm
  obtain ⟨Z, hZ, hZdist⟩ := hD (matrixTraceProjection D₀ Y)
    (matrixTraceProjection_mem D₀ Y)
    ((matrixTraceProjection_matrixOpNorm_le D₀ Y).trans hYn)
  have ht := rectHSNorm_sub_triangle_three d X Y (matrixTraceProjection D₀ Y) Z
  change hsNorm (X - Z) ≤ hsNorm (X - Y) +
    hsNorm (Y - matrixTraceProjection D₀ Y) + hsNorm (matrixTraceProjection D₀ Y - Z) at ht
  have hb := (matrixTraceProjection_bestApproximation D X Z hZ).trans ht
  nlinarith

end ThomGame.Analysis
