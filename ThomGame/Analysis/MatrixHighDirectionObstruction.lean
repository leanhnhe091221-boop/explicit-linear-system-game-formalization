module

public import ThomGame.Analysis.MatrixPolarOverlap
public import ThomGame.Analysis.MatrixPolarOrthogonalPairing
public import ThomGame.Analysis.MatrixHighProductBounds

/-!
# Quantitative obstruction to two orthogonal high directions

The product mass is at least (1-4rho)M and at most 644rho M.
For rho at most 1/1024 and positive M this is impossible.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable {d : Nat} [NeZero d]

theorem matrixHighPolar_orthogonality_obstruction (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ X, normalizedTrace (F X) = normalizedTrace X)
    (P Q X Y U V : CMatrix d) (hP : IsStarProjection P) (hQ : IsStarProjection Q) (hQne : Q ≠ 0)
    (rho M : ℝ) (hrho : 0 ≤ rho) (hsmall : rho ≤ 1 / 1024) (hM : 0 < M)
    (hX : hsNorm X ^ 2 ≤ M) (horth : normalizedTrace (star X * Y) = 0)
    (hU : IsStarProjection (U * star U)) (hV : IsStarProjection (V * star V))
    (hUP : U * star U ≤ P) (hVP : V * star V ≤ P)
    (hnU : matrixOpNorm U ≤ 1) (hnV : matrixOpNorm V ≤ 1)
    (hmU : (1 - 2 * rho) * M ≤ hsNorm U ^ 2)
    (hmV : (1 - 2 * rho) * M ≤ hsNorm V ^ 2) (hVM : hsNorm V ^ 2 ≤ M)
    (hPM : (normalizedTrace P).re ≤ M) (hQM : M / 2 ≤ (normalizedTrace Q).re)
    (hUX : hsNorm (U - X) ^ 2 ≤ 4 * rho * M) (hVY : hsNorm (V - Y) ^ 2 ≤ 4 * rho * M)
    (heU : matrixChannelEnergy F.toLinearMap U ≤ 18 * rho * M)
    (heV : matrixChannelEnergy F.toLinearMap V ≤ 18 * rho * M)
    (hcorner : hsNorm (F (star U * V) -
      (normalizedTrace (star U * V) / normalizedTrace Q) • Q) ≤ rho ^ 4 * hsNorm (star U * V)) : False := by
  have hlow := matrixPartialIsometries_overlap_mass hP hU hV hUP hVP
  have hlow' : (1 - 4 * rho) * M ≤ hsNorm (star U * V) ^ 2 := by linarith
  have hpair := matrixOrthogonal_close_pairing_sq X Y U V rho M hrho hM.le horth hX hVM hUX hVY
  have hscalar : ‖normalizedTrace (star U * V)‖ ^ 2 / (normalizedTrace Q).re ≤ 32 * rho * M := by
    apply (div_le_iff₀ (matrixProjection_trace_re_pos hQ hQne)).mpr
    have hb := mul_le_mul_of_nonneg_left hQM (by positivity : 0 ≤ 32 * rho * M)
    nlinarith only [hpair, hb]
  have herr := matrixHighPolar_product_scalar_error F hF htrace Q U V rho M hrho (by linarith)
    hnU hnV hVM heU heV hcorner
  have hmass := matrixCorner_mass_le_scalar_error hQ hQne (star U * V)
  have hupp : hsNorm (star U * V) ^ 2 ≤ 644 * rho * M := by linarith
  have hc := mul_le_mul_of_nonneg_right hsmall hM.le
  nlinarith only [hlow', hupp, hc, hM]

end ThomGame.Analysis
