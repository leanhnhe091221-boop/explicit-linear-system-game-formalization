module

public import ThomGame.Analysis.MatrixSpectralEnergy
public import ThomGame.Analysis.SpectralStepCoarea

/-!
# Actual matrix spectral projections

Upper spectral cuts use the matrix continuous functional calculus.
Every scalar function is continuous on the finite spectrum, so no
global continuity of the indicator is assumed.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator

variable {d h : Nat} {X : CMatrix d}

noncomputable def matrixSpectralCut (X : CMatrix d) (s : ℝ) : CMatrix d :=
  cfc (spectralStep s) X

noncomputable def matrixEigenbasisTuple (hX : Matrix.IsHermitian X)
    (U : Fin h → UnitaryMatrix d) : Fin h → UnitaryMatrix d :=
  fun r => hX.eigenvectorUnitary⁻¹ * U r * hX.eigenvectorUnitary

theorem matrix_cfc_conjugate (hX : Matrix.IsHermitian X) (f : ℝ → ℝ) :
    cfc f X = matrixUnitaryConjugation hX.eigenvectorUnitary
      (Matrix.diagonal (fun i => (f (hX.eigenvalues i) : ℂ))) := by
  rw [hX.cfc_eq]
  rfl

theorem matrixSpectralCut_eq_conjugate (hX : Matrix.IsHermitian X) (s : ℝ) :
    matrixSpectralCut X s = matrixUnitaryConjugation hX.eigenvectorUnitary
      (Matrix.diagonal (fun i => (spectralStep s (hX.eigenvalues i) : ℂ))) :=
  matrix_cfc_conjugate hX _

theorem matrix_diagonal_spectralStep_projection (e : Fin d → ℝ) (s : ℝ) :
    IsStarProjection (Matrix.diagonal (fun i => (spectralStep s (e i) : ℂ))) := by
  rw [isStarProjection_iff']
  constructor
  · rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [← pow_two, ← Complex.ofReal_pow, spectralStep_sq]
  · rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    simp

theorem matrixSpectralCut_isStarProjection (hX : Matrix.IsHermitian X) (s : ℝ) :
    IsStarProjection (matrixSpectralCut X s) := by
  rw [matrixSpectralCut_eq_conjugate hX]
  exact (matrix_diagonal_spectralStep_projection hX.eigenvalues s).map
    (Unitary.conjStarAlgAut ℂ (CMatrix d) hX.eigenvectorUnitary)

theorem matrixCoordinateEnergy_cfc (hX : Matrix.IsHermitian X)
    (U : Fin h → UnitaryMatrix d) (f : ℝ → ℝ) :
    matrixCoordinateEnergy U (cfc f X) =
      ∑ i, ∑ j, matrixEnergyWeight (matrixEigenbasisTuple hX U) i j *
        (f (hX.eigenvalues j) - f (hX.eigenvalues i)) ^ 2 := by
  rw [matrix_cfc_conjugate hX f]
  have he := matrixCoordinateEnergy_conjugate hX.eigenvectorUnitary⁻¹ U
    (matrixUnitaryConjugation hX.eigenvectorUnitary
      (Matrix.diagonal (fun i => (f (hX.eigenvalues i) : ℂ))))
  simp only [inv_inv, matrixUnitaryConjugation_inv] at he
  exact he.symm.trans (matrixCoordinateEnergy_diagonal _ _)

theorem matrixCoordinateEnergy_spectral (hX : Matrix.IsHermitian X)
    (U : Fin h → UnitaryMatrix d) :
    matrixCoordinateEnergy U X =
      ∑ i, ∑ j, matrixEnergyWeight (matrixEigenbasisTuple hX U) i j *
        (hX.eigenvalues j - hX.eigenvalues i) ^ 2 := by
  have he : cfc (fun t : ℝ => t) X = X := cfc_id ℝ X
  simpa only [he] using matrixCoordinateEnergy_cfc hX U (fun t => t)

theorem matrixSpectralCut_energy (hX : Matrix.IsHermitian X)
    (U : Fin h → UnitaryMatrix d) (s : ℝ) :
    matrixCoordinateEnergy U (matrixSpectralCut X s) =
      ∑ i, ∑ j, matrixEnergyWeight (matrixEigenbasisTuple hX U) i j *
        (spectralStep s (hX.eigenvalues j) - spectralStep s (hX.eigenvalues i)) ^ 2 :=
  matrixCoordinateEnergy_cfc hX U _

theorem normalizedTrace_diagonal_real (e : Fin d → ℝ) :
    (normalizedTrace (Matrix.diagonal (fun i => (e i : ℂ)))).re = (∑ i, e i) / d := by
  simp only [normalizedTrace, Matrix.trace_diagonal, Complex.div_natCast_re, Complex.re_sum,
    Complex.ofReal_re]

theorem matrixSpectralCut_trace (hX : Matrix.IsHermitian X) (s : ℝ) :
    (normalizedTrace (matrixSpectralCut X s)).re = (∑ i, spectralStep s (hX.eigenvalues i)) / d := by
  rw [matrixSpectralCut_eq_conjugate hX, matrixUnitaryConjugation_trace, normalizedTrace_diagonal_real]

theorem normalizedTrace_eq_eigenvalue_sum (hX : Matrix.IsHermitian X) :
    (normalizedTrace X).re = (∑ i, hX.eigenvalues i) / d := by
  have he : X = matrixUnitaryConjugation hX.eigenvectorUnitary
      (Matrix.diagonal (fun i => (hX.eigenvalues i : ℂ))) := hX.spectral_theorem
  calc
    _ = (normalizedTrace (matrixUnitaryConjugation hX.eigenvectorUnitary
        (Matrix.diagonal (fun i => (hX.eigenvalues i : ℂ))))).re := congrArg (fun A => (normalizedTrace A).re) he
    _ = _ := by rw [matrixUnitaryConjugation_trace, normalizedTrace_diagonal_real]

end ThomGame.Analysis
