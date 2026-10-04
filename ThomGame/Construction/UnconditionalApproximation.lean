module

public import ThomGame.Analysis.CompressorKazhdan
public import ThomGame.Construction.CompressorShearSpectralNormalization

/-! Unconditional approximate triviality for the actual Lambda and numbered Sigma presentations. -/

@[expose] public section
namespace ThomGame.Construction

open Analysis Filter

theorem compressor_Q_spectral_gap
    (dims : Nat → Nat) (hd : ∀ n, 0 < dims n) (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop)
    (φ : Compressor.GroupQ →* unitary (MatrixTracialQuotient dims (L : Filter Nat))) :
    CompressorQRepresentationSpectralGap dims hd L φ :=
  compressor_Q_spectral_gap_of_shear integralShear_hasFiniteHilbertKazhdanSet dims hd L hL φ

theorem compressor_spectral_gaps
    (dims : Nat → Nat) (hd : ∀ n, 0 < dims n) (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop)
    (φ : Compressor.GroupQ →* unitary (MatrixTracialQuotient dims (L : Filter Nat))) :
    CompressorRepresentationSpectralGaps dims hd L φ :=
  compressor_spectral_gaps_of_shear integralShear_hasFiniteHilbertKazhdanSet dims hd L hL φ

theorem compressor_internality
    (dims : Nat → Nat) (hd : ∀ n, 0 < dims n) (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop)
    (φ : Compressor.GroupQ →* unitary (MatrixTracialQuotient dims (L : Filter Nat))) :
    ∃ A D : (n : Nat) → StarSubalgebra ℂ (CMatrix (dims n)),
      unitaryRepresentationCommutant φ Compressor.positiveSubgroup = matrixInternalQuotient dims A (L : Filter Nat) ∧
      unitaryRepresentationCommutant φ ⊤ = matrixInternalQuotient dims D (L : Filter Nat) :=
  compressor_internality_of_shear integralShear_hasFiniteHilbertKazhdanSet dims hd L hL φ

theorem lambda_matrix_J_eq_one
    (dims : Nat → Nat) (hd : ∀ n, 0 < dims n) (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop)
    (φ : Lambda.GroupLambda →* unitary (MatrixTracialQuotient dims (L : Filter Nat))) :
    φ Lambda.JElement = 1 :=
  lambda_matrix_J_eq_one_of_shear integralShear_hasFiniteHilbertKazhdanSet dims hd L hL φ

theorem lambdaApproximatelyTrivial : LambdaApproximatelyTrivial :=
  lambdaApproximatelyTrivial_of_shear integralShear_hasFiniteHilbertKazhdanSet

theorem sigmaApproximatelyTrivial : SigmaApproximatelyTrivial :=
  sigmaApproximatelyTrivial_of_shear integralShear_hasFiniteHilbertKazhdanSet

theorem sigmaApproximation_conclusion :
    J_sigma ≠ 1 ∧ ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ (d : Nat), 0 < d →
        ∀ f : MatrixAssignment (SolutionGroup.Generator (Fin 1889684)) d,
          IsApproxRepresentation (SolutionGroup.relators numberedSystem) δ f →
            unitaryLength (f (FreeGroup.of none)) < η :=
  sigmaApproximation_conclusion_of_lambda lambdaApproximatelyTrivial

theorem sigmaApproximation_hsNorm :
    J_sigma ≠ 1 ∧ ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ (d : Nat), 0 < d →
        ∀ f : MatrixAssignment (SolutionGroup.Generator (Fin 1889684)) d,
          IsApproxRepresentation (SolutionGroup.relators numberedSystem) δ f →
            hsNorm ((f (FreeGroup.of none)).val - 1) < η :=
  sigmaApproximation_conclusion

theorem sigma_uniform_no_negative_J :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (d : Nat), 0 < d →
      ∀ f : MatrixAssignment (SolutionGroup.Generator (Fin 1889684)) d,
        IsApproxRepresentation (SolutionGroup.relators numberedSystem) δ f → f (FreeGroup.of none) ≠ -1 :=
  approximatelyTrivial_no_neg_one _ _ sigmaApproximatelyTrivial

end ThomGame.Construction
