module

public import ThomGame.Construction.CompressorPositiveSpectralNormalization
public import ThomGame.Analysis.CompressorShearTraceGap

/-!
# Approximate triviality reduced to the actual integral shear Kazhdan theorem

All implications use the existing presentations, exact coordinate
unitary lifts, and normalized matrix trace. The shear Kazhdan theorem
remains an explicit hypothesis.
-/

@[expose] public section
namespace ThomGame.Construction

open Analysis Filter

theorem compressor_Q_spectral_gap_of_shear
    (hShear : HasFiniteHilbertKazhdanSet.{0} IntegralShear.ShearGroup)
    (dims : Nat → Nat) (hd : ∀ n, 0 < dims n) (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop)
    (φ : Compressor.GroupQ →* unitary (MatrixTracialQuotient dims (L : Filter Nat))) :
    CompressorQRepresentationSpectralGap dims hd L φ := by
  obtain ⟨S, b, hb, hS⟩ := hShear
  obtain ⟨V, hV, hgap⟩ := Compressor.exists_generatorTuple_matrixGap_of_shear S b hb hS dims hd L hL φ
  exact ⟨V, Compressor.shearMarkovGapConstant S b, hV, hgap⟩

theorem compressor_spectral_gaps_of_shear
    (hShear : HasFiniteHilbertKazhdanSet.{0} IntegralShear.ShearGroup)
    (dims : Nat → Nat) (hd : ∀ n, 0 < dims n) (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop)
    (φ : Compressor.GroupQ →* unitary (MatrixTracialQuotient dims (L : Filter Nat))) :
    CompressorRepresentationSpectralGaps dims hd L φ :=
  (compressor_spectral_gaps_iff_Q_gap dims hd L hL φ).mpr
    (compressor_Q_spectral_gap_of_shear hShear dims hd L hL φ)

theorem compressor_internality_of_shear
    (hShear : HasFiniteHilbertKazhdanSet.{0} IntegralShear.ShearGroup)
    (dims : Nat → Nat) (hd : ∀ n, 0 < dims n) (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop)
    (φ : Compressor.GroupQ →* unitary (MatrixTracialQuotient dims (L : Filter Nat))) :
    ∃ A D : (n : Nat) → StarSubalgebra ℂ (CMatrix (dims n)),
      unitaryRepresentationCommutant φ Compressor.positiveSubgroup = matrixInternalQuotient dims A (L : Filter Nat) ∧
      unitaryRepresentationCommutant φ ⊤ = matrixInternalQuotient dims D (L : Filter Nat) :=
  compressor_internality_of_Q_spectral_gap dims hd L hL φ
    (compressor_Q_spectral_gap_of_shear hShear dims hd L hL φ)

theorem lambda_matrix_J_eq_one_of_shear
    (hShear : HasFiniteHilbertKazhdanSet.{0} IntegralShear.ShearGroup)
    (dims : Nat → Nat) (hd : ∀ n, 0 < dims n) (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop)
    (φ : Lambda.GroupLambda →* unitary (MatrixTracialQuotient dims (L : Filter Nat))) :
    φ Lambda.JElement = 1 :=
  lambda_matrix_J_eq_one_of_Q_spectral_gap dims hd L hL φ
    (compressor_Q_spectral_gap_of_shear hShear dims hd L hL _)

theorem lambdaApproximatelyTrivial_of_shear
    (hShear : HasFiniteHilbertKazhdanSet.{0} IntegralShear.ShearGroup) : LambdaApproximatelyTrivial := by
  apply lambdaApproximatelyTrivial_of_Q_spectral_gaps
  intro dims hd φ
  exact compressor_Q_spectral_gap_of_shear hShear dims hd (hyperfilter Nat) Nat.hyperfilter_le_atTop φ

theorem sigmaApproximatelyTrivial_of_shear
    (hShear : HasFiniteHilbertKazhdanSet.{0} IntegralShear.ShearGroup) : SigmaApproximatelyTrivial :=
  sigmaApproximatelyTrivial_of_lambda (lambdaApproximatelyTrivial_of_shear hShear)

end ThomGame.Construction
