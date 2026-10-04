module

public import ThomGame.Construction.CompressorSpectralNormalization
public import ThomGame.Analysis.CompressorPositiveTraceGap

/-!
# The H spectral assumption is discharged for every actual quotient representation

The remaining representation spectral condition is exactly the Q part.
The approximation conclusions remain conditional on that Q condition.
-/

@[expose] public section
namespace ThomGame.Construction

open Analysis Filter

def CompressorQRepresentationSpectralGap (dims : Nat → Nat) (hd : ∀ n, 0 < dims n)
    (L : Ultrafilter Nat) (φ : Compressor.GroupQ →* unitary (MatrixTracialQuotient dims (L : Filter Nat))) : Prop :=
  ∃ V : (n : Nat) → Fin 48 → UnitaryMatrix (dims n), ∃ κ : ℝ,
    (∀ j, matrixTupleClass dims V (L : Filter Nat) j = (φ (Compressor.generatorTuple j)).val) ∧
    MatrixMarkovSpectralGap dims V hd L κ

theorem compressor_positive_commutant_internal
    (dims : Nat → Nat) (hd : ∀ n, 0 < dims n) (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop)
    (φ : Compressor.GroupQ →* unitary (MatrixTracialQuotient dims (L : Filter Nat))) :
    ∃ A : (n : Nat) → StarSubalgebra ℂ (CMatrix (dims n)),
      unitaryRepresentationCommutant φ Compressor.positiveSubgroup = matrixInternalQuotient dims A (L : Filter Nat) := by
  obtain ⟨V, hV, hgap⟩ := Compressor.exists_positiveGeneratorTuple_matrixGap dims hd L hL φ
  exact exists_matrixRepresentation_internal_commutant_of_gap dims hd L hL φ Compressor.positiveSubgroup
    Compressor.positiveGeneratorTuple Compressor.positiveGeneratorTuple_generates V hV
    Compressor.positiveMarkovGapConstant hgap

theorem compressor_spectral_gaps_iff_Q_gap
    (dims : Nat → Nat) (hd : ∀ n, 0 < dims n) (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop)
    (φ : Compressor.GroupQ →* unitary (MatrixTracialQuotient dims (L : Filter Nat))) :
    CompressorRepresentationSpectralGaps dims hd L φ ↔ CompressorQRepresentationSpectralGap dims hd L φ := by
  constructor
  · rintro ⟨_, VQ, _, κQ, _, hVQ, _, hQ⟩
    exact ⟨VQ, κQ, hVQ, hQ⟩
  · rintro ⟨VQ, κQ, hVQ, hQ⟩
    obtain ⟨VH, hVH, hH⟩ := Compressor.exists_positiveGeneratorTuple_matrixGap dims hd L hL φ
    exact ⟨VH, VQ, Compressor.positiveMarkovGapConstant, κQ, hVH, hVQ, hH, hQ⟩

theorem compressor_internality_of_Q_spectral_gap
    (dims : Nat → Nat) (hd : ∀ n, 0 < dims n) (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop)
    (φ : Compressor.GroupQ →* unitary (MatrixTracialQuotient dims (L : Filter Nat)))
    (hgap : CompressorQRepresentationSpectralGap dims hd L φ) :
    ∃ A D : (n : Nat) → StarSubalgebra ℂ (CMatrix (dims n)),
      unitaryRepresentationCommutant φ Compressor.positiveSubgroup = matrixInternalQuotient dims A (L : Filter Nat) ∧
      unitaryRepresentationCommutant φ ⊤ = matrixInternalQuotient dims D (L : Filter Nat) :=
  compressor_internality_of_spectral_gaps dims hd L hL φ
    ((compressor_spectral_gaps_iff_Q_gap dims hd L hL φ).mpr hgap)

theorem lambda_matrix_J_eq_one_of_Q_spectral_gap
    (dims : Nat → Nat) (hd : ∀ n, 0 < dims n) (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop)
    (φ : Lambda.GroupLambda →* unitary (MatrixTracialQuotient dims (L : Filter Nat)))
    (hgap : CompressorQRepresentationSpectralGap dims hd L
      ((φ.comp Double.toLambda).comp (Double.copyHom false))) : φ Lambda.JElement = 1 :=
  lambda_matrix_J_eq_one_of_compressor_spectral_gaps dims hd L hL φ
    ((compressor_spectral_gaps_iff_Q_gap dims hd L hL _).mpr hgap)

theorem lambdaApproximatelyTrivial_of_Q_spectral_gaps
    (hgap : ∀ (dims : Nat → Nat) (hd : ∀ n, 0 < dims n)
      (φ : Compressor.GroupQ →* unitary (MatrixTracialQuotient dims (hyperfilter Nat))),
        CompressorQRepresentationSpectralGap dims hd (hyperfilter Nat) φ) : LambdaApproximatelyTrivial := by
  apply lambdaApproximatelyTrivial_of_compressor_spectral_gaps
  intro dims hd φ
  exact (compressor_spectral_gaps_iff_Q_gap dims hd (hyperfilter Nat) Nat.hyperfilter_le_atTop φ).mpr
    (hgap dims hd φ)

theorem sigmaApproximatelyTrivial_of_Q_spectral_gaps
    (hgap : ∀ (dims : Nat → Nat) (hd : ∀ n, 0 < dims n)
      (φ : Compressor.GroupQ →* unitary (MatrixTracialQuotient dims (hyperfilter Nat))),
        CompressorQRepresentationSpectralGap dims hd (hyperfilter Nat) φ) : SigmaApproximatelyTrivial :=
  sigmaApproximatelyTrivial_of_lambda (lambdaApproximatelyTrivial_of_Q_spectral_gaps hgap)

end ThomGame.Construction
