module

public import ThomGame.Groups.CompressorGeneratingTuples
public import ThomGame.Analysis.MatrixRepresentationSpectralInternals
public import ThomGame.Construction.InternalityApproximationReduction

/-!
# The actual Q/H spectral gaps imply the specified approximation result

The remaining gap condition is the actual quadratic-form gap on the
trace Hilbert space for representatives of the 24 H and 48 Q generators.
ALT and Thom are proved steps in the reduction, not further assumptions.
The H condition is discharged downstream in
CompressorPositiveSpectralNormalization. The Q condition is still open;
no unconditional approximation conclusion is asserted here.
-/

@[expose] public section
namespace ThomGame.Construction

open Analysis Filter

def CompressorRepresentationSpectralGaps (dims : Nat → Nat) (hd : ∀ n, 0 < dims n)
    (L : Ultrafilter Nat) (φ : Compressor.GroupQ →* unitary (MatrixTracialQuotient dims (L : Filter Nat))) : Prop :=
  ∃ VH : (n : Nat) → Fin 24 → UnitaryMatrix (dims n),
    ∃ VQ : (n : Nat) → Fin 48 → UnitaryMatrix (dims n), ∃ κH κQ : ℝ,
      (∀ j, matrixTupleClass dims VH (L : Filter Nat) j = (φ (Compressor.positiveGeneratorTuple j)).val) ∧
      (∀ j, matrixTupleClass dims VQ (L : Filter Nat) j = (φ (Compressor.generatorTuple j)).val) ∧
      MatrixMarkovSpectralGap dims VH hd L κH ∧ MatrixMarkovSpectralGap dims VQ hd L κQ

theorem compressor_internality_of_spectral_gaps
    (dims : Nat → Nat) (hd : ∀ n, 0 < dims n) (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop)
    (φ : Compressor.GroupQ →* unitary (MatrixTracialQuotient dims (L : Filter Nat)))
    (hgap : CompressorRepresentationSpectralGaps dims hd L φ) :
    ∃ A D : (n : Nat) → StarSubalgebra ℂ (CMatrix (dims n)),
      unitaryRepresentationCommutant φ Compressor.positiveSubgroup = matrixInternalQuotient dims A (L : Filter Nat) ∧
      unitaryRepresentationCommutant φ ⊤ = matrixInternalQuotient dims D (L : Filter Nat) := by
  obtain ⟨VH, VQ, κH, κQ, hVH, hVQ, hH, hQ⟩ := hgap
  obtain ⟨A, hA⟩ := exists_matrixRepresentation_internal_commutant_of_gap dims hd L hL φ
    Compressor.positiveSubgroup Compressor.positiveGeneratorTuple Compressor.positiveGeneratorTuple_generates VH hVH κH hH
  obtain ⟨D, hD⟩ := exists_matrixRepresentation_internal_commutant_of_gap dims hd L hL φ
    ⊤ Compressor.generatorTuple Compressor.generatorTuple_generates VQ hVQ κQ hQ
  exact ⟨A, D, hA, hD⟩

theorem lambda_matrix_J_eq_one_of_compressor_spectral_gaps
    (dims : Nat → Nat) (hd : ∀ n, 0 < dims n) (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop)
    (φ : Lambda.GroupLambda →* unitary (MatrixTracialQuotient dims (L : Filter Nat)))
    (hgap : CompressorRepresentationSpectralGaps dims hd L
      ((φ.comp Double.toLambda).comp (Double.copyHom false))) : φ Lambda.JElement = 1 := by
  let : ∀ n, NeZero (dims n) := fun n => ⟨ne_of_gt (hd n)⟩
  obtain ⟨A, D, hA, hD⟩ := compressor_internality_of_spectral_gaps dims hd L hL
    ((φ.comp Double.toLambda).comp (Double.copyHom false)) hgap
  exact lambda_matrix_J_eq_one_of_internal_commutants dims L φ ⟨A, hA⟩ ⟨D, hD⟩

theorem lambdaApproximatelyTrivial_of_compressor_spectral_gaps
    (hgap : ∀ (dims : Nat → Nat) (hd : ∀ n, 0 < dims n)
      (φ : Compressor.GroupQ →* unitary (MatrixTracialQuotient dims (hyperfilter Nat))),
        CompressorRepresentationSpectralGaps dims hd (hyperfilter Nat) φ) : LambdaApproximatelyTrivial := by
  apply lambdaApproximatelyTrivial_of_compressor_internality
  intro dims hd φ
  exact compressor_internality_of_spectral_gaps dims hd (hyperfilter Nat) Nat.hyperfilter_le_atTop φ (hgap dims hd φ)

theorem sigmaApproximatelyTrivial_of_compressor_spectral_gaps
    (hgap : ∀ (dims : Nat → Nat) (hd : ∀ n, 0 < dims n)
      (φ : Compressor.GroupQ →* unitary (MatrixTracialQuotient dims (hyperfilter Nat))),
        CompressorRepresentationSpectralGaps dims hd (hyperfilter Nat) φ) : SigmaApproximatelyTrivial :=
  sigmaApproximatelyTrivial_of_lambda (lambdaApproximatelyTrivial_of_compressor_spectral_gaps hgap)

end ThomGame.Construction
