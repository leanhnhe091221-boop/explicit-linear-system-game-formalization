module

public import ThomGame.Construction.CompressorInternalNormalization
public import ThomGame.Construction.ApproximationReduction
public import ThomGame.Analysis.ApproximationFiniteCriterion

/-!
# From actual Q/H internality to the specified uniform approximation conclusion

All analytic normalization and algebraic obstruction steps are proved.
The remaining premise is the internality of the two actual commutants
for every representation of the specified Q. ALT and the still-needed
group spectral gaps are to discharge that premise.
-/

@[expose] public section
namespace ThomGame.Construction

open Analysis Filter

theorem lambdaApproximatelyTrivial_of_compressor_internality
    (hI : ∀ (dims : Nat → Nat), (∀ n, 0 < dims n) →
      ∀ φ : Compressor.GroupQ →* unitary (MatrixTracialQuotient dims (hyperfilter Nat)),
        ∃ A D : (n : Nat) → StarSubalgebra ℂ (CMatrix (dims n)),
          unitaryRepresentationCommutant φ Compressor.positiveSubgroup =
            matrixInternalQuotient dims A (hyperfilter Nat) ∧
          unitaryRepresentationCommutant φ ⊤ = matrixInternalQuotient dims D (hyperfilter Nat)) :
    LambdaApproximatelyTrivial := by
  apply (approximatelyTrivial_iff_matrixQuotient_killed Lambda.rawRelationSet
    (FreeGroup.of (72 : Lambda.Generator)) lambda_rawRelationSet_finite
    (hyperfilter Nat) Nat.hyperfilter_le_atTop).mpr
  intro dims hd φ
  let : ∀ n, NeZero (dims n) := fun n => ⟨ne_of_gt (hd n)⟩
  obtain ⟨A, D, hA, hD⟩ := hI dims hd ((φ.comp Double.toLambda).comp (Double.copyHom false))
  exact lambda_matrix_J_eq_one_of_internal_commutants dims (hyperfilter Nat) φ ⟨A, hA⟩ ⟨D, hD⟩

theorem sigmaApproximatelyTrivial_of_compressor_internality
    (hI : ∀ (dims : Nat → Nat), (∀ n, 0 < dims n) →
      ∀ φ : Compressor.GroupQ →* unitary (MatrixTracialQuotient dims (hyperfilter Nat)),
        ∃ A D : (n : Nat) → StarSubalgebra ℂ (CMatrix (dims n)),
          unitaryRepresentationCommutant φ Compressor.positiveSubgroup =
            matrixInternalQuotient dims A (hyperfilter Nat) ∧
          unitaryRepresentationCommutant φ ⊤ = matrixInternalQuotient dims D (hyperfilter Nat)) :
    SigmaApproximatelyTrivial :=
  sigmaApproximatelyTrivial_of_lambda (lambdaApproximatelyTrivial_of_compressor_internality hI)

end ThomGame.Construction
