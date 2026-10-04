module

public import ThomGame.Construction.ApproximationReduction
public import ThomGame.Analysis.UnitaryQuotientEmbedding
public import ThomGame.Analysis.MatrixUltratrace
public import ThomGame.Groups.CentralizerEmbedding

/-!
# The actual matrix star algebra suffices for the approximation reduction

The unitary sequence quotient embeds faithfully into the unitary group
of the bounded-matrix quotient carrying the normalized faithful trace.
Consequently normalization in the latter group implies the precise
normalization input of the previously established Lambda reduction.
The analytic normalization theorem itself remains an explicit premise.
-/

@[expose] public section
namespace ThomGame.Construction

open Analysis Filter

theorem unitaryQuotient_normalizes_of_matrix_normalizes
    (dims : Nat → Nat) (φ : Lambda.GroupLambda →* UnitarySequenceQuotient dims (hyperfilter Nat))
    (hn : ((unitaryQuotientEmbedding dims (hyperfilter Nat)).comp (φ.comp Double.toLambda))
        Double.t₁Element ∈
      Subgroup.normalizer
        (Double.imageCentralizer
          ((unitaryQuotientEmbedding dims (hyperfilter Nat)).comp (φ.comp Double.toLambda)) :
          Set (unitary (MatrixTracialQuotient dims (hyperfilter Nat))))) :
    (φ.comp Double.toLambda) Double.t₁Element ∈
      Subgroup.normalizer (Double.imageCentralizer (φ.comp Double.toLambda) :
        Set (UnitarySequenceQuotient dims (hyperfilter Nat))) := by
  exact normalizes_centralizer_range_of_injective
    (unitaryQuotientEmbedding dims (hyperfilter Nat))
    (unitaryQuotientEmbedding_injective dims (hyperfilter Nat))
    ((φ.comp Double.toLambda).comp Double.positiveHom)
    ((φ.comp Double.toLambda) Double.t₁Element) hn

theorem lambdaApproximatelyTrivial_of_matrix_normalizes_centralizer
    (hn : ∀ (dims : Nat → Nat), (∀ n, 0 < dims n) →
      ∀ φ : Lambda.GroupLambda →* unitary (MatrixTracialQuotient dims (hyperfilter Nat)),
        (φ.comp Double.toLambda) Double.t₁Element ∈
          Subgroup.normalizer (Double.imageCentralizer (φ.comp Double.toLambda) :
            Set (unitary (MatrixTracialQuotient dims (hyperfilter Nat))))) :
    LambdaApproximatelyTrivial := by
  apply lambdaApproximatelyTrivial_of_normalizes_centralizer
  intro dims hd φ
  apply unitaryQuotient_normalizes_of_matrix_normalizes dims φ
  exact hn dims hd ((unitaryQuotientEmbedding dims (hyperfilter Nat)).comp φ)

theorem sigmaApproximatelyTrivial_of_matrix_normalizes_centralizer
    (hn : ∀ (dims : Nat → Nat), (∀ n, 0 < dims n) →
      ∀ φ : Lambda.GroupLambda →* unitary (MatrixTracialQuotient dims (hyperfilter Nat)),
        (φ.comp Double.toLambda) Double.t₁Element ∈
          Subgroup.normalizer (Double.imageCentralizer (φ.comp Double.toLambda) :
            Set (unitary (MatrixTracialQuotient dims (hyperfilter Nat))))) :
    SigmaApproximatelyTrivial :=
  sigmaApproximatelyTrivial_of_lambda (lambdaApproximatelyTrivial_of_matrix_normalizes_centralizer hn)

end ThomGame.Construction
