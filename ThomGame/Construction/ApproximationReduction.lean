module

public import ThomGame.Analysis.ApproximationTransport
public import ThomGame.Construction.WheelHom
public import ThomGame.Construction.SigmaNontrivial
public import ThomGame.Groups.DoubleCentralizer

/-!
# The actual Lambda-to-Sigma approximation reduction

The approximation predicates use the existing finite presentations and
free-group words for their specified central generators. The verified
homomorphism transfers dimension-uniform approximate triviality from
Lambda to Sigma. A final conditional theorem exposes exactly the still
unproved matrix-quotient centralizer normalization input.
-/

@[expose] public section
namespace ThomGame.Construction

open Analysis Filter

theorem lambda_rawRelationSet_finite : Lambda.rawRelationSet.Finite :=
  (List.finite_toSet Lambda.rawRelators).image FreeGroup.mk

def LambdaApproximatelyTrivial : Prop :=
  ApproximatelyTrivial Lambda.rawRelationSet (FreeGroup.of (72 : Lambda.Generator))

def SigmaApproximatelyTrivial : Prop :=
  ApproximatelyTrivial (SolutionGroup.relators numberedSystem)
    (FreeGroup.of (none : SolutionGroup.Generator (Fin 1889684)))

theorem sigmaApproximatelyTrivial_of_lambda (h : LambdaApproximatelyTrivial) :
    SigmaApproximatelyTrivial := by
  exact approximatelyTrivial_map lambda_rawRelationSet_finite Sigma_presentation_finite
    lambdaToSigma (FreeGroup.of (72 : Lambda.Generator)) (FreeGroup.of none) lambdaToSigma_J h

theorem sigmaApproximatelyTrivial_iff_quotient_killed :
    SigmaApproximatelyTrivial ↔
      ∀ (dims : Nat → Nat), (∀ n, 0 < dims n) →
        ∀ φ : SigmaGroup →* UnitarySequenceQuotient dims (hyperfilter Nat), φ J_sigma = 1 := by
  exact approximatelyTrivial_iff_hyperfilter_killed _ _ Sigma_presentation_finite

theorem lambdaApproximatelyTrivial_of_normalizes_centralizer
    (hn : ∀ (dims : Nat → Nat), (∀ n, 0 < dims n) →
      ∀ φ : Lambda.GroupLambda →* UnitarySequenceQuotient dims (hyperfilter Nat),
        (φ.comp Double.toLambda) Double.t₁Element ∈
          Subgroup.normalizer (Double.imageCentralizer (φ.comp Double.toLambda) :
            Set (UnitarySequenceQuotient dims (hyperfilter Nat)))) : LambdaApproximatelyTrivial := by
  apply (approximatelyTrivial_iff_hyperfilter_killed _ _ lambda_rawRelationSet_finite).mpr
  intro dims hd φ
  exact Lambda.hom_J_eq_one_of_normalizes_centralizer φ (hn dims hd φ)

theorem sigmaApproximation_conclusion_of_lambda (h : LambdaApproximatelyTrivial) :
    J_sigma ≠ 1 ∧ ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ (d : Nat), 0 < d →
        ∀ f : MatrixAssignment (SolutionGroup.Generator (Fin 1889684)) d,
          IsApproxRepresentation (SolutionGroup.relators numberedSystem) δ f →
            unitaryLength (f (FreeGroup.of none)) < η :=
  ⟨J_sigma_ne_one, sigmaApproximatelyTrivial_of_lambda h⟩

end ThomGame.Construction
