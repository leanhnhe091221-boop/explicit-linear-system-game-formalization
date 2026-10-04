module

public import ThomGame.Construction.InvolutionGroup
public import ThomGame.Construction.SolutionGroup
public import ThomGame.Groups.WheelProduct

/-!
# The concrete homomorphisms Λ → K → Σ

Every defining relation of K is proved in the wheel solution group. The
resulting homomorphisms preserve the specified central element, including
after reindexing to the supplied matrix. Injectivity remains separate.
-/

@[expose] public section
namespace ThomGame.Construction

theorem wheel_ordinary_product (r : WheelIndex) :
    ((wheelWord r).map (fun s => SolutionGroup.x system (.inl s))).prod =
      if wheelFamily.parity r = 1 then SolutionGroup.J system else 1 := by
  have h := wheelFamily.solution_word_product r
  change (List.ofFn (fun j : Fin (wheelWord r).length =>
    SolutionGroup.x system (.inl ((wheelWord r)[j.val])))).prod =
    if wheelFamily.parity r = 1 then SolutionGroup.J system else 1 at h
  rw [List.ofFn_getElem_eq_map (wheelWord r) (fun s => SolutionGroup.x system (.inl s))] at h
  exact h

def wheelInvolutionModel :
    InvolutionPresentation.Model involutionPresentation (SolutionGroup.GroupOf system) where
  j := SolutionGroup.J system
  x s := SolutionGroup.x system (.inl s)
  j_square := SolutionGroup.J_sq system
  x_square s := SolutionGroup.x_sq system (.inl s)
  j_commutes s := SolutionGroup.J_commutes_x system (.inl s)
  word_product := wheel_ordinary_product

def involutionToWheel : InvolutionGroup →* SolutionGroup.GroupOf system :=
  wheelInvolutionModel.toHom

theorem involutionToWheel_J : involutionToWheel J_star = SolutionGroup.J system :=
  wheelInvolutionModel.toHom_J

theorem involutionToWheel_x (s : Ordinary) :
    involutionToWheel (ordinaryInvolution s) = SolutionGroup.x system (.inl s) :=
  wheelInvolutionModel.toHom_x s

def involutionToSigma : InvolutionGroup →* SigmaGroup :=
  wheelSolutionEquiv.toMonoidHom.comp involutionToWheel

theorem involutionToSigma_J : involutionToSigma J_star = J_sigma := by
  change wheelSolutionEquiv (involutionToWheel J_star) = _
  rw [involutionToWheel_J, wheelSolutionEquiv_J]

theorem involutionToSigma_x (s : Ordinary) :
    involutionToSigma (ordinaryInvolution s) = observable (colEquiv (.inl s)) := by
  change wheelSolutionEquiv (involutionToWheel (ordinaryInvolution s)) = _
  rw [involutionToWheel_x]
  exact SolutionGroup.reindexEquiv_x system rowEquiv colEquiv (.inl s)

def lambdaToSigma : Lambda.GroupLambda →* SigmaGroup :=
  involutionToSigma.comp lambdaToInvolution

theorem lambdaToSigma_of (g : Lambda.Generator) :
    lambdaToSigma (PresentedGroup.of (rels := Lambda.rawRelationSet) g) =
      (observable (colEquiv (.inl (g, false))) * observable (colEquiv (.inl (g, true)))) ^ 2 := by
  change involutionToSigma
    (lambdaToInvolution (PresentedGroup.of (rels := Lambda.rawRelationSet) g)) = _
  rw [lambdaToInvolution_of]
  change involutionToSigma ((ordinaryInvolution (g, false) * ordinaryInvolution (g, true)) ^ 2) = _
  rw [map_pow, map_mul, involutionToSigma_x, involutionToSigma_x]

theorem lambdaToSigma_J :
    lambdaToSigma Lambda.JElement = J_sigma := by
  change involutionToSigma (lambdaToInvolution Lambda.JElement) = _
  rw [lambdaToInvolution_J, involutionToSigma_J]

end ThomGame.Construction
