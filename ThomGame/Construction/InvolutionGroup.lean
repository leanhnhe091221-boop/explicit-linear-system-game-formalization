module

public import ThomGame.Construction.Wheel
public import ThomGame.Groups.InvolutionPresentation
public import ThomGame.Groups.LambdaRelations
public import ThomGame.Finite.InvolutionEvaluation

/-!
# The concrete intermediate involution group

The ordinary involutions are (g, false) and (g, true) for the 74 original
generators, including the original generator J of Λ. A separate central
generator J_* is adjoined. The final odd relation identifies J_* with the
substituted original J. The homomorphism from Λ is constructed below;
its injectivity is proved in `Construction.InvolutionFaithful`.
-/

@[expose] public section
namespace ThomGame.Construction

def involutionPresentation : InvolutionPresentation WheelIndex Ordinary where
  word := wheelWord
  parity := wheelFamily.parity

theorem involutionPresentation_collegial : involutionPresentation.Collegial :=
  InvolutionPresentation.collegial_of_even involutionPresentation
    wheelWord_cyclicallyReduced
    (fun r => by change 2 ≤ (wheelWord r).length; have := wheelWord_length_ge_four r; omega)
    wheelWord_count_even

abbrev InvolutionGroup := InvolutionPresentation.GroupOf involutionPresentation

/-- The fresh distinguished central generator, not either of the two ordinary
involutions coming from the original Λ generator numbered 73. -/
def J_star : InvolutionGroup := InvolutionPresentation.J involutionPresentation

def ordinaryInvolution (g : Ordinary) : InvolutionGroup :=
  InvolutionPresentation.x involutionPresentation g

theorem J_star_square : J_star * J_star = 1 :=
  InvolutionPresentation.J_sq involutionPresentation

theorem J_star_central (g : InvolutionGroup) : Commute J_star g :=
  InvolutionPresentation.J_commutes involutionPresentation g

theorem ordinaryInvolution_square (g : Ordinary) :
    ordinaryInvolution g * ordinaryInvolution g = 1 :=
  InvolutionPresentation.x_sq involutionPresentation g

theorem involution_relators_finite : (InvolutionPresentation.relators involutionPresentation).Finite :=
  InvolutionPresentation.relators_finite involutionPresentation

def lambdaImage (g : Lambda.Generator) : InvolutionGroup :=
  InvolutionWords.generatorImage ordinaryInvolution g

theorem lambdaImage_satisfies (r : Word Lambda.Generator) (hr : r ∈ Lambda.normalizedRelators) :
    Word.eval lambdaImage r = 1 := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
  have h := InvolutionPresentation.word_product involutionPresentation (some ⟨i, hi⟩)
  have hp : involutionPresentation.parity (some ⟨i, hi⟩) = 0 := rfl
  rw [hp, ite_eq_right (by decide : ¬ (0 : ZMod 2) = 1)] at h
  change ((InvolutionWords.substitute (Lambda.normalizedRelators[i]'hi)).map
    ordinaryInvolution).prod = 1 at h
  rw [InvolutionWords.substitute_product ordinaryInvolution ordinaryInvolution_square] at h
  exact h

def normalizedLambdaToInvolution : Lambda.NormalizedGroupLambda →* InvolutionGroup :=
  PresentedGroup.toGroup (f := lambdaImage) (rels := Lambda.normalizedRelationSet) (by
    rintro _ ⟨r, hr, rfl⟩
    exact lambdaImage_satisfies r hr)

theorem normalizedLambdaToInvolution_of (g : Lambda.Generator) :
    normalizedLambdaToInvolution (PresentedGroup.of (rels := Lambda.normalizedRelationSet) g) =
      lambdaImage g := by
  exact PresentedGroup.toGroup.of (x := g) _

/-- The substitution descends from the actual raw presentation of Λ. -/
def lambdaToInvolution : Lambda.GroupLambda →* InvolutionGroup :=
  normalizedLambdaToInvolution.comp Lambda.normalizationEquiv.toMonoidHom

theorem lambdaToInvolution_of (g : Lambda.Generator) :
    lambdaToInvolution (PresentedGroup.of (rels := Lambda.rawRelationSet) g) = lambdaImage g := by
  change normalizedLambdaToInvolution
    (Lambda.normalizationEquiv (PresentedGroup.of (rels := Lambda.rawRelationSet) g)) = _
  rw [Lambda.normalizationEquiv_of, normalizedLambdaToInvolution_of]

/-- The final odd relation has exactly the intended role of identifying the
substituted original J with the fresh central generator. -/
theorem lambdaImage_J : lambdaImage 72 = J_star := by
  have h := InvolutionPresentation.word_product involutionPresentation none
  have hp : involutionPresentation.parity none = 1 := rfl
  rw [hp, ite_eq_left rfl] at h
  change ((InvolutionWords.block (72 : Lambda.Generator)).map ordinaryInvolution).prod = J_star at h
  rw [InvolutionWords.block_product] at h
  exact h

theorem lambdaToInvolution_J :
    lambdaToInvolution Lambda.JElement = J_star := by
  change lambdaToInvolution (PresentedGroup.of (rels := Lambda.rawRelationSet) 72) = J_star
  rw [lambdaToInvolution_of, lambdaImage_J]

end ThomGame.Construction
