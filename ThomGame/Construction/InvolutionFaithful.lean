module

public import ThomGame.Construction.InvolutionGroup
public import ThomGame.Groups.InvolutionPermutation
public import ThomGame.Finite.WordHom

/-!
# Injectivity of the actual involution substitution Λ → K

The permutation model on Λ × Bool factors the faithful regular representation
through K. It therefore proves injectivity of the specified substitution,
including preservation of the original central involution. This is the k=2
case needed from Slofstra's Proposition 4.3, proved directly rather than assumed.
-/

@[expose] public section
namespace ThomGame.Construction

abbrev LambdaPermutation := Equiv.Perm (Lambda.GroupLambda × Bool)

noncomputable def lambdaGeneratorReversal (g : Lambda.Generator) :
    InvolutionPermutation.Reversal (Lambda.ofGenerator g) Lambda.JElement :=
  InvolutionPermutation.reversal (Lambda.ofGenerator g) Lambda.JElement
    (Lambda.JElement_commutes_generator g).symm Lambda.JElement_square

noncomputable def ordinaryPermutation : Ordinary → LambdaPermutation
  | (g, false) => (lambdaGeneratorReversal g).u
  | (g, true) => (lambdaGeneratorReversal g).v

theorem ordinaryPermutation_square (s : Ordinary) :
    ordinaryPermutation s * ordinaryPermutation s = 1 := by
  rcases s with ⟨g, b⟩
  cases b with
  | false => exact (lambdaGeneratorReversal g).u_square
  | true => exact (lambdaGeneratorReversal g).v_square

theorem ordinaryPermutation_commutes (s : Ordinary) :
    Commute (InvolutionPermutation.regular Lambda.JElement) (ordinaryPermutation s) := by
  rcases s with ⟨g, b⟩
  cases b with
  | false => exact (lambdaGeneratorReversal g).u_commutes
  | true =>
    exact (lambdaGeneratorReversal g).v_commutes
      (Lambda.JElement_commutes_generator g).symm

theorem ordinaryPermutation_pair (g : Lambda.Generator) :
    InvolutionWords.generatorImage ordinaryPermutation g =
      InvolutionPermutation.regular (Lambda.ofGenerator g) :=
  (lambdaGeneratorReversal g).pair_square

theorem sourceWord_eval (r : WheelIndex) :
    Word.eval Lambda.ofGenerator (sourceWord r) =
      if wheelFamily.parity r = 1 then Lambda.JElement else 1 := by
  cases r with
  | none => exact Word.eval_generator Lambda.ofGenerator 72
  | some i =>
    change Word.eval Lambda.ofGenerator (Lambda.normalizedRelators[i.val]'i.isLt) = 1
    exact (Lambda.all_normalized_iff_all_raw Lambda.ofGenerator).mpr Lambda.eval_rawRelator
      _ (List.getElem_mem i.isLt)

theorem ordinaryPermutation_word (r : WheelIndex) :
    ((wheelWord r).map ordinaryPermutation).prod =
      if wheelFamily.parity r = 1 then InvolutionPermutation.regular Lambda.JElement else 1 := by
  change ((InvolutionWords.substitute (sourceWord r)).map ordinaryPermutation).prod = _
  rw [InvolutionWords.substitute_product ordinaryPermutation ordinaryPermutation_square]
  have hf : InvolutionWords.generatorImage ordinaryPermutation =
      fun g => InvolutionPermutation.regular (Lambda.ofGenerator g) :=
    funext ordinaryPermutation_pair
  rw [hf, ← Word.map_eval, sourceWord_eval]
  split <;> simp

noncomputable def involutionPermutationModel :
    InvolutionPresentation.Model involutionPresentation LambdaPermutation where
  j := InvolutionPermutation.regular Lambda.JElement
  x := ordinaryPermutation
  j_square := by rw [← map_mul, Lambda.JElement_square, map_one]
  x_square := ordinaryPermutation_square
  j_commutes := ordinaryPermutation_commutes
  word_product := ordinaryPermutation_word

noncomputable def involutionToPermutation : InvolutionGroup →* LambdaPermutation :=
  involutionPermutationModel.toHom

theorem involutionToPermutation_x (s : Ordinary) :
    involutionToPermutation (ordinaryInvolution s) = ordinaryPermutation s :=
  involutionPermutationModel.toHom_x s

theorem involutionToPermutation_J :
    involutionToPermutation J_star = InvolutionPermutation.regular Lambda.JElement :=
  involutionPermutationModel.toHom_J

theorem involutionToPermutation_lambdaImage (g : Lambda.Generator) :
    involutionToPermutation (lambdaImage g) =
      InvolutionPermutation.regular (Lambda.ofGenerator g) := by
  change involutionToPermutation ((ordinaryInvolution (g, false) * ordinaryInvolution (g, true)) ^ 2) = _
  rw [map_pow, map_mul, involutionToPermutation_x, involutionToPermutation_x]
  exact ordinaryPermutation_pair g

theorem involutionToPermutation_comp_lambda :
    involutionToPermutation.comp lambdaToInvolution = InvolutionPermutation.regular := by
  apply PresentedGroup.ext
  intro g
  change involutionToPermutation (lambdaToInvolution
    (PresentedGroup.of (rels := Lambda.rawRelationSet) g)) = _
  rw [lambdaToInvolution_of, involutionToPermutation_lambdaImage]
  rfl

/-- The specified homomorphism from the actual raw Λ presentation is injective. -/
theorem lambdaToInvolution_injective : Function.Injective lambdaToInvolution := by
  intro x y h
  apply InvolutionPermutation.regular_injective
  calc
    InvolutionPermutation.regular x = involutionToPermutation (lambdaToInvolution x) :=
      (DFunLike.congr_fun involutionToPermutation_comp_lambda x).symm
    _ = involutionToPermutation (lambdaToInvolution y) := congrArg involutionToPermutation h
    _ = InvolutionPermutation.regular y := DFunLike.congr_fun involutionToPermutation_comp_lambda y

theorem J_star_eq_one_iff : J_star = 1 ↔ Lambda.JElement = 1 := by
  constructor
  · intro h
    apply lambdaToInvolution_injective
    rw [lambdaToInvolution_J, h, map_one]
  · intro h
    rw [← lambdaToInvolution_J, h, map_one]

end ThomGame.Construction
