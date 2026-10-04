module

public import ThomGame.Construction.UnconditionalApproximation
public import ThomGame.Construction.PaperOrderedSystem
public import ThomGame.Analysis.PaperSolutionApproximation

/-!
Unconditional central nontriviality and uniform approximate triviality for the
paper's actual increasing-column presentation, including its commutator conventions.
-/

@[expose] public section
namespace ThomGame.Construction

open Analysis

theorem paper_J_sigma_ne_one : paper_J_sigma ≠ 1 := by
  intro h
  apply J_sigma_ne_one
  rw [← paperSigmaEquiv_J, h, map_one]

/-- Every paper delta-representation is an engineering 4 delta-representation,
with exactly the same images of the free generators and in the same dimension. -/
theorem paper_approx_to_engineering {d : Nat} {δ : ℝ}
    (f : MatrixAssignment (SolutionGroup.Generator (Fin 1889684)) d)
    (hf : IsApproxRepresentation (SolutionGroup.Paper.relators paperSystem) δ f) :
    IsApproxRepresentation (SolutionGroup.relators numberedSystem) (4 * δ) f :=
  paper_ordered_approx_to_original numberedSystem f hf

theorem engineering_approx_to_paper {d : Nat} {δ : ℝ}
    (f : MatrixAssignment (SolutionGroup.Generator (Fin 1889684)) d)
    (hf : IsApproxRepresentation (SolutionGroup.relators numberedSystem) δ f) :
    IsApproxRepresentation (SolutionGroup.Paper.relators paperSystem) (4 * δ) f :=
  original_approx_to_paper_ordered numberedSystem f hf

theorem paperSigmaApproximatelyTrivial :
    ApproximatelyTrivial (SolutionGroup.Paper.relators paperSystem) (FreeGroup.of none) :=
  paper_ordered_approximatelyTrivial numberedSystem _ sigmaApproximatelyTrivial

theorem paperApproximation_conclusion :
    paper_J_sigma ≠ 1 ∧ ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ (d : Nat), 0 < d →
        ∀ f : MatrixAssignment (SolutionGroup.Generator (Fin 1889684)) d,
          IsApproxRepresentation (SolutionGroup.Paper.relators paperSystem) δ f →
            unitaryLength (f (FreeGroup.of none)) < η :=
  ⟨paper_J_sigma_ne_one, paperSigmaApproximatelyTrivial⟩

theorem paperApproximation_hsNorm :
    paper_J_sigma ≠ 1 ∧ ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ (d : Nat), 0 < d →
        ∀ f : MatrixAssignment (SolutionGroup.Generator (Fin 1889684)) d,
          IsApproxRepresentation (SolutionGroup.Paper.relators paperSystem) δ f →
            hsNorm ((f (FreeGroup.of none)).val - 1) < η :=
  paperApproximation_conclusion

theorem paper_uniform_no_negative_J :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (d : Nat), 0 < d →
      ∀ f : MatrixAssignment (SolutionGroup.Generator (Fin 1889684)) d,
        IsApproxRepresentation (SolutionGroup.Paper.relators paperSystem) δ f →
          f (FreeGroup.of none) ≠ -1 :=
  approximatelyTrivial_no_neg_one _ _ paperSigmaApproximatelyTrivial

end ThomGame.Construction
