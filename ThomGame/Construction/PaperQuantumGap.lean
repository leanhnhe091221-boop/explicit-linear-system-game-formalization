module

public import ThomGame.Construction.PaperCommutingStrategy
public import ThomGame.Quantum.NearPerfectApproximation

/-! Strict quantum separation for the paper's specified game, with all analytic
and group-theoretic hypotheses discharged. -/

@[expose] public section
namespace ThomGame.Construction

open Quantum Analysis

theorem paper_near_perfect_approximation {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε > 0, ∀ T : FiniteStrategy (Fin 1417152) (Fin 1889684) (Fin 3 → ZMod 2) (ZMod 2),
      1 - ε ≤ paperGame.success T.correlation →
      ∃ d : Nat, 0 < d ∧ ∃ f : MatrixAssignment (SolutionGroup.Generator (Fin 1889684)) d,
        IsApproxRepresentation (SolutionGroup.Paper.relators paperSystem) δ f ∧
          f (FreeGroup.of none) = -1 :=
  paperSystem.near_perfect_approximation hδ

theorem paper_uniform_quantum_gap :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ T : FiniteStrategy (Fin 1417152) (Fin 1889684) (Fin 3 → ZMod 2) (ZMod 2),
        paperGame.success T.correlation < 1 - ε :=
  paperSystem.uniform_gap_of_no_negative_J paper_uniform_no_negative_J

theorem paper_omegaQ_lt_one : paperGame.omegaQ < 1 :=
  paperSystem.omegaQ_lt_one_of_no_negative_J paper_uniform_no_negative_J

theorem paper_omegaQa_lt_one : paperGame.omegaQa < 1 := by
  rw [← paper_omegaQ_eq_omegaQa]
  exact paper_omegaQ_lt_one

theorem paper_quantum_value_separation :
    paperGame.omegaQ = paperGame.omegaQa ∧ paperGame.omegaQa < 1 ∧ paperGame.omegaQc = 1 :=
  ⟨paper_omegaQ_eq_omegaQa, paper_omegaQa_lt_one, paper_omegaQc_eq_one⟩

theorem paper_main_results :
    paper_J_sigma ≠ 1 ∧
      (∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
        ∀ d : Nat, 0 < d →
          ∀ f : MatrixAssignment (SolutionGroup.Generator (Fin 1889684)) d,
            IsApproxRepresentation (SolutionGroup.Paper.relators paperSystem) δ f →
              hsNorm ((f (FreeGroup.of none)).val - 1) < η) ∧
      paperGame.omegaQ = paperGame.omegaQa ∧ paperGame.omegaQa < 1 ∧ paperGame.omegaQc = 1 :=
  ⟨paperApproximation_hsNorm.1, paperApproximation_hsNorm.2, paper_quantum_value_separation⟩

end ThomGame.Construction
