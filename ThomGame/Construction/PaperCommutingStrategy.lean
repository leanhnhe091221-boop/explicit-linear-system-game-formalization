module

public import ThomGame.Construction.PaperGame
public import ThomGame.Construction.PaperApproximation
public import ThomGame.Quantum.RegularSolutionStrategy

/-! The paper's actual perfect commuting strategy and commuting value one. -/

@[expose] public section
namespace ThomGame.Construction

open Quantum

noncomputable def paperCommutingStrategy :
    CommutingStrategy (Fin 1417152) (Fin 1889684) (Fin 3 → ZMod 2) (ZMod 2)
      (GroupHilbert (SolutionGroup.Paper.GroupOf paperSystem)) :=
  regularSolutionStrategy paperSystem paper_J_sigma_ne_one

theorem paperCommutingStrategy_state :
    paperCommutingStrategy.state =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
        (GroupHilbert.delta 1 - GroupHilbert.delta paper_J_sigma) := rfl

theorem paperCommutingStrategy_rejected_zero
    (r : Fin 1417152) (i : Fin 3) (a : Fin 3 → ZMod 2) (b : ZMod 2)
    (h : ¬ ((∑ j, a j = paperSystem.rhs r) ∧ a i = b)) :
    paperCommutingStrategy.correlation r (paperSystem.column r i) a b = 0 :=
  regularSolutionStrategy_rejected_zero paperSystem paper_J_sigma_ne_one r i a b h

theorem paperCommutingStrategy_perfect :
    paperGame.success paperCommutingStrategy.correlation = 1 :=
  regularSolutionStrategy_perfect paperSystem paper_J_sigma_ne_one

theorem paper_omegaQc_eq_one : paperGame.omegaQc = 1 :=
  paperGame.omegaQc_eq_one_of_perfect paperCommutingStrategy paperCommutingStrategy_perfect

theorem paper_values_with_perfect_commuting :
    0 ≤ paperGame.omegaQ ∧ paperGame.omegaQ = paperGame.omegaQa ∧
      paperGame.omegaQa ≤ 1 ∧ paperGame.omegaQc = 1 :=
  ⟨paperGame.omegaQ_nonneg, paper_omegaQ_eq_omegaQa,
    paperGame.omegaQa_le_one, paper_omegaQc_eq_one⟩

end ThomGame.Construction
