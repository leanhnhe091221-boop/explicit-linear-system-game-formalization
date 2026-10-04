module

public import ThomGame.Construction.PaperExplicitDoubleBound
public import ThomGame.Construction.PaperGapUpperBound

/-!
# The two numerical corollaries for the manuscript's explicit game

The original construction, qualitative separation, and POVM bridge are unchanged.
The new quantitative proof supplies the literal double-exponential lower bound.
Both corollaries below are closed theorems, without certificate hypotheses.
-/

@[expose] public section
namespace ThomGame.Construction

/-- The exact classical value, including arbitrary shared randomness. -/
theorem paper_classical_value_corollary :
    paperGame.omegaC = 1 - (1 / 4251456 : ℝ) := paper_omegaC_eq

/-- The strictly positive explicit gap and its upper bound, for general POVMs.
The middle equality uses the existing perfect commuting strategy. -/
theorem paper_quantum_gap_corollary :
    0 < (1 / 2 : ℝ) ^ ((2 : ℕ) ^ 50003) ∧
    (1 / 2 : ℝ) ^ ((2 : ℕ) ^ 50003) ≤ 1 - paperGame.omegaQPOVM ∧
    1 - paperGame.omegaQPOVM = paperGame.omegaQcPOVM - paperGame.omegaQPOVM ∧
    1 - paperGame.omegaQPOVM ≤ (1 / 4251456 : ℝ) := by
  refine ⟨paperExplicitGap_pos,
    paper_explicit_povm_gap_of_double_bound paper_explicit_double_bound, ?_,
    paper_povm_quantumGap_bounds.2⟩
  rw [paper_omegaQcPOVM_eq_one]

end ThomGame.Construction
