module

public import ThomGame.Construction.PaperClassicalValue
public import ThomGame.Construction.PaperPOVMGap
public import ThomGame.Quantum.ClassicalQuantumValue

/-!
# The upper bound on the quantum gap

The classical strategy gives the numerical upper bound.  Positivity uses the
previously proved qualitative separation.  The specific double-exponential
lower bound is a separate quantitative assertion, not a consequence of this
module's positivity statement.
-/

@[expose] public section
namespace ThomGame.Construction

theorem paper_quantumGap_pos : 0 < 1 - paperGame.omegaQ :=
  sub_pos.mpr paper_omegaQ_lt_one

theorem paper_quantumGap_le_incidence_reciprocal :
    1 - paperGame.omegaQ ≤ (1 / 4251456 : ℝ) := by
  have h := paperGame.omegaC_le_omegaQ
  rw [paper_omegaC_eq] at h
  linarith

theorem paper_quantumGap_bounds :
    0 < 1 - paperGame.omegaQ ∧ 1 - paperGame.omegaQ ≤ (1 / 4251456 : ℝ) :=
  ⟨paper_quantumGap_pos, paper_quantumGap_le_incidence_reciprocal⟩

theorem paper_povm_quantumGap_bounds :
    0 < 1 - paperGame.omegaQPOVM ∧
      1 - paperGame.omegaQPOVM ≤ (1 / 4251456 : ℝ) := by
  rw [paperGame.omegaQPOVM_eq_omegaQ]
  exact paper_quantumGap_bounds

theorem paper_povm_separationGap_bounds :
    0 < paperGame.omegaQcPOVM - paperGame.omegaQPOVM ∧
      paperGame.omegaQcPOVM - paperGame.omegaQPOVM ≤ (1 / 4251456 : ℝ) := by
  rw [paper_omegaQcPOVM_eq_one]
  exact paper_povm_quantumGap_bounds

end ThomGame.Construction
