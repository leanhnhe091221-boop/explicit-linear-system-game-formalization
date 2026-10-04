module

public import ThomGame.Construction.PaperQuantumGap
public import ThomGame.Quantum.POVMGameValue
public import ThomGame.Quantum.FinitePOVMCoordinates

/-! The manuscript's quantum conclusions with arbitrary POVMs.

This is a semantic wrapper around the existing projective-strategy proofs.
Finite local measurement dilation transfers the quantum and approximate quantum
values; the existing perfect commuting strategy is already a POVM strategy.
-/

@[expose] public section
namespace ThomGame.Construction

open Quantum Analysis

theorem paper_omegaQPOVM_lt_one : paperGame.omegaQPOVM < 1 := by
  rw [paperGame.omegaQPOVM_eq_omegaQ]
  exact paper_omegaQ_lt_one

theorem paper_omegaQaPOVM_lt_one : paperGame.omegaQaPOVM < 1 := by
  rw [paperGame.omegaQaPOVM_eq_omegaQa]
  exact paper_omegaQa_lt_one

theorem paper_omegaQcPOVM_eq_one : paperGame.omegaQcPOVM = 1 :=
  paperGame.omegaQcPOVM_eq_one_of_perfect paperCommutingStrategy
    paperCommutingStrategy_perfect

theorem paper_povm_quantum_value_separation :
    paperGame.omegaQPOVM = paperGame.omegaQaPOVM ∧
      paperGame.omegaQaPOVM < 1 ∧ paperGame.omegaQcPOVM = 1 := by
  refine ⟨?_, paper_omegaQaPOVM_lt_one, paper_omegaQcPOVM_eq_one⟩
  rw [paperGame.omegaQPOVM_eq_omegaQ, paperGame.omegaQaPOVM_eq_omegaQa]
  exact paper_omegaQ_eq_omegaQa

/-- The existing central-element conclusions and quantum separation, with the
quantum values now taken over the manuscript's general POVM strategies. -/
theorem paper_main_results_povm :
    paper_J_sigma ≠ 1 ∧
      (∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
        ∀ d : Nat, 0 < d →
          ∀ f : MatrixAssignment (SolutionGroup.Generator (Fin 1889684)) d,
            IsApproxRepresentation (SolutionGroup.Paper.relators paperSystem) δ f →
              hsNorm ((f (FreeGroup.of none)).val - 1) < η) ∧
      paperGame.omegaQPOVM = paperGame.omegaQaPOVM ∧
      paperGame.omegaQaPOVM < 1 ∧ paperGame.omegaQcPOVM = 1 :=
  ⟨paper_main_results.1, paper_main_results.2.1, paper_povm_quantum_value_separation⟩

end ThomGame.Construction
