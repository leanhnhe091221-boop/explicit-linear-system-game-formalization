import ThomGame.Construction.PaperValueCorollaries
import Lean.Util.CollectAxioms

set_option autoImplicit false

open ThomGame.Construction ThomGame.Analysis ThomGame.Quantum

-- These examples have no spectral-gap, certificate, or quantitative-bound hypotheses.
example : paperGame.omegaC = 1 - (1 / 4251456 : ℝ) :=
  paper_classical_value_corollary

example :
    0 < (1 / 2 : ℝ) ^ ((2 : ℕ) ^ 50003) ∧
    (1 / 2 : ℝ) ^ ((2 : ℕ) ^ 50003) ≤ 1 - paperGame.omegaQPOVM ∧
    1 - paperGame.omegaQPOVM = paperGame.omegaQcPOVM - paperGame.omegaQPOVM ∧
    1 - paperGame.omegaQPOVM ≤ (1 / 4251456 : ℝ) :=
  paper_quantum_gap_corollary

#check paper_classical_value_corollary
#check paper_quantum_gap_corollary
#print axioms paper_classical_value_corollary
#print axioms paper_quantum_gap_corollary

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``paper_classical_value_corollary, ``paper_quantum_gap_corollary] do
    for ax in (← collectAxioms name) do
      unless allowed.contains ax do
        throwError "Unexpected axiom in {name}: {ax}"
  logInfo "Both unconditional numerical corollaries passed the recursive axiom audit."
