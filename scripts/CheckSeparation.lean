import ThomGame.Construction.NonlocalGameSeparation
import Lean.Util.CollectAxioms

/-! A focused semantic and axiom check for the existence of a nonlocal-game
separation. Run after building ThomGame.Construction.NonlocalGameSeparation.
Only definitions and theorem types are printed; proof terms are omitted. -/

set_option autoImplicit false
set_option pp.proofs false

open ThomGame ThomGame.Quantum

-- Game, probability arrays, and expected payoff.
#print CorrelationTable
#print FiniteGame
#print FiniteGame.answerScore
#print FiniteGame.success

-- General POVMs and the finite-dimensional tensor-product Born rule.
#print POVM
#print LocalSpace
#print BipartiteSpace
#print FinitePOVMStrategy
#print FinitePOVMStrategy.correlation

-- Arbitrary complete Hilbert spaces, with cross-player commutation only.
#print CommutingPOVMStrategy
#print CommutingPOVMStrategy.correlation

-- All allowed correlations, followed by the actual suprema.
#print povmQuantumCorrelations
#print povmCommutingCorrelations
#print FiniteGame.value
#print FiniteGame.omegaQPOVM
#print FiniteGame.omegaQcPOVM

-- Choosing coordinates does not restrict the finite-dimensional Hilbert spaces.
#check @FinitePOVMStrategy.exists_coordinates

namespace SeparationCheck

-- Check the requested statement explicitly, rather than only looking up its name.
theorem separation :
    ∃ (X Y A B : Type) (_ : Fintype X) (_ : Fintype Y)
      (_ : Fintype A) (_ : Fintype B) (G : FiniteGame X Y A B),
      (∀ x y a b, G.payoff x y a b = 0 ∨ G.payoff x y a b = 1) ∧
      G.omegaQcPOVM = 1 ∧ G.omegaQPOVM < 1 :=
  exists_finiteGame_povm_quantum_commuting_separation

-- The binary-game witness also has four nonempty alphabets.
-- No new analytic argument is needed.
theorem binary_separation :
    ∃ (X Y A B : Type) (_ : Fintype X) (_ : Fintype Y)
      (_ : Fintype A) (_ : Fintype B) (G : FiniteGame X Y A B),
      Nonempty X ∧ Nonempty Y ∧ Nonempty A ∧ Nonempty B ∧
      (∀ x y a b, G.payoff x y a b = 0 ∨ G.payoff x y a b = 1) ∧
      G.omegaQcPOVM = 1 ∧ G.omegaQPOVM < 1 := by
  classical
  obtain ⟨hQ, hQa, hQc⟩ := Construction.paper_main_results_povm.2.2
  refine ⟨Fin 1417152, Fin 1889684, Fin 3 → ZMod 2, ZMod 2,
    inferInstance, inferInstance, inferInstance, inferInstance,
    Construction.paperGame, inferInstance, inferInstance, inferInstance, inferInstance,
    ?_, hQc, hQ.trans_lt hQa⟩
  intro x y a b
  change (if _ then (1 : ℝ) else 0) = 0 ∨ (if _ then (1 : ℝ) else 0) = 1
  split <;> simp_all

#print separation
#print binary_separation
#print axioms separation
#print axioms binary_separation
#print axioms FinitePOVMStrategy.exists_coordinates

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets : Array Name := #[``separation, ``binary_separation,
    ``FinitePOVMStrategy.exists_coordinates]
  for name in targets do
    for ax in (← collectAxioms name) do
      unless allowed.contains ax do
        throwError "Unexpected axiom in {name}: {ax}"
  logInfo "Separation check passed: explicit statements, nonempty binary game, and standard axioms only."

end SeparationCheck
