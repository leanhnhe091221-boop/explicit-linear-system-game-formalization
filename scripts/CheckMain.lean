import ThomGame.Construction.PaperQuantumGap
import ThomGame.Construction.PaperPOVMGap
import ThomGame.Construction.NonlocalGameSeparation
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option pp.universes true

-- Inspect the actual objects behind the final theorem, not only its name.
#print ThomGame.Construction.paperSystem
#print ThomGame.Construction.paperGame
#print ThomGame.SolutionGroup.Paper.relatorWord
#print ThomGame.SolutionGroup.Paper.relators
#print ThomGame.Analysis.MatrixAssignment
#print ThomGame.Analysis.IsApproxRepresentation
#print ThomGame.Analysis.hsNorm
#print ThomGame.Analysis.negativeCentralAssignment
#print ThomGame.Quantum.FiniteStrategy
#print ThomGame.Quantum.CommutingStrategy
#print ThomGame.Quantum.quantumCorrelations
#print ThomGame.Quantum.approximateQuantumCorrelations
#print ThomGame.Quantum.commutingCorrelations
#print ThomGame.Quantum.FiniteGame.success
#print ThomGame.Quantum.FiniteGame.value
#print ThomGame.Quantum.FiniteGame.omegaQ
#print ThomGame.Quantum.FiniteGame.omegaQa
#print ThomGame.Quantum.FiniteGame.omegaQc

#check @ThomGame.Analysis.exists_matrixCompression_unitary
#check @ThomGame.Analysis.matrixIntertwiningError_mul_le
#check @ThomGame.Analysis.matrixIntertwiningError_inv
#check @ThomGame.Analysis.matrixIntertwiningError_relation_le
#check @ThomGame.Analysis.matrixIntertwiningError_difference_le
#check @ThomGame.Analysis.rectHSNorm_rank_le_of_relative
#check @ThomGame.SparseSystem.near_perfect_unitary_relations
#check @ThomGame.Analysis.negativeCentralAssignment_isApprox
#check @ThomGame.SparseSystem.near_perfect_approximation
#check @ThomGame.Construction.paper_near_perfect_approximation
#check @ThomGame.Construction.paper_uniform_quantum_gap
#check @ThomGame.Construction.paper_omegaQ_lt_one
#check @ThomGame.Construction.paper_omegaQa_lt_one
#check @ThomGame.Construction.paper_quantum_value_separation
#check @ThomGame.Construction.paper_main_results

open ThomGame ThomGame.Analysis ThomGame.Quantum ThomGame.Construction

-- The matrix, the exceptional one-based row, and the question distribution.
example : Matrix (Fin 1417152) (Fin 1889684) (ZMod 2) := A
example : paperSystem.matrix = A := paperSystem_matrix
example : paperSystem.rhs = b := paperSystem_rhs
example (r : Fin 1417152) : b r = if r.val + 1 = 1417141 then 1 else 0 := b_formula r
example (r : Fin 1417152) (c : Fin 1889684) :
    paperGame.weight r c = if A r c = 1 then 1 / 4251456 else 0 := paperGame_weight r c

-- Normalization is by the actual positive compressed dimension.
example {d : Nat} {P : CMatrix d} (hP : IsStarProjection P) (hP0 : P ≠ 0)
    (X : CMatrix P.rank) {η : ℝ} (hη : 0 ≤ η)
    (hX : rectHSNorm 1 X ^ 2 ≤ η ^ 2 * rectHSNorm 1 P ^ 2) :
    0 < P.rank ∧ hsNorm X ≤ η :=
  ⟨matrixProjection_rank_pos hP hP0, rectHSNorm_rank_le_of_relative hP hP0 X hη hX⟩

-- The assignment is a genuine free-group homomorphism with J exactly -I.
example {C : Type*} {d : Nat} (x : C → UnitaryMatrix d) :
    ∃ f : FreeGroup (Option C) →* UnitaryMatrix d,
      f (FreeGroup.of none) = -1 ∧ ∀ c, f (FreeGroup.of (some c)) = x c :=
  ⟨negativeCentralAssignment x, negativeCentralAssignment_none x,
    negativeCentralAssignment_some x⟩

-- Tolerance is chosen before all strategy dimensions, and the output dimension is positive.
example (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε > 0, ∀ T : FiniteStrategy (Fin 1417152) (Fin 1889684) (Fin 3 → ZMod 2) (ZMod 2),
      1 - ε ≤ paperGame.success T.correlation →
      ∃ d : Nat, 0 < d ∧ ∃ f : MatrixAssignment (SolutionGroup.Generator (Fin 1889684)) d,
        IsApproxRepresentation (SolutionGroup.Paper.relators paperSystem) δ f ∧
          f (FreeGroup.of none) = -1 := paper_near_perfect_approximation hδ

example : ∃ ε : ℝ, 0 < ε ∧
    ∀ T : FiniteStrategy (Fin 1417152) (Fin 1889684) (Fin 3 → ZMod 2) (ZMod 2),
      paperGame.success T.correlation < 1 - ε := paper_uniform_quantum_gap

example : paperGame.success paperCommutingStrategy.correlation = 1 :=
  paperCommutingStrategy_perfect

example : paperGame.omegaQ = paperGame.omegaQa ∧ paperGame.omegaQa < 1 ∧ paperGame.omegaQc = 1 :=
  paper_quantum_value_separation

example : paper_J_sigma ≠ 1 ∧
    (∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ d : Nat, 0 < d →
        ∀ f : MatrixAssignment (SolutionGroup.Generator (Fin 1889684)) d,
          IsApproxRepresentation (SolutionGroup.Paper.relators paperSystem) δ f →
            hsNorm ((f (FreeGroup.of none)).val - 1) < η) ∧
    paperGame.omegaQ = paperGame.omegaQa ∧ paperGame.omegaQa < 1 ∧ paperGame.omegaQc = 1 :=
  paper_main_results

#print axioms ThomGame.Construction.paper_main_results
#print axioms ThomGame.Construction.paper_quantum_value_separation
#print axioms ThomGame.Construction.paper_uniform_quantum_gap

-- The manuscript allows arbitrary POVMs. The new wrapper transfers the
-- unchanged core result using exact finite-dimensional dilation and inclusion.
example : paperGame.omegaQPOVM = paperGame.omegaQ := paperGame.omegaQPOVM_eq_omegaQ
example : paperGame.omegaQaPOVM = paperGame.omegaQa := paperGame.omegaQaPOVM_eq_omegaQa
example : paperGame.omegaQPOVM = paperGame.omegaQaPOVM ∧
    paperGame.omegaQaPOVM < 1 ∧ paperGame.omegaQcPOVM = 1 :=
  paper_povm_quantum_value_separation

#check ThomGame.Construction.paper_main_results_povm
#print axioms ThomGame.Construction.paper_main_results_povm
#print axioms ThomGame.Construction.paper_povm_quantum_value_separation

-- The existential statements quantify all four finite alphabets and the game.
#check ThomGame.Quantum.exists_finiteGame_quantum_commuting_separation
#check ThomGame.Quantum.exists_finiteGame_povm_quantum_commuting_separation
#print axioms ThomGame.Quantum.exists_finiteGame_quantum_commuting_separation
#print axioms ThomGame.Quantum.exists_finiteGame_povm_quantum_commuting_separation

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets : Array Name := #[
    ``ThomGame.Construction.paper_main_results,
    ``ThomGame.Construction.paper_main_results_povm,
    ``ThomGame.Quantum.exists_finiteGame_quantum_commuting_separation,
    ``ThomGame.Quantum.exists_finiteGame_povm_quantum_commuting_separation]
  for name in targets do
    for ax in (← collectAxioms name) do
      unless allowed.contains ax do
        throwError "Unexpected axiom in {name}: {ax}"
  logInfo "Original and POVM main theorems and existential corollaries passed the axiom audit."
