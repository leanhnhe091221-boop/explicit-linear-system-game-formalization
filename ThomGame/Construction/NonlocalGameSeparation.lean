module

public import ThomGame.Construction.PaperPOVMGap

/-! Existence of a finite two-player nonlocal game with a binary payoff separating
the quantum and commuting values, as a direct corollary of the paper's main theorems. -/

@[expose] public section
namespace ThomGame.Quantum

/-- There exists a finite two-player nonlocal game with a binary payoff, commuting
value one and quantum value strictly below one. The alphabets are existentially quantified. -/
theorem exists_finiteGame_quantum_commuting_separation :
    ∃ (X Y A B : Type) (_ : Fintype X) (_ : Fintype Y)
      (_ : Fintype A) (_ : Fintype B) (G : FiniteGame X Y A B),
      (∀ x y a b, G.payoff x y a b = 0 ∨ G.payoff x y a b = 1) ∧
      G.omegaQc = 1 ∧ G.omegaQ < 1 := by
  classical
  obtain ⟨hQ, hQa, hQc⟩ := Construction.paper_main_results.2.2
  refine ⟨Fin 1417152, Fin 1889684, Fin 3 → ZMod 2, ZMod 2,
    inferInstance, inferInstance, inferInstance, inferInstance,
    Construction.paperGame, ?_, hQc, hQ.trans_lt hQa⟩
  intro x y a b
  change (if _ then (1 : ℝ) else 0) = 0 ∨ (if _ then (1 : ℝ) else 0) = 1
  split <;> simp_all

/-- The same existence result when both values allow arbitrary POVMs. -/
theorem exists_finiteGame_povm_quantum_commuting_separation :
    ∃ (X Y A B : Type) (_ : Fintype X) (_ : Fintype Y)
      (_ : Fintype A) (_ : Fintype B) (G : FiniteGame X Y A B),
      (∀ x y a b, G.payoff x y a b = 0 ∨ G.payoff x y a b = 1) ∧
      G.omegaQcPOVM = 1 ∧ G.omegaQPOVM < 1 := by
  classical
  obtain ⟨hQ, hQa, hQc⟩ := Construction.paper_main_results_povm.2.2
  refine ⟨Fin 1417152, Fin 1889684, Fin 3 → ZMod 2, ZMod 2,
    inferInstance, inferInstance, inferInstance, inferInstance,
    Construction.paperGame, ?_, hQc, hQ.trans_lt hQa⟩
  intro x y a b
  change (if _ then (1 : ℝ) else 0) = 0 ∨ (if _ then (1 : ℝ) else 0) = 1
  split <;> simp_all

end ThomGame.Quantum
