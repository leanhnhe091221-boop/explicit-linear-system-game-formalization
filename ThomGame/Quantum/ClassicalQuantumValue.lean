module

public import ThomGame.Quantum.ClassicalGameValue

/-! Comparing the actual classical value with the actual finite quantum value. -/

@[expose] public section
namespace ThomGame.Quantum

variable {X Y A B : Type*} [Fintype A] [Fintype B]

theorem deterministicCorrelation_eq_quantum (alice : X → A) (bob : Y → B) :
    deterministicCorrelation alice bob = (FiniteStrategy.deterministic alice bob).correlation := by
  classical
  funext x y a b
  exact (FiniteStrategy.deterministic_correlation alice bob x y a b).symm

namespace FiniteGame

variable [Fintype X] [Fintype Y] [Nonempty A] [Nonempty B]

theorem omegaC_le_omegaQ (G : FiniteGame X Y A B) : G.omegaC ≤ G.omegaQ := by
  apply G.omegaC_le_of_deterministic
  intro alice bob
  rw [deterministicCorrelation_eq_quantum]
  exact G.finiteStrategy_success_le _

end FiniteGame
end ThomGame.Quantum
