module

public import ThomGame.Quantum.GameValue
public import Mathlib.Tactic.Linarith

/-! Supremum-one means actual finite strategies approach perfect success. -/

@[expose] public section
namespace ThomGame.Quantum.FiniteGame

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Nonempty A] [Nonempty B] (G : FiniteGame X Y A B)

theorem omegaQ_eq_one_iff : G.omegaQ = 1 ↔
    ∀ ε : ℝ, 0 < ε → ∃ S : FiniteStrategy X Y A B, 1 - ε < G.success S.correlation := by
  constructor
  · intro h ε hε
    have hl : 1 - ε < G.omegaQ := by rw [h]; linarith
    obtain ⟨v, ⟨p, ⟨S, rfl⟩, rfl⟩, hv⟩ :=
      exists_lt_of_lt_csSup (quantumCorrelations_nonempty.image G.success) hl
    exact ⟨S, hv⟩
  · intro h
    apply le_antisymm G.omegaQ_le_one
    by_contra hn
    have hlt : G.omegaQ < 1 := lt_of_not_ge hn
    obtain ⟨S, hS⟩ := h (1 - G.omegaQ) (sub_pos.mpr hlt)
    have hs := G.finiteStrategy_success_le S
    linarith

theorem omegaQ_lt_one_of_uniform_gap (ε : ℝ) (hε : 0 < ε)
    (h : ∀ S : FiniteStrategy X Y A B, G.success S.correlation ≤ 1 - ε) :
    G.omegaQ < 1 := by
  have hv : G.omegaQ ≤ 1 - ε := by
    apply csSup_le (quantumCorrelations_nonempty.image G.success)
    rintro _ ⟨p, ⟨S, rfl⟩, rfl⟩
    exact h S
  linarith

theorem omegaQc_eq_one_of_perfect {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (S : CommutingStrategy X Y A B H)
    (h : G.success S.correlation = 1) : G.omegaQc = 1 := by
  apply le_antisymm G.omegaQc_le_one
  rw [← h]
  exact G.commutingStrategy_success_le S

end ThomGame.Quantum.FiniteGame
