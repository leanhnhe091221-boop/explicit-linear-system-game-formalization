module

public import ThomGame.Construction.PaperOrderedSystem
public import ThomGame.Quantum.IncidenceGame
public import ThomGame.Quantum.NearPerfectStrategy

/-! The paper's actual finite game, its Born probabilities, and its three values. -/

@[expose] public section
namespace ThomGame.Construction

open Quantum
open scoped BigOperators

noncomputable def paperGame :
    FiniteGame (Fin 1417152) (Fin 1889684) (Fin 3 → ZMod 2) (ZMod 2) :=
  paperSystem.incidenceGame

theorem paperGame_weight (r : Fin 1417152) (c : Fin 1889684) :
    paperGame.weight r c = if A r c = 1 then 1 / 4251456 else 0 := by
  have h : c ∈ paperSystem.rowSupport r ↔ A r c = 1 :=
    (paperSystem.mem_rowSupport r c).trans (paperSystem_support r c).symm
  change (if c ∈ paperSystem.rowSupport r then
    (3 * (Fintype.card (Fin 1417152) : ℝ))⁻¹ else 0) = _
  simp only [h]
  norm_num

theorem paperGame_payoff (r : Fin 1417152) (i : Fin 3)
    (a : Fin 3 → ZMod 2) (b : ZMod 2) :
    paperGame.payoff r (paperSystem.column r i) a b = 1 ↔
      (∑ j, a j = paperSystem.rhs r) ∧ a i = b :=
  paperSystem.incidenceGame_payoff r i a b

theorem paperGame_success (p : CorrelationTable (Fin 1417152) (Fin 1889684)
    (Fin 3 → ZMod 2) (ZMod 2)) :
    paperGame.success p = (1 / 4251456 : ℝ) *
      ∑ r, ∑ i, ∑ a, ∑ b,
        (if paperSystem.Accepts r i a b then p r (paperSystem.column r i) a b else 0) := by
  simpa only [paperGame, Fintype.card_fin, Nat.cast_ofNat, one_div,
    show (3 : ℝ) * 1417152 = 4251456 by norm_num]
    using paperSystem.incidenceGame_success p

theorem paperGame_answer_counts :
    Fintype.card (Fin 3 → ZMod 2) = 8 ∧ Fintype.card (ZMod 2) = 2 := by
  norm_num [Fintype.card_fun]

theorem paper_omegaQ_eq_omegaQa : paperGame.omegaQ = paperGame.omegaQa :=
  paperGame.omegaQ_eq_omegaQa

theorem paper_values_bounds :
    0 ≤ paperGame.omegaQ ∧ paperGame.omegaQ ≤ paperGame.omegaQc ∧ paperGame.omegaQc ≤ 1 :=
  ⟨paperGame.omegaQ_nonneg, paperGame.omegaQ_le_omegaQc, paperGame.omegaQc_le_one⟩

theorem paper_omegaQ_eq_one_iff : paperGame.omegaQ = 1 ↔
    ∀ ε : ℝ, 0 < ε → ∃ S : FiniteStrategy (Fin 1417152) (Fin 1889684)
      (Fin 3 → ZMod 2) (ZMod 2), 1 - ε < paperGame.success S.correlation :=
  paperGame.omegaQ_eq_one_iff

end ThomGame.Construction
