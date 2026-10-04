module

public import ThomGame.Construction.PaperGame
public import ThomGame.Quantum.FiniteStrategyRelations

/-! Explicit state-dependent relation bounds for the paper's finite-dimensional strategies. -/

@[expose] public section
namespace ThomGame.Construction

open Quantum

theorem paper_finite_strategy_consistency
    (T : FiniteStrategy (Fin 1417152) (Fin 1889684) (Fin 3 → ZMod 2) (ZMod 2))
    {ε : ℝ} (h : 1 - ε ≤ paperGame.success T.correlation)
    (r : Fin 1417152) (i : Fin 3) :
    ‖(T.localAliceBit r i).rTensor (LocalSpace T.dimBob) T.state -
      (T.localBobBit (paperSystem.column r i)).lTensor (LocalSpace T.dimAlice) T.state‖ ≤
        2 * Real.sqrt (4251456 * ε) := by
  simpa only [Fintype.card_fin, Nat.cast_ofNat, show (3 : ℝ) * 1417152 = 4251456 by norm_num]
    using T.near_perfect_local_consistency paperSystem h r i

theorem paper_finite_strategy_row
    (T : FiniteStrategy (Fin 1417152) (Fin 1889684) (Fin 3 → ZMod 2) (ZMod 2))
    {ε : ℝ} (h : 1 - ε ≤ paperGame.success T.correlation) (r : Fin 1417152) :
    ‖(T.localBobBit (paperSystem.column r 0) * T.localBobBit (paperSystem.column r 1) *
      T.localBobBit (paperSystem.column r 2)).lTensor (LocalSpace T.dimAlice) T.state -
        bitSign (paperSystem.rhs r) • T.state‖ ≤ 8 * Real.sqrt (4251456 * ε) := by
  simpa only [Fintype.card_fin, Nat.cast_ofNat, show (3 : ℝ) * 1417152 = 4251456 by norm_num]
    using T.near_perfect_local_row paperSystem h r

theorem paper_finite_strategy_commutator
    (T : FiniteStrategy (Fin 1417152) (Fin 1889684) (Fin 3 → ZMod 2) (ZMod 2))
    {ε : ℝ} (h : 1 - ε ≤ paperGame.success T.correlation)
    (r : Fin 1417152) (i j : Fin 3) :
    ‖(T.localBobBit (paperSystem.column r i) * T.localBobBit (paperSystem.column r j) -
      T.localBobBit (paperSystem.column r j) * T.localBobBit (paperSystem.column r i)).lTensor
        (LocalSpace T.dimAlice) T.state‖ ≤ 8 * Real.sqrt (4251456 * ε) := by
  simpa only [Fintype.card_fin, Nat.cast_ofNat, show (3 : ℝ) * 1417152 = 4251456 by norm_num]
    using T.near_perfect_local_commutator paperSystem h r i j

end ThomGame.Construction
