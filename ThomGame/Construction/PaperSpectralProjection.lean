module

public import ThomGame.Construction.PaperGame
public import ThomGame.Quantum.NearPerfectProjection

/-! A uniform common spectral projection for the actual paper game. -/

@[expose] public section
namespace ThomGame.Construction

open Quantum Analysis
open scoped Matrix.Norms.L2Operator

theorem paper_near_perfect_projection {κ : ℝ} (hκ : 0 < κ) :
    ∃ ε > 0, ∀ T : FiniteStrategy (Fin 1417152) (Fin 1889684) (Fin 3 → ZMod 2) (ZMod 2),
      1 - ε ≤ paperGame.success T.correlation →
      ∃ P : CMatrix T.dimBob, P ≠ 0 ∧ IsStarProjection P ∧
        (∀ r i, rectHSNorm 1 (P * T.bobMatrix (paperSystem.column r i) -
          T.bobMatrix (paperSystem.column r i) * P) ^ 2 ≤ κ * rectHSNorm 1 P ^ 2) ∧
        (∀ r, rectHSNorm 1 (T.rowMatrixError paperSystem r * P) ^ 2 ≤ κ * rectHSNorm 1 P ^ 2) ∧
        (∀ r i j, rectHSNorm 1 (T.commutatorMatrixError paperSystem r i j * P) ^ 2 ≤
          κ * rectHSNorm 1 P ^ 2) :=
  paperSystem.near_perfect_common_projection hκ

end ThomGame.Construction
