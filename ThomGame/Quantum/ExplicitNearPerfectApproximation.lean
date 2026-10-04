module

public import ThomGame.Quantum.ExplicitNearPerfectUnitaryRelations

/-! A fully explicit sufficient game-loss budget for the existing solution-group
approximation, including the exact negative central generator. -/

@[expose] public section
namespace ThomGame.SparseSystem

open Quantum Analysis

variable {R C : Type*} [Fintype R] [Nonempty R] [Fintype C] [LinearOrder C]
    (S : SparseSystem R C)

theorem near_perfect_approximation_explicit {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hbudget : 2 * systemDensityBudget R ε ≤ (δ / 9) ^ 2)
    (T : FiniteStrategy R C (Fin 3 → ZMod 2) (ZMod 2))
    (hT : 1 - ε ≤ S.incidenceGame.success T.correlation) :
    ∃ d : Nat, 0 < d ∧ ∃ f : MatrixAssignment (SolutionGroup.Generator C) d,
      IsApproxRepresentation (SolutionGroup.Paper.relators S) δ f ∧
        f (FreeGroup.of none) = -1 := by
  obtain ⟨d, hd, x, hs, hr, hc⟩ :=
    S.near_perfect_unitary_relations_explicit hε hδ hbudget T hT
  exact ⟨d, hd, negativeCentralAssignment x,
    negativeCentralAssignment_isApprox S x hδ.le hs hr hc, negativeCentralAssignment_none x⟩

end ThomGame.SparseSystem
