module

public import ThomGame.Quantum.NearPerfectUnitaryRelations
public import ThomGame.Analysis.NegativeCentralAssignment
public import ThomGame.Quantum.NearPerfectStrategy

/-! The Slofstra--Vidick reduction for the actual incidence game and free-group
approximate representations, uniformly over all finite strategy dimensions. -/

@[expose] public section
namespace ThomGame.SparseSystem

open Quantum Analysis

variable {R C : Type*} [Fintype R] [Nonempty R] [Fintype C] [LinearOrder C]
    (S : SparseSystem R C)

theorem near_perfect_approximation {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε > 0, ∀ T : FiniteStrategy R C (Fin 3 → ZMod 2) (ZMod 2),
      1 - ε ≤ S.incidenceGame.success T.correlation →
      ∃ d : Nat, 0 < d ∧ ∃ f : MatrixAssignment (SolutionGroup.Generator C) d,
        IsApproxRepresentation (SolutionGroup.Paper.relators S) δ f ∧
          f (FreeGroup.of none) = -1 := by
  obtain ⟨ε, hε, he⟩ := S.near_perfect_unitary_relations hδ
  refine ⟨ε, hε, fun T hT => ?_⟩
  obtain ⟨d, hd, x, hs, hr, hc⟩ := he T hT
  exact ⟨d, hd, negativeCentralAssignment x,
    negativeCentralAssignment_isApprox S x hδ.le hs hr hc, negativeCentralAssignment_none x⟩

theorem uniform_gap_of_no_negative_J
    (h : ∃ δ : ℝ, 0 < δ ∧ ∀ d : Nat, 0 < d →
      ∀ f : MatrixAssignment (SolutionGroup.Generator C) d,
        IsApproxRepresentation (SolutionGroup.Paper.relators S) δ f →
          f (FreeGroup.of none) ≠ -1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ T : FiniteStrategy R C (Fin 3 → ZMod 2) (ZMod 2),
      S.incidenceGame.success T.correlation < 1 - ε := by
  obtain ⟨δ, hδ, hn⟩ := h
  obtain ⟨ε, hε, he⟩ := S.near_perfect_approximation hδ
  refine ⟨ε, hε, fun T => ?_⟩
  by_contra ht
  obtain ⟨d, hd, f, hf, hj⟩ := he T (le_of_not_gt ht)
  exact hn d hd f hf hj

theorem omegaQ_lt_one_of_no_negative_J
    (h : ∃ δ : ℝ, 0 < δ ∧ ∀ d : Nat, 0 < d →
      ∀ f : MatrixAssignment (SolutionGroup.Generator C) d,
        IsApproxRepresentation (SolutionGroup.Paper.relators S) δ f →
          f (FreeGroup.of none) ≠ -1) :
    S.incidenceGame.omegaQ < 1 := by
  obtain ⟨ε, hε, he⟩ := S.uniform_gap_of_no_negative_J h
  exact S.incidenceGame.omegaQ_lt_one_of_uniform_gap ε hε (fun T => (he T).le)

theorem omegaQ_lt_one_of_approximatelyTrivial
    (h : ApproximatelyTrivial (SolutionGroup.Paper.relators S) (FreeGroup.of none)) :
    S.incidenceGame.omegaQ < 1 :=
  S.omegaQ_lt_one_of_no_negative_J (approximatelyTrivial_no_neg_one _ _ h)

end ThomGame.SparseSystem
