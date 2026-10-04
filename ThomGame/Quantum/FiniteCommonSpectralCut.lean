module

public import ThomGame.Quantum.FiniteDensityRelations
public import ThomGame.Analysis.MatrixCommonSpectralCut

/-! One actual nonzero projection for all relations of a near-perfect finite strategy. -/

@[expose] public section
namespace ThomGame.Quantum

open Analysis Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable def systemDensityBudget (R : Type*) [Fintype R] (ε : ℝ) : ℝ :=
  12 * (Fintype.card R : ℝ) * Real.sqrt 2 * Real.sqrt ((3 * (Fintype.card R : ℝ)) * ε) +
    640 * (Fintype.card R : ℝ) * ((3 * (Fintype.card R : ℝ)) * ε) + ε

theorem systemDensityBudget_pos (R : Type*) [Fintype R] {ε : ℝ} (hε : 0 < ε) :
    0 < systemDensityBudget R ε := by unfold systemDensityBudget; positivity

namespace FiniteStrategy

variable {R C : Type*} (T : FiniteStrategy R C (Fin 3 → ZMod 2) (ZMod 2)) (S : SparseSystem R C)

noncomputable def rowMatrixError (r : R) : CMatrix T.dimBob :=
  T.bobMatrix (S.column r 0) * T.bobMatrix (S.column r 1) * T.bobMatrix (S.column r 2) -
    bitSign (S.rhs r) • 1

noncomputable def commutatorMatrixError (r : R) (i j : Fin 3) : CMatrix T.dimBob :=
  T.bobMatrix (S.column r i) * T.bobMatrix (S.column r j) -
    T.bobMatrix (S.column r j) * T.bobMatrix (S.column r i)

noncomputable def relationMatrix : R ⊕ (R × Fin 3 × Fin 3) → CMatrix T.dimBob :=
  Sum.elim (T.rowMatrixError S) (fun p => T.commutatorMatrixError S p.1 p.2.1 p.2.2)

noncomputable def occurrenceUnitary (p : R × Fin 3) : UnitaryMatrix T.dimBob :=
  T.bobUnitary (S.column p.1 p.2)

variable [Fintype R] [Nonempty R] [Fintype C] [LinearOrder C]

theorem relationMatrix_weighted_norm_le {ε : ℝ}
    (h : 1 - ε ≤ S.incidenceGame.success T.correlation) (j : R ⊕ (R × Fin 3 × Fin 3)) :
    rectHSNorm 1 (T.relationMatrix S j * densityRoot T.state) ≤
      8 * Real.sqrt ((3 * (Fintype.card R : ℝ)) * ε) := by
  cases j with
  | inl r => exact T.near_perfect_density_row S h r
  | inr p => exact T.near_perfect_density_relation_commutator S h p.1 p.2.1 p.2.2

theorem total_density_error_le {ε : ℝ} (hε : 0 < ε)
    (h : 1 - ε ≤ S.incidenceGame.success T.correlation) :
    2 * (∑ p, rectHSNorm 1 (densityRoot T.state * (T.occurrenceUnitary S p).val -
      (T.occurrenceUnitary S p).val * densityRoot T.state)) +
    (∑ j, rectHSNorm 1 (T.relationMatrix S j * densityRoot T.state) ^ 2) ≤
      systemDensityBudget R ε := by
  let t := Real.sqrt ((3 * (Fintype.card R : ℝ)) * ε)
  have ht : t ^ 2 = (3 * (Fintype.card R : ℝ)) * ε := Real.sq_sqrt (by positivity)
  have hc : (∑ p, rectHSNorm 1 (densityRoot T.state * (T.occurrenceUnitary S p).val -
      (T.occurrenceUnitary S p).val * densityRoot T.state)) ≤
      ∑ _p : R × Fin 3, 2 * Real.sqrt 2 * t := by
    apply Finset.sum_le_sum
    intro p _
    change rectHSNorm 1 (densityRoot T.state * T.bobMatrix (S.column p.1 p.2) -
      T.bobMatrix (S.column p.1 p.2) * densityRoot T.state) ≤ _
    rw [rectHSNorm_sub_comm]
    exact T.near_perfect_density_commutator S h p.1 p.2
  have hr : (∑ j, rectHSNorm 1 (T.relationMatrix S j * densityRoot T.state) ^ 2) ≤
      ∑ _j : R ⊕ (R × Fin 3 × Fin 3), (8 * t) ^ 2 := by
    apply Finset.sum_le_sum
    intro j _
    exact (sq_le_sq₀ (rectHSNorm_nonneg _ _) (by positivity)).mpr
      (T.relationMatrix_weighted_norm_le S h j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hc hr
  unfold systemDensityBudget
  change _ ≤ 12 * (Fintype.card R : ℝ) * Real.sqrt 2 * t +
    640 * (Fintype.card R : ℝ) * ((3 * (Fintype.card R : ℝ)) * ε) + ε
  nlinarith only [hc, hr, ht, hε]

theorem near_perfect_common_spectralCut {ε : ℝ} (hε : 0 < ε)
    (h : 1 - ε ≤ S.incidenceGame.success T.correlation) :
    ∃ s > 0, matrixSquareSpectralCut (densityRoot T.state) s ≠ 0 ∧
      IsStarProjection (matrixSquareSpectralCut (densityRoot T.state) s) ∧
      (∀ r i, rectHSNorm 1 (matrixSquareSpectralCut (densityRoot T.state) s * T.bobMatrix (S.column r i) -
        T.bobMatrix (S.column r i) * matrixSquareSpectralCut (densityRoot T.state) s) ^ 2 ≤
          2 * systemDensityBudget R ε * rectHSNorm 1 (matrixSquareSpectralCut (densityRoot T.state) s) ^ 2) ∧
      (∀ j, rectHSNorm 1 (T.relationMatrix S j * matrixSquareSpectralCut (densityRoot T.state) s) ^ 2 ≤
        2 * systemDensityBudget R ε * rectHSNorm 1 (matrixSquareSpectralCut (densityRoot T.state) s) ^ 2) := by
  obtain ⟨s, hs, hz, hp, hu, hr⟩ := exists_common_matrixSpectralCut
    (densityRoot_nonneg T.state).isSelfAdjoint.isHermitian (T.state_densityRoot_norm)
    (T.occurrenceUnitary S) (T.relationMatrix S) (systemDensityBudget_pos R hε)
    (T.total_density_error_le S hε h)
  exact ⟨s, hs, hz, hp, fun r i => hu (r, i), hr⟩

end FiniteStrategy
end ThomGame.Quantum
