module

public import ThomGame.Quantum.ReducedDensityMatrix
public import ThomGame.Quantum.FiniteStrategyRelations

/-! Concrete matrix versions of the near-perfect strategy estimates. -/

@[expose] public section
namespace ThomGame.Quantum.FiniteStrategy

open Analysis Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {R C : Type*} (T : FiniteStrategy R C (Fin 3 → ZMod 2) (ZMod 2))

noncomputable def bobMatrix (c : C) : CMatrix T.dimBob := localMatrix (T.localBobBit c)

noncomputable def bobUnitary (c : C) : UnitaryMatrix T.dimBob :=
  localMatrixUnitary (T.localBobBit c) (T.localBobBit_selfAdjoint c) (T.localBobBit_square c)

theorem bobUnitary_val (c : C) : (T.bobUnitary c).val = T.bobMatrix c := rfl

theorem bobMatrix_isHermitian (c : C) : Matrix.IsHermitian (T.bobMatrix c) :=
  localMatrix_isHermitian _ (T.localBobBit_selfAdjoint c)

theorem bobMatrix_square (c : C) : T.bobMatrix c * T.bobMatrix c = 1 := by
  rw [bobMatrix, ← localMatrix_mul, T.localBobBit_square, localMatrix_one]

theorem state_densityRoot_norm : rectHSNorm 1 (densityRoot T.state) = 1 := by
  rw [densityRoot_norm, T.norm_state]

theorem state_reducedDensity_trace : (reducedDensity T.state).trace = 1 := by
  rw [reducedDensity_trace, T.norm_state]
  norm_num

variable [Fintype R] [Nonempty R] [Fintype C] [LinearOrder C] (S : SparseSystem R C)

theorem near_perfect_density_commutator {ε : ℝ}
    (h : 1 - ε ≤ S.incidenceGame.success T.correlation) (r : R) (i : Fin 3) :
    rectHSNorm 1 (T.bobMatrix (S.column r i) * densityRoot T.state -
      densityRoot T.state * T.bobMatrix (S.column r i)) ≤
        2 * Real.sqrt 2 * Real.sqrt ((3 * (Fintype.card R : ℝ)) * ε) := by
  have hd := densityRoot_commutator_le T.state (T.localAliceBit r i) (T.localBobBit (S.column r i))
    (T.localAliceBit_selfAdjoint r i) (T.localAliceBit_square r i)
    (T.localBobBit_selfAdjoint _) (T.localBobBit_square _)
  rw [norm_sub_rev] at hd
  have hb := mul_le_mul_of_nonneg_left (T.near_perfect_local_consistency S h r i) (Real.sqrt_nonneg 2)
  exact hd.trans (by nlinarith only [hb])

theorem near_perfect_density_row {ε : ℝ}
    (h : 1 - ε ≤ S.incidenceGame.success T.correlation) (r : R) :
    rectHSNorm 1 ((T.bobMatrix (S.column r 0) * T.bobMatrix (S.column r 1) *
      T.bobMatrix (S.column r 2) - bitSign (S.rhs r) • 1) * densityRoot T.state) ≤
        8 * Real.sqrt ((3 * (Fintype.card R : ℝ)) * ε) := by
  simp only [bobMatrix, ← localMatrix_mul, densityRoot_weighted_sub_smul_norm]
  exact T.near_perfect_local_row S h r

theorem near_perfect_density_relation_commutator {ε : ℝ}
    (h : 1 - ε ≤ S.incidenceGame.success T.correlation) (r : R) (i j : Fin 3) :
    rectHSNorm 1 ((T.bobMatrix (S.column r i) * T.bobMatrix (S.column r j) -
      T.bobMatrix (S.column r j) * T.bobMatrix (S.column r i)) * densityRoot T.state) ≤
        8 * Real.sqrt ((3 * (Fintype.card R : ℝ)) * ε) := by
  simp only [bobMatrix, ← localMatrix_mul, ← localMatrix_sub, densityRoot_weighted_norm]
  exact T.near_perfect_local_commutator S h r i j

end ThomGame.Quantum.FiniteStrategy
