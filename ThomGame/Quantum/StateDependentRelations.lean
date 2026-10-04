module

public import ThomGame.Quantum.StateWordTransfer

/-! Dimension-independent state-dependent bounds for the actual row relations. -/

@[expose] public section
namespace ThomGame.Quantum.CommutingStrategy

variable {R C H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype R] [Nonempty R] [Fintype C] [LinearOrder C]
  (T : CommutingStrategy R C (Fin 3 → ZMod 2) (ZMod 2) H) (S : SparseSystem R C)

noncomputable def incidenceError : ℝ :=
  Real.sqrt ((3 * (Fintype.card R : ℝ)) * (1 - S.incidenceGame.success T.correlation))

theorem incidenceError_nonneg : 0 ≤ T.incidenceError S := Real.sqrt_nonneg _

theorem incidenceError_sq : (T.incidenceError S) ^ 2 =
    (3 * (Fintype.card R : ℝ)) * (1 - S.incidenceGame.success T.correlation) := by
  apply Real.sq_sqrt
  exact mul_nonneg (by positivity)
    (sub_nonneg.mpr (S.incidenceGame.success_le_one T.isProbabilityTable))

theorem consistency_error_le (r : R) (i : Fin 3) :
    ‖T.aliceBit r i T.state - T.bobBit (S.column r i) T.state‖ ≤ 2 * T.incidenceError S := by
  have h := T.consistency_error_sq_le_loss S r i
  have he := T.incidenceError_sq S
  have hp := T.incidenceError_nonneg S
  nlinarith [norm_nonneg (T.aliceBit r i T.state - T.bobBit (S.column r i) T.state)]

theorem parity_error_le (r : R) :
    ‖(T.aliceBit r 0 * T.aliceBit r 1 * T.aliceBit r 2) T.state -
      bitSign (S.rhs r) • T.state‖ ≤ 2 * T.incidenceError S := by
  have h := T.parity_error_sq_le_loss S r
  have he := T.incidenceError_sq S
  have hp := T.incidenceError_nonneg S
  nlinarith [norm_nonneg ((T.aliceBit r 0 * T.aliceBit r 1 * T.aliceBit r 2) T.state -
    bitSign (S.rhs r) • T.state)]

theorem bob_row_error_le (r : R) :
    ‖(T.bobBit (S.column r 0) * T.bobBit (S.column r 1) * T.bobBit (S.column r 2)) T.state -
      bitSign (S.rhs r) • T.state‖ ≤ 8 * T.incidenceError S := by
  have h := T.bob_triple_state_transfer S r
  have h0 := T.consistency_error_le S r 0
  have h1 := T.consistency_error_le S r 1
  have h2 := T.consistency_error_le S r 2
  have hp := T.parity_error_le S r
  have ht := norm_sub_le_norm_sub_add_norm_sub
    ((T.bobBit (S.column r 0) * T.bobBit (S.column r 1) * T.bobBit (S.column r 2)) T.state)
    ((T.aliceBit r 0 * T.aliceBit r 1 * T.aliceBit r 2) T.state)
    (bitSign (S.rhs r) • T.state)
  linarith

theorem bob_commutator_error_le (r : R) (i j : Fin 3) :
    ‖(T.bobBit (S.column r i) * T.bobBit (S.column r j)) T.state -
      (T.bobBit (S.column r j) * T.bobBit (S.column r i)) T.state‖ ≤ 8 * T.incidenceError S := by
  have hij := T.bob_pair_state_transfer S r i j
  have hji := T.bob_pair_state_transfer S r j i
  rw [(T.aliceBit_commute r j i).eq, norm_sub_rev] at hji
  have hi := T.consistency_error_le S r i
  have hj := T.consistency_error_le S r j
  have ht := norm_sub_le_norm_sub_add_norm_sub
    ((T.bobBit (S.column r i) * T.bobBit (S.column r j)) T.state)
    ((T.aliceBit r i * T.aliceBit r j) T.state)
    ((T.bobBit (S.column r j) * T.bobBit (S.column r i)) T.state)
  linarith

theorem incidenceError_le_of_near_perfect {ε : ℝ}
    (h : 1 - ε ≤ S.incidenceGame.success T.correlation) :
    T.incidenceError S ≤ Real.sqrt ((3 * (Fintype.card R : ℝ)) * ε) := by
  apply Real.sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem near_perfect_state_relations {ε : ℝ}
    (h : 1 - ε ≤ S.incidenceGame.success T.correlation) :
    (∀ r i, ‖T.aliceBit r i T.state - T.bobBit (S.column r i) T.state‖ ≤
      2 * Real.sqrt ((3 * (Fintype.card R : ℝ)) * ε)) ∧
    (∀ r, ‖(T.bobBit (S.column r 0) * T.bobBit (S.column r 1) *
      T.bobBit (S.column r 2)) T.state - bitSign (S.rhs r) • T.state‖ ≤
        8 * Real.sqrt ((3 * (Fintype.card R : ℝ)) * ε)) ∧
    (∀ r i j, ‖(T.bobBit (S.column r i) * T.bobBit (S.column r j)) T.state -
      (T.bobBit (S.column r j) * T.bobBit (S.column r i)) T.state‖ ≤
        8 * Real.sqrt ((3 * (Fintype.card R : ℝ)) * ε)) := by
  have he := T.incidenceError_le_of_near_perfect S h
  refine ⟨fun r i => (T.consistency_error_le S r i).trans ?_,
    fun r => (T.bob_row_error_le S r).trans ?_,
    fun r i j => (T.bob_commutator_error_le S r i j).trans ?_⟩
  all_goals exact mul_le_mul_of_nonneg_left he (by norm_num)

end ThomGame.Quantum.CommutingStrategy
