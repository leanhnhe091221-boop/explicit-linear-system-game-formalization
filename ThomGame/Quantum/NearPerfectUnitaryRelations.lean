module

public import ThomGame.Quantum.NearPerfectProjection
public import ThomGame.Analysis.MatrixUnitaryIntertwining
public import ThomGame.Analysis.MatrixProjectionNormalization

/-! Actual unitary matrices on the positive-rank common spectral subspace satisfy
all solution relations approximately in the normalized Hilbert--Schmidt norm. -/

@[expose] public section
namespace ThomGame.SparseSystem

open Quantum Analysis Matrix

variable {R C : Type*} [Fintype R] [Nonempty R] [Fintype C] [LinearOrder C]
    (S : SparseSystem R C)

theorem near_perfect_unitary_relations {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε > 0, ∀ T : FiniteStrategy R C (Fin 3 → ZMod 2) (ZMod 2),
      1 - ε ≤ S.incidenceGame.success T.correlation →
      ∃ k : Nat, 0 < k ∧ ∃ x : C → UnitaryMatrix k,
        (∀ c, hsNorm ((x c).val * (x c).val - 1) ≤ δ) ∧
        (∀ r, hsNorm ((x (S.column r 0)).val * (x (S.column r 1)).val *
          (x (S.column r 2)).val - bitSign (S.rhs r) • 1) ≤ δ) ∧
        (∀ r i j, hsNorm ((x (S.column r i)).val * (x (S.column r j)).val -
          (x (S.column r j)).val * (x (S.column r i)).val) ≤ δ) := by
  classical
  let η : ℝ := δ / 9
  have hη : 0 < η := div_pos hδ (by norm_num)
  obtain ⟨ε, hε, he⟩ := S.near_perfect_common_projection (sq_pos_of_pos hη)
  refine ⟨ε, hε, fun T hT => ?_⟩
  obtain ⟨P, hP0, hP, hg, hr, hc⟩ := he T hT
  let F := matrixProjectionFinFrame hP
  have hFi : Fᴴ * F = 1 := matrixProjectionFinFrame_initial hP
  have hFf : F * Fᴴ = P := matrixProjectionFinFrame_final hP
  have hg' (r : R) (i : Fin 3) :
      rectHSNorm P.rank (P * T.bobMatrix (S.column r i) - T.bobMatrix (S.column r i) * P) ≤ η :=
    rectHSNorm_rank_le_of_relative hP hP0 _ hη.le (hg r i)
  have hr' (r : R) : rectHSNorm P.rank (T.rowMatrixError S r * F) ≤ η :=
    (rectHSNorm_mul_frame_le_cut P.rank hFi hFf _).trans
      (rectHSNorm_rank_le_of_relative hP hP0 _ hη.le (hr r))
  have hc' (r : R) (i j : Fin 3) :
      rectHSNorm P.rank (T.commutatorMatrixError S r i j * F) ≤ η :=
    (rectHSNorm_mul_frame_le_cut P.rank hFi hFf _).trans
      (rectHSNorm_rank_le_of_relative hP hP0 _ hη.le (hc r i j))
  choose V hV using fun c => exists_matrixCompression_unitary P.rank hP hFi hFf (T.bobUnitary c)
  let x : C → UnitaryMatrix P.rank := fun c =>
    if ∃ r i, S.column r i = c then V c else 1
  have hx (r : R) (i : Fin 3) : x (S.column r i) = V (S.column r i) := by
    exact ite_eq_left ⟨r, i, rfl⟩
  have hi (r : R) (i : Fin 3) :
      matrixIntertwiningError P.rank F (T.bobUnitary (S.column r i)) (x (S.column r i)) ≤ 2 * η := by
    rw [hx]
    exact (hV _).trans (mul_le_mul_of_nonneg_left (hg' r i) (by norm_num))
  have hs (r : R) (i : Fin 3) :
      hsNorm ((x (S.column r i)).val * (x (S.column r i)).val - 1) ≤ 4 * η := by
    have hm := matrixIntertwiningError_mul_le P.rank F
      (T.bobUnitary (S.column r i)) (T.bobUnitary (S.column r i))
      (x (S.column r i)) (x (S.column r i))
    have ht := matrixIntertwiningError_relation_le P.rank F hFi
      (T.bobUnitary (S.column r i) * T.bobUnitary (S.column r i))
      (x (S.column r i) * x (S.column r i)) 1
    have hu : (T.bobUnitary (S.column r i) * T.bobUnitary (S.column r i)).val = 1 :=
      T.bobMatrix_square _
    simp only [hu, one_smul, sub_self, Matrix.zero_mul, rectHSNorm_zero, add_zero] at ht
    change hsNorm ((x (S.column r i)).val * (x (S.column r i)).val - 1) ≤ _ at ht
    have hb := hi r i
    linarith
  refine ⟨P.rank, matrixProjection_rank_pos hP hP0, x, ?_, ?_, ?_⟩
  · intro c
    by_cases ho : ∃ r i, S.column r i = c
    · obtain ⟨r, i, rfl⟩ := ho
      exact (hs r i).trans (by dsimp [η]; linarith)
    · have hx0 : x c = 1 := ite_eq_right ho
      simpa [hx0] using hδ.le
  · intro r
    have hm := matrixIntertwiningError_triple_le P.rank F
      (T.bobUnitary (S.column r 0)) (T.bobUnitary (S.column r 1)) (T.bobUnitary (S.column r 2))
      (x (S.column r 0)) (x (S.column r 1)) (x (S.column r 2))
    have ht := matrixIntertwiningError_relation_le P.rank F hFi
      (T.bobUnitary (S.column r 0) * T.bobUnitary (S.column r 1) * T.bobUnitary (S.column r 2))
      (x (S.column r 0) * x (S.column r 1) * x (S.column r 2)) (bitSign (S.rhs r))
    change hsNorm ((x (S.column r 0)).val * (x (S.column r 1)).val *
      (x (S.column r 2)).val - bitSign (S.rhs r) • 1) ≤
      _ + rectHSNorm P.rank (T.rowMatrixError S r * F) at ht
    have h0 := hi r 0
    have h1 := hi r 1
    have h2 := hi r 2
    have hb := hr' r
    dsimp only [η] at *
    linarith
  · intro r i j
    have hij := matrixIntertwiningError_mul_le P.rank F
      (T.bobUnitary (S.column r i)) (T.bobUnitary (S.column r j))
      (x (S.column r i)) (x (S.column r j))
    have hji := matrixIntertwiningError_mul_le P.rank F
      (T.bobUnitary (S.column r j)) (T.bobUnitary (S.column r i))
      (x (S.column r j)) (x (S.column r i))
    have ht := matrixIntertwiningError_difference_le P.rank F hFi
      (T.bobUnitary (S.column r i) * T.bobUnitary (S.column r j))
      (T.bobUnitary (S.column r j) * T.bobUnitary (S.column r i))
      (x (S.column r i) * x (S.column r j)) (x (S.column r j) * x (S.column r i))
    change hsNorm ((x (S.column r i)).val * (x (S.column r j)).val -
      (x (S.column r j)).val * (x (S.column r i)).val) ≤
      _ + _ + rectHSNorm P.rank (T.commutatorMatrixError S r i j * F) at ht
    have h0 := hi r i
    have h1 := hi r j
    have hb := hc' r i j
    dsimp only [η] at *
    linarith

end ThomGame.SparseSystem
