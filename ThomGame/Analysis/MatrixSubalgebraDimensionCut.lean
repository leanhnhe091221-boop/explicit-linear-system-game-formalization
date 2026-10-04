module

public import ThomGame.Analysis.MatrixBlockDimensionTrimming
public import ThomGame.Analysis.MatrixSubalgebraCutProjections
public import ThomGame.Analysis.MatrixProductCornerCompression

/-!
# An actual algebraic dimension cut with a uniform slack bound

For every target d at most m, a subalgebra of M_m has a compression to
k at most d with d-k=e and e^2 at most (m-d)m. This estimate vanishes
with the relative dimension change even when the dimensions stay bounded.
The compressed unit ball is exactly the image of the original unit ball.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {m : Nat} (A : StarSubalgebra ℂ (CMatrix m)) (d : Nat)

theorem exists_matrixSubalgebra_dimension_projections (hd : d ≤ m) :
    ∃ (P Q : CMatrix m) (e : Nat),
      IsStarProjection P ∧ IsStarProjection Q ∧ P ∈ A ∧
      Q ∈ StarSubalgebra.centralizer ℂ (A : Set (CMatrix m)) ∧ Commute P Q ∧
      (P * Q).rank + e = d ∧ e ^ 2 ≤ (m - d) * m := by
  obtain ⟨R⟩ := exists_matrixSubalgebraStarBlocks A
  have hdim := matrixStarRepresentation_dimension A R A.subtype
  have hs := matrixStarRepresentationMultiplicity_pos A R A.subtype Subtype.val_injective
  obtain ⟨r, s, e, hr, ht, he, heb⟩ := exists_matrixBlocks_trim_relative R.size
    (matrixStarRepresentationMultiplicity A R A.subtype) d R.size_pos hs (by omega)
  refine ⟨matrixSubalgebraFactorCut A R r, matrixSubalgebraMultiplicityCut A R s, e,
    matrixSubalgebraFactorCut_projection A R r, matrixSubalgebraMultiplicityCut_projection A R s,
    matrixSubalgebraFactorCut_mem A R r, matrixSubalgebraMultiplicityCut_mem A R s,
    matrixSubalgebraCuts_commute A R r s, ?_, ?_⟩
  · rwa [matrixSubalgebraCuts_product_rank A R r s hr ht]
  · rwa [← hdim] at heb

structure MatrixSubalgebraDimensionCut where
  size : Nat
  slack : Nat
  size_add_slack : size + slack = d
  slack_sq_le : slack ^ 2 ≤ (m - d) * m
  frame : Matrix (Fin m) (Fin size) ℂ
  initial : frameᴴ * frame = 1
  algebra : StarSubalgebra ℂ (CMatrix size)
  compression_mem : ∀ X ∈ A, frameᴴ * X * frame ∈ algebra
  contraction_lift : ∀ Y ∈ algebra, matrixOpNorm Y ≤ 1 →
    ∃ X ∈ A, matrixOpNorm X ≤ 1 ∧ frameᴴ * X * frame = Y

theorem exists_matrixSubalgebraDimensionCut (hd : d ≤ m) : Nonempty (MatrixSubalgebraDimensionCut A d) := by
  obtain ⟨P, Q, e, hP, hQ, hPA, hQA, hcomm, he, heb⟩ := exists_matrixSubalgebra_dimension_projections A d hd
  let hPQ := hP.mul hQ hcomm
  let F := matrixProjectionFinFrame hPQ
  have hFi : Fᴴ * F = 1 := matrixProjectionFinFrame_initial hPQ
  have hFf : F * Fᴴ = P * Q := matrixProjectionFinFrame_final hPQ
  exact ⟨⟨(P * Q).rank, e, he, heb, F, hFi,
    (matrixProductCornerRepresentation A hP hQA F hFi hFf).range,
    matrixProductCorner_compression_mem A hP hPA hQA F hFi hFf,
    matrixProductCorner_contraction_lift A hP hQA F hFi hFf⟩⟩

variable (S : MatrixSubalgebraDimensionCut A d)

theorem matrixSubalgebraDimensionCut_size_le : S.size ≤ d := by have h := S.size_add_slack; omega

theorem matrixSubalgebraDimensionCut_unitBall_image :
    (fun X : CMatrix m => S.frameᴴ * X * S.frame) '' {X : CMatrix m | X ∈ A ∧ matrixOpNorm X ≤ 1} =
      {Y : CMatrix S.size | Y ∈ S.algebra ∧ matrixOpNorm Y ≤ 1} := by
  ext Y
  constructor
  · rintro ⟨X, ⟨hX, hn⟩, rfl⟩
    exact ⟨S.compression_mem X hX, (matrixFrameCompression_opNorm_le S.frame S.initial X).trans hn⟩
  · rintro ⟨hY, hn⟩
    obtain ⟨X, hX, hXn, he⟩ := S.contraction_lift Y hY hn
    exact ⟨X, ⟨hX, hXn⟩, he⟩

theorem matrixSubalgebraDimensionCut_complement_trace (hd : d ≤ m) :
    matrixTraceReal m (1 - S.frame * S.frameᴴ) = ((m - d : Nat) + (S.slack : ℝ)) / m := by
  have hp := matrixFrame_final_projection S.frame S.initial
  have hr : (S.frame * S.frameᴴ).rank = S.size := by
    rw [Matrix.rank_self_mul_conjTranspose, ← Matrix.rank_conjTranspose_mul_self S.frame, S.initial, Matrix.rank_one]
    exact Fintype.card_fin _
  have hc := matrixProjection_rank_one_sub_add hp
  have he := S.size_add_slack
  have hc' : (1 - S.frame * S.frameᴴ).rank = m - d + S.slack := by
    simp only [Fintype.card_fin] at hc
    omega
  rw [matrixTraceReal_projection_rank m hp.one_sub, hc', Nat.cast_add]

end ThomGame.Analysis
