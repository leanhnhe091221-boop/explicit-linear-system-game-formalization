module

public import ThomGame.Analysis.MatrixQuotientExpectation

/-!
# Internal conditional expectations as Hilbert orthogonal projections

The closure of the internal trace vectors is a closed Hilbert subspace.
Its orthogonal projection agrees exactly with the coordinate expectation
on every bounded matrix class, for arbitrary index types and ultrafilters.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter

variable {ι : Type*} (dims : ι → Nat)
  (S : (i : ι) → StarSubalgebra ℂ (CMatrix (dims i)))
  (hd : ∀ i, 0 < dims i) (U : Ultrafilter ι)

noncomputable def matrixInternalTraceSubspace : Submodule ℂ (MatrixTraceHilbert dims hd U) :=
  ((matrixInternalQuotient dims S (U : Filter ι)).toSubalgebra.toSubmodule.map
    (matrixHilbertEmbedding dims hd U)).topologicalClosure

instance matrixInternalTraceSubspace_isClosed :
    IsClosed (matrixInternalTraceSubspace dims S hd U : Set (MatrixTraceHilbert dims hd U)) :=
  Submodule.isClosed_topologicalClosure _

theorem matrixHilbertEmbedding_mem_internalTraceSubspace
    (x : MatrixTracialQuotient dims (U : Filter ι))
    (hx : x ∈ matrixInternalQuotient dims S (U : Filter ι)) :
    matrixHilbertEmbedding dims hd U x ∈ matrixInternalTraceSubspace dims S hd U :=
  Submodule.le_topologicalClosure _ ⟨x, hx, rfl⟩

noncomputable def matrixHilbertExpectation :
    MatrixTraceHilbert dims hd U →L[ℂ] MatrixTraceHilbert dims hd U :=
  (matrixInternalTraceSubspace dims S hd U).starProjection

theorem matrixQuotientExpectation_residual_orthogonal
    (x : MatrixTracialQuotient dims (U : Filter ι)) :
    matrixHilbertEmbedding dims hd U x -
      matrixHilbertEmbedding dims hd U (matrixQuotientExpectation dims S hd (U : Filter ι) x) ∈
        (matrixInternalTraceSubspace dims S hd U)ᗮ := by
  unfold matrixInternalTraceSubspace
  rw [Submodule.orthogonal_closure]
  rintro y ⟨b, hb, rfl⟩
  rw [inner_sub_right, matrixHilbertEmbedding_inner, matrixHilbertEmbedding_inner,
    matrixQuotientExpectation_pairing dims S hd U x b hb, sub_self]

@[simp] theorem matrixHilbertExpectation_embedding
    (x : MatrixTracialQuotient dims (U : Filter ι)) :
    matrixHilbertExpectation dims S hd U (matrixHilbertEmbedding dims hd U x) =
      matrixHilbertEmbedding dims hd U (matrixQuotientExpectation dims S hd (U : Filter ι) x) :=
  (matrixInternalTraceSubspace dims S hd U).eq_starProjection_of_mem_orthogonal
    (matrixHilbertEmbedding_mem_internalTraceSubspace dims S hd U _
      (matrixQuotientExpectation_mem dims S hd (U : Filter ι) x))
    (matrixQuotientExpectation_residual_orthogonal dims S hd U x)

theorem matrixHilbertExpectation_norm_le : ‖matrixHilbertExpectation dims S hd U‖ ≤ 1 :=
  (matrixInternalTraceSubspace dims S hd U).starProjection_norm_le

theorem matrixHilbertExpectation_range :
    LinearMap.range (matrixHilbertExpectation dims S hd U).toLinearMap =
      matrixInternalTraceSubspace dims S hd U := by
  ext ξ
  constructor
  · rintro ⟨η, rfl⟩
    exact (matrixInternalTraceSubspace dims S hd U).starProjection_apply_mem η
  · intro hξ
    exact ⟨ξ, (matrixInternalTraceSubspace dims S hd U).starProjection_eq_self_iff.mpr hξ⟩

theorem matrixQuotientExpectation_pythagoras
    (x : MatrixTracialQuotient dims (U : Filter ι)) :
    ‖matrixHilbertEmbedding dims hd U x‖ ^ 2 =
      ‖matrixHilbertEmbedding dims hd U (matrixQuotientExpectation dims S hd (U : Filter ι) x)‖ ^ 2 +
      ‖matrixHilbertEmbedding dims hd U (x - matrixQuotientExpectation dims S hd (U : Filter ι) x)‖ ^ 2 := by
  have h := Submodule.norm_sq_eq_add_norm_sq_starProjection
    (matrixHilbertEmbedding dims hd U x) (matrixInternalTraceSubspace dims S hd U)
  rw [Submodule.starProjection_orthogonal_val] at h
  change ‖matrixHilbertEmbedding dims hd U x‖ ^ 2 =
    ‖matrixHilbertExpectation dims S hd U (matrixHilbertEmbedding dims hd U x)‖ ^ 2 +
    ‖matrixHilbertEmbedding dims hd U x -
      matrixHilbertExpectation dims S hd U (matrixHilbertEmbedding dims hd U x)‖ ^ 2 at h
  simpa only [matrixHilbertExpectation_embedding, map_sub] using h

theorem matrixQuotientExpectation_residualNorm_le
    (x : MatrixTracialQuotient dims (U : Filter ι)) :
    ‖matrixHilbertEmbedding dims hd U (x - matrixQuotientExpectation dims S hd (U : Filter ι) x)‖ ≤
      ‖matrixHilbertEmbedding dims hd U x‖ := by
  have h := matrixQuotientExpectation_pythagoras dims S hd U x
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  nlinarith [sq_nonneg ‖matrixHilbertEmbedding dims hd U
    (matrixQuotientExpectation dims S hd (U : Filter ι) x)‖]

theorem matrixQuotientExpectation_bestApproximation
    (x b : MatrixTracialQuotient dims (U : Filter ι))
    (hb : b ∈ matrixInternalQuotient dims S (U : Filter ι)) :
    ‖matrixHilbertEmbedding dims hd U (x - matrixQuotientExpectation dims S hd (U : Filter ι) x)‖ ≤
      ‖matrixHilbertEmbedding dims hd U (x - b)‖ := by
  have h := matrixQuotientExpectation_residualNorm_le dims S hd U (x - b)
  rw [(matrixQuotientExpectation dims S hd (U : Filter ι)).map_sub,
    matrixQuotientExpectation_eq_self dims S hd (U : Filter ι) b hb] at h
  simpa only [sub_sub_sub_cancel_right] using h

end ThomGame.Analysis
