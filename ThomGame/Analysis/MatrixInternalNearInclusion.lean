module

public import ThomGame.Analysis.MatrixNearInclusion
public import ThomGame.Analysis.MatrixQuotientExpectation

/-!
# Internal inclusion is equivalent to vanishing one-sided near inclusion

Choose actual maximizing contractions in the coordinate source algebras.
Their quotient lies in the target exactly when its expectation error
vanishes. Conversely, the uniform error controls every bounded source
representative. This proves Thom Lemma 2.2 for any filter.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

variable {ι : Type*} (dims : ι → Nat) [∀ k, NeZero (dims k)]
  (B A : (k : ι) → StarSubalgebra ℂ (CMatrix (dims k)))
  (hd : ∀ k, 0 < dims k) (L : Filter ι)

include hd

theorem matrixInternal_le_iff_nearInclusionError_tendsto :
    matrixInternalQuotient dims B L ≤ matrixInternalQuotient dims A L ↔
      Tendsto (fun k => matrixNearInclusionError (B k) (A k)) L (𝓝 0) := by
  constructor
  · intro hle
    choose X hXB hXnorm hXdist using fun k => exists_matrixNearInclusion_maximizer (B k) (A k)
    let R : BoundedMatrixSequence dims := ⟨X, 1, zero_le_one, hXnorm⟩
    have hR : matrixQuotientMk dims L R ∈ matrixInternalQuotient dims A L :=
      hle ((mem_matrixInternalQuotient dims B L _).mpr ⟨R, hXB, rfl⟩)
    have he := matrixQuotientExpectation_eq_self dims A hd L (matrixQuotientMk dims L R) hR
    rw [matrixQuotientExpectation_mk] at he
    have ht := (matrixQuotientMk_eq_iff dims L R (matrixSequenceExpectation dims A hd R)).mp he.symm
    have hfun : (fun k => hsNorm (R.val k - (matrixSequenceExpectation dims A hd R).val k)) =
        (fun k => matrixNearInclusionError (B k) (A k)) := funext hXdist
    rwa [hfun] at ht
  · intro ht x hx
    obtain ⟨R, hRB, rfl⟩ := (mem_matrixInternalQuotient dims B L x).mp hx
    obtain ⟨K, _, hK⟩ := BoundedMatrixSequence.bound dims R
    have hbound k : hsNorm (R.val k - (matrixSequenceExpectation dims A hd R).val k) ≤
        matrixNearInclusionError (B k) (A k) * K :=
      (matrixNearInclusionError_mem_bound (B k) (A k) (hRB k)).trans
        (mul_le_mul_of_nonneg_left (hK k) (matrixNearInclusionError_nonneg (B k) (A k)))
    have he : Tendsto (fun k => hsNorm (R.val k - (matrixSequenceExpectation dims A hd R).val k)) L (𝓝 0) :=
      squeeze_zero (fun k => hsNorm_nonneg _) hbound (by simpa only [zero_mul] using ht.mul_const K)
    rw [(matrixQuotientMk_eq_iff dims L R (matrixSequenceExpectation dims A hd R)).mpr he]
    exact (mem_matrixInternalQuotient dims A L _).mpr
      ⟨matrixSequenceExpectation dims A hd R, matrixSequenceExpectation_mem dims A hd R, rfl⟩

theorem exists_matrixNearInclusion_errors_of_internal_le
    (hle : matrixInternalQuotient dims B L ≤ matrixInternalQuotient dims A L) :
    ∃ ε : ι → ℝ, (∀ k, 0 ≤ ε k) ∧ Tendsto ε L (𝓝 0) ∧
      ∀ k, MatrixNearInclusion (B k) (A k) (ε k) := by
  refine ⟨fun k => matrixNearInclusionError (B k) (A k),
    fun k => matrixNearInclusionError_nonneg (B k) (A k),
    (matrixInternal_le_iff_nearInclusionError_tendsto dims B A hd L).mp hle, ?_⟩
  intro k
  exact (matrixNearInclusion_iff_error_le (B k) (A k) _).mpr le_rfl

theorem matrixInternal_le_of_nearInclusion_errors (ε : ι → ℝ) (hε : Tendsto ε L (𝓝 0))
    (hnear : ∀ k, MatrixNearInclusion (B k) (A k) (ε k)) :
    matrixInternalQuotient dims B L ≤ matrixInternalQuotient dims A L := by
  apply (matrixInternal_le_iff_nearInclusionError_tendsto dims B A hd L).mpr
  exact squeeze_zero (fun k => matrixNearInclusionError_nonneg (B k) (A k))
    (fun k => (matrixNearInclusion_iff_error_le (B k) (A k) (ε k)).mp (hnear k)) hε

end ThomGame.Analysis
