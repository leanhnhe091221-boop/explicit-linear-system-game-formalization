module

public import ThomGame.Analysis.MatrixCenterProjectionBound
public import ThomGame.Analysis.MatrixSequenceExpectation

/-!
# The center of an internal matrix algebra is the internal algebra of centers

Actual coordinate unitary witnesses detect distance from the center. Their
uniform operator bound is one, so centrality in the quotient makes the
center-projection error tend to zero. The statement holds for any filter.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology Matrix.Norms.L2Operator

variable {ι : Type*} (dims : ι → Nat)
  (S : (k : ι) → StarSubalgebra ℂ (CMatrix (dims k))) (hd : ∀ k, 0 < dims k) (L : Filter ι)

theorem matrixInternal_center_distance_tendsto (A : BoundedMatrixSequence dims)
    (hA : ∀ k, A.val k ∈ S k)
    (hcomm : ∀ B : BoundedMatrixSequence dims, (∀ k, B.val k ∈ S k) →
      Commute (matrixQuotientMk dims L B) (matrixQuotientMk dims L A)) :
    Tendsto (fun k => hsNorm (A.val k -
      (matrixSequenceExpectation dims (fun k => starSubalgebraCenter (S k)) hd A).val k)) L (𝓝 0) := by
  classical
  let (k : ι) : NeZero (dims k) := ⟨Nat.ne_of_gt (hd k)⟩
  have hex k : ∃ U : unitary (S k), hsNorm (A.val k - matrixTraceProjection (starSubalgebraCenter (S k)) (A.val k)) ≤
      2 * hsNorm ((matrixSubalgebraUnitary (S k) U).val * A.val k - A.val k * (matrixSubalgebraUnitary (S k) U).val) :=
    exists_matrixUnitary_detecting_center_distance (S k) (A.val k) (hA k)
  choose U hU using hex
  let B : BoundedMatrixSequence dims := ⟨fun k => (matrixSubalgebraUnitary (S k) (U k)).val,
    1, zero_le_one, fun k => matrixOpNorm_unitary_le (matrixSubalgebraUnitary (S k) (U k))⟩
  have hB : ∀ k, B.val k ∈ S k := fun k => (U k).val.property
  have he : matrixQuotientMk dims L (B * A) = matrixQuotientMk dims L (A * B) := by
    rw [map_mul, map_mul]
    exact (hcomm B hB).eq
  have ht := (matrixQuotientMk_eq_iff dims L (B * A) (A * B)).mp he
  have ht' := ht.const_mul 2
  rw [mul_zero] at ht'
  exact squeeze_zero (fun k => hsNorm_nonneg _) (fun k => hU k) ht'

omit hd in
theorem matrixInternalCenters_commute {x y : MatrixTracialQuotient dims L}
    (hx : x ∈ matrixInternalQuotient dims (fun k => starSubalgebraCenter (S k)) L)
    (hy : y ∈ matrixInternalQuotient dims S L) : Commute y x := by
  obtain ⟨A, hA, rfl⟩ := (mem_matrixInternalQuotient dims _ L x).mp hx
  obtain ⟨B, hB, rfl⟩ := (mem_matrixInternalQuotient dims S L y).mp hy
  show matrixQuotientMk dims L B * matrixQuotientMk dims L A =
    matrixQuotientMk dims L A * matrixQuotientMk dims L B
  rw [← map_mul, ← map_mul]
  apply congrArg (matrixQuotientMk dims L)
  apply Subtype.ext
  funext k
  exact ((mem_starSubalgebraCenter_iff (S k) (A.val k)).mp (hA k)).2 (B.val k) (hB k)

include hd in
theorem matrixInternalQuotient_center :
    starSubalgebraCenter (matrixInternalQuotient dims S L) =
      matrixInternalQuotient dims (fun k => starSubalgebraCenter (S k)) L := by
  ext x
  rw [mem_starSubalgebraCenter_iff]
  constructor
  · rintro ⟨hx, hcomm⟩
    obtain ⟨A, hA, rfl⟩ := (mem_matrixInternalQuotient dims S L x).mp hx
    have ht := matrixInternal_center_distance_tendsto dims S hd L A hA (fun B hB =>
      hcomm _ ((mem_matrixInternalQuotient dims S L _).mpr ⟨B, hB, rfl⟩))
    apply (mem_matrixInternalQuotient dims _ L _).mpr
    refine ⟨matrixSequenceExpectation dims (fun k => starSubalgebraCenter (S k)) hd A,
      matrixSequenceExpectation_mem dims (fun k => starSubalgebraCenter (S k)) hd A, ?_⟩
    exact ((matrixQuotientMk_eq_iff dims L A _).mpr ht).symm
  · intro hx
    refine ⟨?_, fun y hy => (matrixInternalCenters_commute dims S L hx hy).eq⟩
    obtain ⟨A, hA, rfl⟩ := (mem_matrixInternalQuotient dims _ L x).mp hx
    exact (mem_matrixInternalQuotient dims S L _).mpr
      ⟨A, fun k => starSubalgebraCenter_le (S k) (hA k), rfl⟩

end ThomGame.Analysis
