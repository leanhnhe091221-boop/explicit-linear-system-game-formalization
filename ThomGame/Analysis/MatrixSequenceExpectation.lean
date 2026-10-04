module

public import ThomGame.Analysis.MatrixConditionalExpectation
public import ThomGame.Analysis.MatrixInternalSequences

/-!
# Coordinate conditional expectations on bounded matrix sequences

Operator norm contraction preserves uniform boundedness, while the
normalized Hilbert--Schmidt contraction preserves every filter's null
ideal. These are the two bounds needed to descend the coordinate maps.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter

variable {ι : Type*} (dims : ι → Nat)
  (S : (i : ι) → StarSubalgebra ℂ (CMatrix (dims i))) (hd : ∀ i, 0 < dims i)

noncomputable def matrixSequenceExpectation :
    BoundedMatrixSequence dims →ₗ[ℂ] BoundedMatrixSequence dims := by
  letI (i : ι) : NeZero (dims i) := ⟨Nat.ne_of_gt (hd i)⟩
  exact {
    toFun A := ⟨fun i => matrixTraceProjection (S i) (A.val i), by
      obtain ⟨K, hK, hA⟩ := BoundedMatrixSequence.bound dims A
      exact ⟨K, hK, fun i => (matrixTraceProjection_matrixOpNorm_le (S i) (A.val i)).trans (hA i)⟩⟩
    map_add' A B := Subtype.ext (funext fun i => (matrixTraceProjection (S i)).map_add _ _)
    map_smul' c A := Subtype.ext (funext fun i => (matrixTraceProjection (S i)).map_smul c _) }

@[simp] theorem matrixSequenceExpectation_apply (A : BoundedMatrixSequence dims) (i : ι) [NeZero (dims i)] :
    (matrixSequenceExpectation dims S hd A).val i = matrixTraceProjection (S i) (A.val i) := rfl

theorem matrixSequenceExpectation_mem (A : BoundedMatrixSequence dims) :
    matrixSequenceExpectation dims S hd A ∈ matrixInternalSequences dims S := by
  intro i
  let : NeZero (dims i) := ⟨Nat.ne_of_gt (hd i)⟩
  exact matrixTraceProjection_mem (S i) (A.val i)

theorem matrixSequenceExpectation_eq_self (A : BoundedMatrixSequence dims)
    (hA : A ∈ matrixInternalSequences dims S) : matrixSequenceExpectation dims S hd A = A := by
  apply Subtype.ext
  funext i
  let : NeZero (dims i) := ⟨Nat.ne_of_gt (hd i)⟩
  exact matrixTraceProjection_eq_self (S i) (A.val i) (hA i)

@[simp] theorem matrixSequenceExpectation_one : matrixSequenceExpectation dims S hd 1 = 1 :=
  matrixSequenceExpectation_eq_self dims S hd 1 (matrixInternalSequences dims S).one_mem

@[simp] theorem matrixSequenceExpectation_idem (A : BoundedMatrixSequence dims) :
    matrixSequenceExpectation dims S hd (matrixSequenceExpectation dims S hd A) =
      matrixSequenceExpectation dims S hd A :=
  matrixSequenceExpectation_eq_self dims S hd _ (matrixSequenceExpectation_mem dims S hd A)

@[simp] theorem matrixSequenceExpectation_star (A : BoundedMatrixSequence dims) :
    matrixSequenceExpectation dims S hd (star A) = star (matrixSequenceExpectation dims S hd A) := by
  apply Subtype.ext
  funext i
  let : NeZero (dims i) := ⟨Nat.ne_of_gt (hd i)⟩
  exact matrixTraceProjection_star (S i) (A.val i)

theorem matrixSequenceExpectation_mul_left (A X : BoundedMatrixSequence dims)
    (hA : A ∈ matrixInternalSequences dims S) :
    matrixSequenceExpectation dims S hd (A * X) = A * matrixSequenceExpectation dims S hd X := by
  apply Subtype.ext
  funext i
  let : NeZero (dims i) := ⟨Nat.ne_of_gt (hd i)⟩
  exact matrixTraceProjection_mul_left (S i) (A.val i) (X.val i) (hA i)

theorem matrixSequenceExpectation_mul_right (X A : BoundedMatrixSequence dims)
    (hA : A ∈ matrixInternalSequences dims S) :
    matrixSequenceExpectation dims S hd (X * A) = matrixSequenceExpectation dims S hd X * A := by
  apply Subtype.ext
  funext i
  let : NeZero (dims i) := ⟨Nat.ne_of_gt (hd i)⟩
  exact matrixTraceProjection_mul_right (S i) (X.val i) (A.val i) (hA i)

theorem matrixSequenceExpectation_matrixOpNorm_le (A : BoundedMatrixSequence dims) (i : ι) :
    matrixOpNorm ((matrixSequenceExpectation dims S hd A).val i) ≤ matrixOpNorm (A.val i) := by
  let : NeZero (dims i) := ⟨Nat.ne_of_gt (hd i)⟩
  exact matrixTraceProjection_matrixOpNorm_le (S i) (A.val i)

theorem matrixSequenceExpectation_hsNorm_le (A : BoundedMatrixSequence dims) (i : ι) :
    hsNorm ((matrixSequenceExpectation dims S hd A).val i) ≤ hsNorm (A.val i) := by
  let : NeZero (dims i) := ⟨Nat.ne_of_gt (hd i)⟩
  exact matrixTraceProjection_hsNorm_le (S i) (A.val i)

theorem matrixSequenceExpectation_null (L : Filter ι) (A : BoundedMatrixSequence dims)
    (hA : A ∈ matrixNullIdeal dims L) :
    matrixSequenceExpectation dims S hd A ∈ matrixNullIdeal dims L :=
  squeeze_zero (fun _ => hsNorm_nonneg _)
    (matrixSequenceExpectation_hsNorm_le dims S hd A) hA

theorem matrixSequenceExpectation_trace (A : BoundedMatrixSequence dims) (i : ι) :
    normalizedTrace ((matrixSequenceExpectation dims S hd A).val i) = normalizedTrace (A.val i) := by
  let : NeZero (dims i) := ⟨Nat.ne_of_gt (hd i)⟩
  exact matrixTraceProjection_trace (S i) (A.val i)

theorem matrixSequenceExpectation_ultratrace (U : Ultrafilter ι) (A : BoundedMatrixSequence dims) :
    matrixSequenceUltratrace dims U (matrixSequenceExpectation dims S hd A) =
      matrixSequenceUltratrace dims U A := by
  unfold matrixSequenceUltratrace
  simp only [matrixSequenceExpectation_trace]

theorem matrixSequenceExpectation_pairing (U : Ultrafilter ι) (A B : BoundedMatrixSequence dims)
    (hB : B ∈ matrixInternalSequences dims S) :
    matrixSequenceUltratrace dims U (star B * matrixSequenceExpectation dims S hd A) =
      matrixSequenceUltratrace dims U (star B * A) := by
  unfold matrixSequenceUltratrace
  congr 1
  funext i
  let : NeZero (dims i) := ⟨Nat.ne_of_gt (hd i)⟩
  exact matrixTraceProjection_pairing (S i) (A.val i) (B.val i) (hB i)

end ThomGame.Analysis
