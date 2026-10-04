module

public import ThomGame.Analysis.MatrixQuotientExpectation
public import ThomGame.Analysis.MatrixRelativeCommutant

/-!
# The actual internal anchor and a scalar coordinate expectation

Commutation in normalized 2-norm gives membership in the genuine tuple
commutant. The stated internal intersection and coordinate expectation
then force the quotient element to be the specified scalar.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

variable {ι : Type*} (dims : ι → Nat) {h : Nat}
    (U : (n : ι) → Fin h → UnitaryMatrix (dims n)) (L : Filter ι)

theorem matrixQuotientMk_mem_relativeCommutant_of_tendsto (X : BoundedMatrixSequence dims)
    (hc : ∀ j, Tendsto (fun n => hsNorm (X.val n * (U n j).val - (U n j).val * X.val n)) L (𝓝 0)) :
    matrixQuotientMk dims L X ∈ matrixRelativeCommutant dims U L := by
  apply (mem_matrixRelativeCommutant_iff dims U L _).mpr
  intro j
  have he := (matrixQuotientMk_eq_iff dims L
    (X * boundedUnitarySequence dims (fun n => U n j))
    (boundedUnitarySequence dims (fun n => U n j) * X)).mpr (hc j)
  rw [map_mul, map_mul] at he
  exact he.symm

variable [∀ n, NeZero (dims n)]
    (A D : (n : ι) → StarSubalgebra ℂ (CMatrix (dims n)))
    (X : BoundedMatrixSequence dims) (c : ℂ)

theorem matrixQuotientAnchor_scalar
    (hanchor : matrixInternalQuotient dims A L ⊓ matrixRelativeCommutant dims U L =
      matrixInternalQuotient dims D L)
    (hXA : ∀ n, X.val n ∈ A n)
    (hc : ∀ j, Tendsto (fun n => hsNorm (X.val n * (U n j).val - (U n j).val * X.val n)) L (𝓝 0))
    (hE : ∀ n, matrixTraceProjection (D n) (X.val n) = c • 1) :
    matrixQuotientMk dims L X = c • 1 := by
  have hmem : matrixQuotientMk dims L X ∈ matrixInternalQuotient dims D L := by
    rw [← hanchor]
    exact ⟨(mem_matrixInternalQuotient dims A L _).mpr ⟨X, hXA, rfl⟩,
      matrixQuotientMk_mem_relativeCommutant_of_tendsto dims U L X hc⟩
  have hseq : matrixSequenceExpectation dims D (fun n => NeZero.pos (dims n)) X = c • 1 := by
    apply Subtype.ext
    exact funext fun n => hE n
  have he := matrixQuotientExpectation_eq_self dims D (fun n => NeZero.pos (dims n)) L _ hmem
  rw [matrixQuotientExpectation_mk, hseq] at he
  change (matrixQuotientStarAlgHom dims L) (c • 1) = _ at he
  rw [map_smul, map_one] at he
  exact he.symm

theorem matrixQuotientAnchor_scalar_tendsto
    (hanchor : matrixInternalQuotient dims A L ⊓ matrixRelativeCommutant dims U L =
      matrixInternalQuotient dims D L)
    (hXA : ∀ n, X.val n ∈ A n)
    (hc : ∀ j, Tendsto (fun n => hsNorm (X.val n * (U n j).val - (U n j).val * X.val n)) L (𝓝 0))
    (hE : ∀ n, matrixTraceProjection (D n) (X.val n) = c • 1) :
    Tendsto (fun n => hsNorm (X.val n - c • 1)) L (𝓝 0) := by
  apply (matrixQuotientMk_eq_iff dims L X (c • 1)).mp
  change matrixQuotientMk dims L X = (matrixQuotientStarAlgHom dims L) (c • 1)
  rw [map_smul, map_one]
  exact matrixQuotientAnchor_scalar dims U L A D X c hanchor hXA hc hE

end ThomGame.Analysis
