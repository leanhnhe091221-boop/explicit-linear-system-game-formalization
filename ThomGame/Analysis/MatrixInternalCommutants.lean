module

public import ThomGame.Analysis.MatrixCommutantConvexHull
public import ThomGame.Analysis.MatrixSequenceExpectation

/-!
# The commutant of an internal algebra has exact coordinate representatives

Every ambient matrix can be projected to the coordinate commutant.
Unitary witnesses from the original coordinate algebras show that this
projection error vanishes whenever the quotient element commutes with
the internal algebra. This holds for any filter and positive dimensions.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology Matrix.Norms.L2Operator

variable {ι : Type*} (dims : ι → Nat)
  (S : (k : ι) → StarSubalgebra ℂ (CMatrix (dims k))) (hd : ∀ k, 0 < dims k) (L : Filter ι)

omit hd in
theorem mem_matrixInternalCommutant_iff (x : MatrixTracialQuotient dims L) :
    x ∈ StarSubalgebra.centralizer ℂ (matrixInternalQuotient dims S L : Set (MatrixTracialQuotient dims L)) ↔
      ∀ B : BoundedMatrixSequence dims, (∀ k, B.val k ∈ S k) → Commute (matrixQuotientMk dims L B) x := by
  rw [StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h B hB
    exact (h _ ((mem_matrixInternalQuotient dims S L _).mpr ⟨B, hB, rfl⟩)).1
  · intro h y hy
    have hcomm : ∀ z ∈ matrixInternalQuotient dims S L, z * x = x * z := by
      intro z hz
      obtain ⟨B, hB, rfl⟩ := (mem_matrixInternalQuotient dims S L z).mp hz
      exact (h B hB).eq
    exact ⟨hcomm y hy, hcomm (star y) ((matrixInternalQuotient dims S L).star_mem' hy)⟩

include hd in
theorem matrixInternal_commutant_distance_tendsto (A : BoundedMatrixSequence dims)
    (hcomm : ∀ B : BoundedMatrixSequence dims, (∀ k, B.val k ∈ S k) →
      Commute (matrixQuotientMk dims L B) (matrixQuotientMk dims L A)) :
    Tendsto (fun k => hsNorm (A.val k -
      (matrixSequenceExpectation dims (fun k => StarSubalgebra.centralizer ℂ (S k : Set (CMatrix (dims k)))) hd A).val k))
      L (𝓝 0) := by
  classical
  let (k : ι) : NeZero (dims k) := ⟨Nat.ne_of_gt (hd k)⟩
  choose U hU using fun k => exists_matrixUnitary_detecting_commutant_distance (S k) (A.val k)
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
theorem matrixInternalCommutants_commute {x y : MatrixTracialQuotient dims L}
    (hx : x ∈ matrixInternalQuotient dims (fun k => StarSubalgebra.centralizer ℂ (S k : Set (CMatrix (dims k)))) L)
    (hy : y ∈ matrixInternalQuotient dims S L) : Commute y x := by
  obtain ⟨A, hA, rfl⟩ := (mem_matrixInternalQuotient dims _ L x).mp hx
  obtain ⟨B, hB, rfl⟩ := (mem_matrixInternalQuotient dims S L y).mp hy
  show matrixQuotientMk dims L B * matrixQuotientMk dims L A =
    matrixQuotientMk dims L A * matrixQuotientMk dims L B
  rw [← map_mul, ← map_mul]
  apply congrArg (matrixQuotientMk dims L)
  apply Subtype.ext
  funext k
  exact (mem_matrixSubalgebraCommutant_iff (S k) (A.val k)).mp (hA k) (B.val k) (hB k)

include hd in
theorem matrixInternalQuotient_commutant :
    StarSubalgebra.centralizer ℂ (matrixInternalQuotient dims S L : Set (MatrixTracialQuotient dims L)) =
      matrixInternalQuotient dims (fun k => StarSubalgebra.centralizer ℂ (S k : Set (CMatrix (dims k)))) L := by
  ext x
  rw [mem_matrixInternalCommutant_iff]
  constructor
  · intro hcomm
    obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims L x
    have ht := matrixInternal_commutant_distance_tendsto dims S hd L A hcomm
    apply (mem_matrixInternalQuotient dims _ L _).mpr
    refine ⟨matrixSequenceExpectation dims (fun k => StarSubalgebra.centralizer ℂ (S k : Set (CMatrix (dims k)))) hd A,
      matrixSequenceExpectation_mem dims _ hd A, ?_⟩
    exact ((matrixQuotientMk_eq_iff dims L A _).mpr ht).symm
  · intro hx B hB
    exact matrixInternalCommutants_commute dims S L hx
      ((mem_matrixInternalQuotient dims S L _).mpr ⟨B, hB, rfl⟩)

end ThomGame.Analysis
