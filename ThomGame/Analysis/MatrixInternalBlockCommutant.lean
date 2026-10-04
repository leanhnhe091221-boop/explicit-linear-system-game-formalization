module

public import ThomGame.Analysis.MatrixPartitionScalarAlgebra
public import ThomGame.Analysis.MatrixRandomSignPinching
public import ThomGame.Analysis.MatrixSignPinchingContraction
public import ThomGame.Analysis.MatrixInternalSequences

/-!
# The commutant of the internal scalar diagonal algebra

Coordinate sign unitaries detect the off-block part of any bounded
representative. The resulting exact commutant equality holds for any
filter, without assuming a spectral gap or internality of another algebra.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter Matrix
open scoped Topology BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

theorem matrixSignSum_mem_scalarAlgebra {d : Nat} {μ : Type*} [Fintype μ]
    (E : μ → CMatrix d) (ε : μ → Bool) : finiteSignSum E ε ∈ matrixPartitionScalarAlgebra E := by
  apply (matrixPartitionScalarAlgebra E).sum_mem
  intro i _
  change finiteSign (ε i) • E i ∈ matrixPartitionScalarAlgebra E
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact (matrixPartitionScalarAlgebra E).smul_mem
    (matrixPartitionScalarAlgebra_projection_mem E i) (finiteSign (ε i) : ℂ)

variable {ι : Type*} (dims : ι → Nat) {μ : ι → Type*} [∀ k, Fintype (μ k)]
  (E : (k : ι) → μ k → CMatrix (dims k))
  (hE : ∀ k i, IsStarProjection (E k i))
  (horth : ∀ k, Pairwise (fun i j => E k i * E k j = 0))

noncomputable def boundedMatrixPinch (A : BoundedMatrixSequence dims) : BoundedMatrixSequence dims :=
  ⟨fun k => matrixBlockPinch (E k) (A.val k), by
    obtain ⟨K, hK, hA⟩ := BoundedMatrixSequence.bound dims A
    exact ⟨K, hK, fun k => (matrixBlockPinch_matrixOpNorm_le (E k) (hE k) (horth k) _).trans (hA k)⟩⟩

@[simp] theorem boundedMatrixPinch_apply (A : BoundedMatrixSequence dims) (k : ι) :
    (boundedMatrixPinch dims E hE horth A).val k = matrixBlockPinch (E k) (A.val k) := rfl

noncomputable def boundedMatrixSign (ε : (k : ι) → μ k → Bool) : BoundedMatrixSequence dims :=
  ⟨fun k => finiteSignSum (E k) (ε k), 1, zero_le_one,
    fun k => matrixSignSum_matrixOpNorm_le_one (E k) (hE k) (horth k) (ε k)⟩

@[simp] theorem boundedMatrixSign_apply (ε : (k : ι) → μ k → Bool) (k : ι) :
    (boundedMatrixSign dims E hE horth ε).val k = finiteSignSum (E k) (ε k) := rfl

theorem boundedMatrixSign_scalar_mem (ε : (k : ι) → μ k → Bool) (k : ι) :
    (boundedMatrixSign dims E hE horth ε).val k ∈ matrixPartitionScalarAlgebra (E k) :=
  matrixSignSum_mem_scalarAlgebra (E k) (ε k)

theorem boundedMatrixPinch_block_mem (A : BoundedMatrixSequence dims) (k : ι) :
    (boundedMatrixPinch dims E hE horth A).val k ∈ matrixPartitionBlockAlgebra (E k) := by
  apply (mem_matrixPartitionBlockAlgebra_iff (E k) (hE k) _).mpr
  intro i
  exact matrixBlockPinch_commute (E k) (hE k) (fun i j hij => horth k hij) i (A.val k)

variable (hsum : ∀ k, ∑ i, E k i = 1) (L : Filter ι)

include hE horth hsum

theorem matrixInternalDiagonal_commute_pinching_tendsto (hd : ∀ k, 0 < dims k)
    (A : BoundedMatrixSequence dims)
    (hA : ∀ S : BoundedMatrixSequence dims,
      (∀ k, S.val k ∈ matrixPartitionScalarAlgebra (E k)) →
        Commute (matrixQuotientMk dims L S) (matrixQuotientMk dims L A)) :
    Tendsto (fun k => hsNorm (A.val k - matrixBlockPinch (E k) (A.val k))) L (𝓝 0) := by
  classical
  have hsign (k : ι) : ∃ ε : μ k → Bool,
      2 * hsNorm (A.val k - matrixBlockPinch (E k) (A.val k)) ^ 2 ≤
        hsNorm (A.val k * finiteSignSum (E k) ε - finiteSignSum (E k) ε * A.val k) ^ 2 := by
    let : NeZero (dims k) := ⟨Nat.ne_of_gt (hd k)⟩
    exact exists_matrixSignSum_pinching_defect_le (E k) (hE k) (horth k) (hsum k) (A.val k)
  choose ε hε using hsign
  let S := boundedMatrixSign dims E hE horth ε
  have hc : matrixQuotientMk dims L (A * S) = matrixQuotientMk dims L (S * A) := by
    rw [map_mul, map_mul]
    exact (hA S (boundedMatrixSign_scalar_mem dims E hE horth ε)).symm.eq
  have ht := (matrixQuotientMk_eq_iff dims L (A * S) (S * A)).mp hc
  change Tendsto (fun k => hsNorm (A.val k * finiteSignSum (E k) (ε k) -
    finiteSignSum (E k) (ε k) * A.val k)) L (𝓝 0) at ht
  apply squeeze_zero (fun k => hsNorm_nonneg _) _ ht
  intro k
  apply (sq_le_sq₀ (hsNorm_nonneg _) (hsNorm_nonneg _)).mp
  linarith only [hε k, sq_nonneg (hsNorm (A.val k - matrixBlockPinch (E k) (A.val k)))]

theorem matrixInternalBlock_scalar_commute {x y : MatrixTracialQuotient dims L}
    (hx : x ∈ matrixInternalQuotient dims (fun k => matrixPartitionBlockAlgebra (E k)) L)
    (hy : y ∈ matrixInternalQuotient dims (fun k => matrixPartitionScalarAlgebra (E k)) L) :
    Commute y x := by
  obtain ⟨A, hA, rfl⟩ := (mem_matrixInternalQuotient dims _ L x).mp hx
  obtain ⟨B, hB, rfl⟩ := (mem_matrixInternalQuotient dims _ L y).mp hy
  show matrixQuotientMk dims L B * matrixQuotientMk dims L A =
    matrixQuotientMk dims L A * matrixQuotientMk dims L B
  rw [← map_mul, ← map_mul]
  apply congrArg (matrixQuotientMk dims L)
  apply Subtype.ext
  funext k
  exact (matrixPartitionScalarAlgebra_commute (E k) (hE k) (horth k) (hsum k) (hA k) (hB k)).eq

theorem matrixInternalDiagonal_centralizer (hd : ∀ k, 0 < dims k) :
    StarSubalgebra.centralizer ℂ
      (matrixInternalQuotient dims (fun k => matrixPartitionScalarAlgebra (E k)) L :
        Set (MatrixTracialQuotient dims L)) =
      matrixInternalQuotient dims (fun k => matrixPartitionBlockAlgebra (E k)) L := by
  ext x
  rw [StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro hx
    obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims L x
    have ht := matrixInternalDiagonal_commute_pinching_tendsto dims E hE horth hsum L hd A
      (fun S hS => (hx _ ((mem_matrixInternalQuotient dims _ L _).mpr ⟨S, hS, rfl⟩)).1)
    apply (mem_matrixInternalQuotient dims _ L _).mpr
    refine ⟨boundedMatrixPinch dims E hE horth A,
      boundedMatrixPinch_block_mem dims E hE horth A, ?_⟩
    symm
    exact (matrixQuotientMk_eq_iff dims L A (boundedMatrixPinch dims E hE horth A)).mpr ht
  · intro hx y hy
    exact ⟨(matrixInternalBlock_scalar_commute dims E hE horth hsum L hx hy).eq,
      (matrixInternalBlock_scalar_commute dims E hE horth hsum L hx
        ((matrixInternalQuotient dims (fun k => matrixPartitionScalarAlgebra (E k)) L).star_mem' hy)).eq⟩

end ThomGame.Analysis
