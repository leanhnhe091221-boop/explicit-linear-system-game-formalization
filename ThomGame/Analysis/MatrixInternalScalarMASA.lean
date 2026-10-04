module

public import ThomGame.Analysis.MatrixBlockScalarGap
public import ThomGame.Analysis.MatrixALTScalarDiagonal
public import ThomGame.Analysis.MatrixQuotientExpectation

/-!
# The actual internal scalar diagonal is maximal abelian

The uniform block scalar gap gives a direct Poincare proof: a block
representative commuting with the tuple is 2-close to its scalar
diagonal expectation. Together with the exact diagonal commutant
criterion this proves the MASA identity.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter Matrix
open scoped Topology BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

theorem matrixPartitionScalarAlgebra_le_block {d : Nat} {μ : Type*} [Fintype μ]
    (E : μ → CMatrix d) (hE : ∀ i, IsStarProjection (E i))
    (horth : Pairwise (fun i j => E i * E j = 0)) (hsum : ∑ i, E i = 1) :
    matrixPartitionScalarAlgebra E ≤ matrixPartitionBlockAlgebra E := by
  intro X hX
  obtain ⟨c, rfl⟩ := (mem_matrixPartitionScalarAlgebra_iff E hE horth hsum X).mp hX
  apply (mem_matrixPartitionBlockAlgebra_iff E hE _).mpr
  intro i
  show E i * matrixPartitionScalarSum E c = matrixPartitionScalarSum E c * E i
  rw [matrixPartitionScalarSum_block_left E hE horth]
  exact (matrixCorner_sum_block_right E (fun j => c j • E j) horth
    (fun j => by rw [Matrix.smul_mul, (hE j).isIdempotentElem.eq]) i).symm

theorem matrixCoordinateEnergy_tendsto_zero_of_commutant {ι : Type*} (dims : ι → Nat) {h : Nat}
    (U : (k : ι) → Fin h → UnitaryMatrix (dims k)) (L : Filter ι) (A : BoundedMatrixSequence dims)
    (hA : matrixQuotientMk dims L A ∈ matrixRelativeCommutant dims U L) :
    Tendsto (fun k => matrixCoordinateEnergy (U k) (A.val k)) L (𝓝 0) := by
  have hc := (mem_matrixRelativeCommutant_iff dims U L _).mp hA
  have ht (j : Fin h) : Tendsto (fun k => hsNorm ((U k j).val * A.val k - A.val k * (U k j).val)) L (𝓝 0) := by
    apply (matrixQuotientMk_eq_iff dims L
      (boundedUnitarySequence dims (fun k => U k j) * A)
      (A * boundedUnitarySequence dims (fun k => U k j))).mp
    rw [map_mul, map_mul]
    exact (hc j).eq
  have hs := (tendsto_finsetSum Finset.univ (fun j _ => (ht j).pow 2)).const_mul (lazyMarkovWeight h)
  simpa only [matrixCoordinateEnergy, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, mul_zero] using hs

variable {ι : Type*} (dims : ι → Nat) {h : Nat}
  (U : (k : ι) → Fin h → UnitaryMatrix (dims k)) (hd : ∀ k, 0 < dims k)
  (c : ℝ) (Q : (k : ι) → MatrixScalarGapPartition (U k) c) (L : Filter ι)

include hd

theorem matrixScalarGapPartition_block_commutant_mem_diagonal (hc : 0 < c)
    (hne : ∀ k i, (Q k).E i ≠ 0) (x : MatrixTracialQuotient dims L)
    (hblock : x ∈ matrixInternalQuotient dims (fun k => matrixPartitionBlockAlgebra (Q k).E) L)
    (hcomm : x ∈ matrixRelativeCommutant dims U L) :
    x ∈ matrixInternalQuotient dims (fun k => matrixPartitionScalarAlgebra (Q k).E) L := by
  obtain ⟨A, hA, rfl⟩ := (mem_matrixInternalQuotient dims _ L x).mp hblock
  let (k : ι) : NeZero (dims k) := ⟨Nat.ne_of_gt (hd k)⟩
  let S := fun k => matrixPartitionScalarAlgebra (Q k).E
  let B := matrixSequenceExpectation dims S hd A
  have he := matrixCoordinateEnergy_tendsto_zero_of_commutant dims U L A hcomm
  have hdiv : Tendsto (fun k => matrixCoordinateEnergy (U k) (A.val k) / c) L (𝓝 0) := by
    simpa only [zero_div] using he.div_const c
  have hsq : Tendsto (fun k => hsNorm (A.val k - B.val k) ^ 2) L (𝓝 0) := by
    apply squeeze_zero (fun k => sq_nonneg _) _ hdiv
    intro k
    apply (le_div_iff₀ hc).mpr
    change hsNorm (A.val k - matrixTraceProjection (S k) (A.val k)) ^ 2 * c ≤ _
    rw [← matrixPartitionScalarExpectation_eq_traceProjection (Q k).E (Q k).projection
      (Q k).orthogonal (Q k).sum_one]
    simpa only [mul_comm] using (Q k).block_scalar_gap (hne k) (A.val k) (hA k)
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  have hnorm : Tendsto (fun k => hsNorm (A.val k - B.val k)) L (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_sq (hsNorm_nonneg _), Real.sqrt_zero] using ht
  have hsame := (matrixQuotientMk_eq_iff dims L A B).mpr hnorm
  exact (mem_matrixInternalQuotient dims _ L _).mpr
    ⟨B, matrixSequenceExpectation_mem dims S hd A, hsame.symm⟩

theorem matrixScalarGapPartition_internal_block_inf_commutant (hc : 0 < c)
    (hne : ∀ k i, (Q k).E i ≠ 0) :
    matrixInternalQuotient dims (fun k => matrixPartitionBlockAlgebra (Q k).E) L ⊓
      matrixRelativeCommutant dims U L =
        matrixInternalQuotient dims (fun k => matrixPartitionScalarAlgebra (Q k).E) L := by
  apply le_antisymm
  · intro x hx
    exact matrixScalarGapPartition_block_commutant_mem_diagonal dims U hd c Q L hc hne x hx.1 hx.2
  · apply le_inf _ (matrixScalarGapPartition_internal_le_commutant dims U c Q L)
    intro x hx
    obtain ⟨A, hA, rfl⟩ := (mem_matrixInternalQuotient dims _ L x).mp hx
    exact (mem_matrixInternalQuotient dims _ L _).mpr ⟨A, fun k =>
      matrixPartitionScalarAlgebra_le_block (Q k).E (Q k).projection (Q k).orthogonal (Q k).sum_one (hA k), rfl⟩

theorem matrixScalarGapPartition_internal_masa (hc : 0 < c) (hne : ∀ k i, (Q k).E i ≠ 0) :
    StarSubalgebra.centralizer ℂ
      (matrixInternalQuotient dims (fun k => matrixPartitionScalarAlgebra (Q k).E) L :
        Set (MatrixTracialQuotient dims L)) ⊓ matrixRelativeCommutant dims U L =
      matrixInternalQuotient dims (fun k => matrixPartitionScalarAlgebra (Q k).E) L := by
  rw [matrixInternalDiagonal_centralizer dims (fun k => (Q k).E) (fun k => (Q k).projection)
    (fun k => (Q k).orthogonal) (fun k => (Q k).sum_one) L hd]
  exact matrixScalarGapPartition_internal_block_inf_commutant dims U hd c Q L hc hne

end ThomGame.Analysis
