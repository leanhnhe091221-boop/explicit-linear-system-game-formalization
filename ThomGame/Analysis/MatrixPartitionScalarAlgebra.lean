module

public import ThomGame.Analysis.MatrixOrthogonalCornerSums
public import Mathlib.Algebra.Star.Subalgebra

/-!
# The actual scalar diagonal algebra of a projection partition

The generated star algebra is exactly the finite scalar sums of the
partition projections. Its commutant is the algebra of matrices
commuting with every partition block.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} {μ : Type*} [Fintype μ]

noncomputable def matrixPartitionScalarSum (E : μ → CMatrix d) (c : μ → ℂ) : CMatrix d :=
  ∑ i, c i • E i

theorem matrixPartitionScalarSum_block_left (E : μ → CMatrix d)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (c : μ → ℂ) (i : μ) : E i * matrixPartitionScalarSum E c = c i • E i := by
  exact matrixCorner_sum_block_left E (fun i => c i • E i) horth
    (fun i => by rw [Matrix.mul_smul, (hE i).isIdempotentElem.eq]) i

theorem matrixPartitionScalarSum_mul (E : μ → CMatrix d)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (c b : μ → ℂ) : matrixPartitionScalarSum E c * matrixPartitionScalarSum E b =
      matrixPartitionScalarSum E (c * b) := by
  change (∑ i, c i • E i) * matrixPartitionScalarSum E b = _
  rw [Matrix.sum_mul]
  simp only [Matrix.smul_mul, matrixPartitionScalarSum_block_left E hE horth, smul_smul]
  rfl

noncomputable def matrixPartitionScalarHom (E : μ → CMatrix d)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (hsum : ∑ i, E i = 1) : (μ → ℂ) →⋆ₐ[ℂ] CMatrix d where
  toFun := matrixPartitionScalarSum E
  map_zero' := by simp [matrixPartitionScalarSum]
  map_one' := by simpa only [matrixPartitionScalarSum, Pi.one_apply, one_smul] using hsum
  map_add' c b := by simp only [matrixPartitionScalarSum, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_mul' c b := (matrixPartitionScalarSum_mul E hE horth c b).symm
  commutes' c := by
    change (∑ i, c • E i) = algebraMap ℂ (CMatrix d) c
    rw [← Finset.smul_sum, hsum, Algebra.algebraMap_eq_smul_one]
  map_star' c := by
    simp only [matrixPartitionScalarSum, star_sum, star_smul, Pi.star_apply,
      fun i => (hE i).isSelfAdjoint.star_eq]

def matrixPartitionScalarAlgebra (E : μ → CMatrix d) : StarSubalgebra ℂ (CMatrix d) :=
  StarAlgebra.adjoin ℂ (Set.range E)

omit [Fintype μ] in
theorem matrixPartitionScalarAlgebra_projection_mem (E : μ → CMatrix d) (i : μ) :
    E i ∈ matrixPartitionScalarAlgebra E := StarAlgebra.subset_adjoin ℂ _ ⟨i, rfl⟩

theorem matrixPartitionScalarSum_mem (E : μ → CMatrix d) (c : μ → ℂ) :
    matrixPartitionScalarSum E c ∈ matrixPartitionScalarAlgebra E := by
  apply (matrixPartitionScalarAlgebra E).sum_mem
  intro i _
  exact (matrixPartitionScalarAlgebra E).smul_mem (matrixPartitionScalarAlgebra_projection_mem E i) (c i)

theorem matrixPartitionScalarAlgebra_eq_range (E : μ → CMatrix d)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (hsum : ∑ i, E i = 1) :
    matrixPartitionScalarAlgebra E = (matrixPartitionScalarHom E hE horth hsum).range := by
  classical
  apply le_antisymm
  · apply StarAlgebra.adjoin_le
    rintro X ⟨i, rfl⟩
    refine ⟨fun j => if j = i then 1 else 0, ?_⟩
    change matrixPartitionScalarSum E (fun j => if j = i then 1 else 0) = E i
    simp [matrixPartitionScalarSum]
  · rintro X ⟨c, rfl⟩
    exact matrixPartitionScalarSum_mem E c

theorem mem_matrixPartitionScalarAlgebra_iff (E : μ → CMatrix d)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (hsum : ∑ i, E i = 1) (X : CMatrix d) :
    X ∈ matrixPartitionScalarAlgebra E ↔ ∃ c : μ → ℂ, matrixPartitionScalarSum E c = X := by
  rw [matrixPartitionScalarAlgebra_eq_range E hE horth hsum]
  rfl

def matrixPartitionBlockAlgebra (E : μ → CMatrix d) : StarSubalgebra ℂ (CMatrix d) :=
  StarSubalgebra.centralizer ℂ (Set.range E)

omit [Fintype μ] in
theorem mem_matrixPartitionBlockAlgebra_iff (E : μ → CMatrix d)
    (hE : ∀ i, IsStarProjection (E i)) (X : CMatrix d) :
    X ∈ matrixPartitionBlockAlgebra E ↔ ∀ i, Commute (E i) X := by
  rw [matrixPartitionBlockAlgebra, StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro hx i
    exact (hx _ ⟨i, rfl⟩).1
  · intro hx Y hY
    obtain ⟨i, rfl⟩ := hY
    exact ⟨(hx i).eq, by simpa only [(hE i).isSelfAdjoint.star_eq] using (hx i).eq⟩

theorem matrixPartitionScalarSum_commute (E : μ → CMatrix d) (c : μ → ℂ) {X : CMatrix d}
    (hX : ∀ i, Commute (E i) X) : Commute (matrixPartitionScalarSum E c) X := by
  show matrixPartitionScalarSum E c * X = X * matrixPartitionScalarSum E c
  simp only [matrixPartitionScalarSum, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul, fun i => (hX i).eq]

theorem matrixPartitionScalarAlgebra_commute (E : μ → CMatrix d)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (hsum : ∑ i, E i = 1) {X Y : CMatrix d}
    (hX : X ∈ matrixPartitionBlockAlgebra E) (hY : Y ∈ matrixPartitionScalarAlgebra E) : Commute Y X := by
  obtain ⟨c, rfl⟩ := (mem_matrixPartitionScalarAlgebra_iff E hE horth hsum Y).mp hY
  exact matrixPartitionScalarSum_commute E c ((mem_matrixPartitionBlockAlgebra_iff E hE X).mp hX)

theorem matrixPartitionScalarAlgebra_centralizer (E : μ → CMatrix d)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (hsum : ∑ i, E i = 1) :
    StarSubalgebra.centralizer ℂ (matrixPartitionScalarAlgebra E : Set (CMatrix d)) =
      matrixPartitionBlockAlgebra E := by
  ext X
  rw [StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro hX
    apply (mem_matrixPartitionBlockAlgebra_iff E hE X).mpr
    intro i
    exact (hX _ (matrixPartitionScalarAlgebra_projection_mem E i)).1
  · intro hX Y hY
    exact ⟨(matrixPartitionScalarAlgebra_commute E hE horth hsum hX hY).eq,
      (matrixPartitionScalarAlgebra_commute E hE horth hsum hX
        ((matrixPartitionScalarAlgebra E).star_mem' hY)).eq⟩

end ThomGame.Analysis
