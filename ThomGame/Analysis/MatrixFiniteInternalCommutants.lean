module

public import ThomGame.Analysis.MatrixInternalCommutants
public import ThomGame.Analysis.MatrixInternalCenters
public import ThomGame.Analysis.MatrixFiniteExpectation

/-!
# Internal commutants and centers inside the actual finite operator algebra

The faithful, surjective matrix representation transports the coordinate
commutant and center equalities to the entire finite weakly closed algebra.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter

variable (dims : Nat → Nat) (S : (n : Nat) → StarSubalgebra ℂ (CMatrix (dims n)))
  (hd : ∀ n, 0 < dims n) (L : Ultrafilter Nat)

theorem matrixFiniteEmbedding_mem_internalCommutant_iff (x : MatrixTracialQuotient dims (L : Filter Nat)) :
    matrixFiniteEmbedding dims hd L x ∈ StarSubalgebra.centralizer ℂ
        (matrixInternalFiniteAlgebra dims S hd L : Set (MatrixFiniteOperatorAlgebra dims hd L)) ↔
      x ∈ StarSubalgebra.centralizer ℂ
        (matrixInternalQuotient dims S (L : Filter Nat) : Set (MatrixTracialQuotient dims (L : Filter Nat))) := by
  rw [StarSubalgebra.mem_centralizer_iff, StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h y hy
    have he := h _ ((matrixFiniteEmbedding_mem_internal_iff dims S hd L y).mpr hy)
    simpa only [← map_star, ← map_mul, (matrixFiniteEmbedding_injective dims hd L).eq_iff] using he
  · intro h y hy
    have hy' : ∃ z ∈ matrixInternalQuotient dims S (L : Filter Nat), matrixFiniteEmbedding dims hd L z = y := hy
    obtain ⟨z, hz, rfl⟩ := hy'
    constructor
    · simpa only [map_mul] using congrArg (matrixFiniteEmbedding dims hd L) (h z hz).1
    · simpa only [map_mul, map_star] using congrArg (matrixFiniteEmbedding dims hd L) (h z hz).2

theorem matrixInternalFiniteAlgebra_commutant (hL : (L : Filter Nat) ≤ atTop) :
    StarSubalgebra.centralizer ℂ
        (matrixInternalFiniteAlgebra dims S hd L : Set (MatrixFiniteOperatorAlgebra dims hd L)) =
      matrixInternalFiniteAlgebra dims (fun n => StarSubalgebra.centralizer ℂ (S n : Set (CMatrix (dims n)))) hd L := by
  ext T
  obtain ⟨x, rfl⟩ := matrixFiniteEmbedding_surjective dims hd L hL T
  rw [matrixFiniteEmbedding_mem_internalCommutant_iff, matrixFiniteEmbedding_mem_internal_iff,
    matrixInternalQuotient_commutant dims S hd (L : Filter Nat)]

theorem matrixInternalFiniteAlgebra_center (hL : (L : Filter Nat) ≤ atTop) :
    starSubalgebraCenter (matrixInternalFiniteAlgebra dims S hd L) =
      matrixInternalFiniteAlgebra dims (fun n => starSubalgebraCenter (S n)) hd L := by
  ext T
  obtain ⟨x, rfl⟩ := matrixFiniteEmbedding_surjective dims hd L hL T
  change (matrixFiniteEmbedding dims hd L x ∈ matrixInternalFiniteAlgebra dims S hd L ∧
    matrixFiniteEmbedding dims hd L x ∈ StarSubalgebra.centralizer ℂ
      (matrixInternalFiniteAlgebra dims S hd L : Set (MatrixFiniteOperatorAlgebra dims hd L))) ↔ _
  rw [matrixFiniteEmbedding_mem_internal_iff, matrixFiniteEmbedding_mem_internalCommutant_iff,
    matrixFiniteEmbedding_mem_internal_iff]
  change x ∈ starSubalgebraCenter (matrixInternalQuotient dims S (L : Filter Nat)) ↔ _
  rw [matrixInternalQuotient_center dims S hd (L : Filter Nat)]

end ThomGame.Analysis
