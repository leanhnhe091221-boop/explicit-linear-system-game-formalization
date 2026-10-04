module

public import ThomGame.Analysis.MatrixInternalNearInclusion
public import ThomGame.Analysis.MatrixFiniteExpectation

/-!
# Thom's near-inclusion criterion in the actual finite operator algebra

The faithful matrix representation preserves and reflects inclusions
between internal algebras. The coordinate near-inclusion criterion
therefore applies directly in the finite weakly closed model.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

variable (dims : Nat → Nat) (B A : (n : Nat) → StarSubalgebra ℂ (CMatrix (dims n)))
  (hd : ∀ n, 0 < dims n) (L : Ultrafilter Nat)

theorem matrixInternalFiniteAlgebra_le_iff :
    matrixInternalFiniteAlgebra dims B hd L ≤ matrixInternalFiniteAlgebra dims A hd L ↔
      matrixInternalQuotient dims B (L : Filter Nat) ≤ matrixInternalQuotient dims A (L : Filter Nat) := by
  constructor
  · intro h x hx
    exact (matrixFiniteEmbedding_mem_internal_iff dims A hd L x).mp
      (h ((matrixFiniteEmbedding_mem_internal_iff dims B hd L x).mpr hx))
  · rintro h T ⟨x, hx, rfl⟩
    exact ⟨x, h hx, rfl⟩

variable [∀ n, NeZero (dims n)]

theorem matrixInternalFinite_le_iff_nearInclusionError_tendsto :
    matrixInternalFiniteAlgebra dims B hd L ≤ matrixInternalFiniteAlgebra dims A hd L ↔
      Tendsto (fun n => matrixNearInclusionError (B n) (A n)) (L : Filter Nat) (𝓝 0) := by
  rw [matrixInternalFiniteAlgebra_le_iff,
    matrixInternal_le_iff_nearInclusionError_tendsto dims B A hd (L : Filter Nat)]

theorem exists_matrixNearInclusion_errors_of_finiteInternal_le
    (hle : matrixInternalFiniteAlgebra dims B hd L ≤ matrixInternalFiniteAlgebra dims A hd L) :
    ∃ ε : Nat → ℝ, (∀ n, 0 ≤ ε n) ∧ Tendsto ε (L : Filter Nat) (𝓝 0) ∧
      ∀ n, MatrixNearInclusion (B n) (A n) (ε n) :=
  exists_matrixNearInclusion_errors_of_internal_le dims B A hd (L : Filter Nat)
    ((matrixInternalFiniteAlgebra_le_iff dims B A hd L).mp hle)

end ThomGame.Analysis
