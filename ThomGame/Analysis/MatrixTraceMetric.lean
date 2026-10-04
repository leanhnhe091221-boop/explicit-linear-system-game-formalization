module

public import ThomGame.Analysis.MatrixTraceHilbert

/-!
# Matrix distances and their trace Hilbert limits

The Hilbert completion preserves the trace norm. Thus distances between
embedded matrix classes are the ultralimits of the normalized matrix
Hilbert--Schmidt distances of any bounded representatives.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

variable {ι : Type*} (dims : ι → Nat) (hd : ∀ i, 0 < dims i) (U : Ultrafilter ι)

theorem matrixHilbertEmbedding_norm (x : MatrixTracialQuotient dims (U : Filter ι)) :
    ‖matrixHilbertEmbedding dims hd U x‖ = ‖matrixTraceSpaceEquiv dims hd U x‖ :=
  UniformSpace.Completion.norm_coe _

theorem matrixHilbertEmbedding_norm_tendsto (A : BoundedMatrixSequence dims) :
    Tendsto (fun i => hsNorm (A.val i)) (U : Filter ι)
      (𝓝 ‖matrixHilbertEmbedding dims hd U (matrixQuotientMk dims (U : Filter ι) A)‖) := by
  rw [matrixHilbertEmbedding_norm]
  exact matrixTraceSpace_norm_tendsto dims hd U A

theorem matrixHilbertEmbedding_dist_tendsto (A B : BoundedMatrixSequence dims) :
    Tendsto (fun i => hsNorm (A.val i - B.val i)) (U : Filter ι)
      (𝓝 (dist (matrixHilbertEmbedding dims hd U (matrixQuotientMk dims (U : Filter ι) A))
        (matrixHilbertEmbedding dims hd U (matrixQuotientMk dims (U : Filter ι) B)))) := by
  rw [dist_eq_norm, ← map_sub, ← map_sub]
  exact matrixHilbertEmbedding_norm_tendsto dims hd U (A - B)

theorem matrixHilbertEmbedding_norm_le (A : BoundedMatrixSequence dims) (K : ℝ)
    (hA : ∀ i, matrixOpNorm (A.val i) ≤ K) :
    ‖matrixHilbertEmbedding dims hd U (matrixQuotientMk dims (U : Filter ι) A)‖ ≤ K := by
  apply le_of_tendsto (matrixHilbertEmbedding_norm_tendsto dims hd U A)
  apply Filter.Eventually.of_forall
  intro i
  let : NeZero (dims i) := ⟨Nat.ne_of_gt (hd i)⟩
  exact (hsNorm_le_matrixOpNorm _).trans (hA i)

end ThomGame.Analysis
