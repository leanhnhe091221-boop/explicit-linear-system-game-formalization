module

public import ThomGame.Analysis.MatrixRepresentedAlgebra
public import ThomGame.Analysis.WOTNormBounds

/-!
# Bounded pieces of the original matrix quotient are WOT closed

The actual operator-norm ball in the represented image is the
intersection of a fixed matrix-representative ball with the ambient
operator-norm ball. Both are WOT closed. This does not yet imply
closedness of the unbounded union.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter

variable (dims : Nat → Nat) (hd : ∀ n, 0 < dims n) (U : Ultrafilter Nat)

def matrixRepresentedWOTNormBall (K : ℝ) :
    Set (MatrixTraceHilbert dims hd U →WOT[ℂ] MatrixTraceHilbert dims hd U) :=
  {T | T ∈ (matrixLeftWOTRepresentation dims hd U).range ∧ ‖T.toCLM‖ ≤ K}

theorem matrixRepresentedWOTNormBall_eq (K : ℝ) (hK : 0 ≤ K) :
    matrixRepresentedWOTNormBall dims hd U K = matrixBoundedWOTBall dims hd U (2 * K) ∩
      {T | ‖T.toCLM‖ ≤ K} := by
  ext T
  constructor
  · rintro ⟨⟨x, rfl⟩, hx⟩
    obtain ⟨A, hA, hAx⟩ := exists_matrixRepresentative_bounded dims hd U x K hK hx
    exact ⟨⟨A, hA, congrArg (matrixLeftWOTRepresentation dims hd U) hAx⟩, hx⟩
  · rintro ⟨⟨A, hA, rfl⟩, hT⟩
    exact ⟨⟨matrixQuotientMk dims (U : Filter Nat) A, rfl⟩, hT⟩

theorem matrixRepresentedWOTNormBall_isClosed (hU : (U : Filter Nat) ≤ atTop)
    (K : ℝ) (hK : 0 ≤ K) : IsClosed (matrixRepresentedWOTNormBall dims hd U K) := by
  rw [matrixRepresentedWOTNormBall_eq dims hd U K hK]
  exact (matrixBoundedWOTBall_isClosed dims hd U hU (2 * K) (by positivity)).inter
    (wot_norm_ball_isClosed K hK)

end ThomGame.Analysis
