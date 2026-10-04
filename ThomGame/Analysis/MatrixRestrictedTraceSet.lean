module

public import ThomGame.Analysis.MatrixBoundedTraceBall

/-!
# Trace limits preserving coordinatewise matrix constraints

The diagonal representative takes its value at each coordinate from one
of the original representatives at that same coordinate. Consequently
arbitrary coordinatewise set membership is preserved, including membership
in a prescribed family of matrix star subalgebras. No closedness assumption
on those coordinate sets is needed.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

variable (dims : Nat → Nat) (hd : ∀ n, 0 < dims n) (U : Ultrafilter Nat)

def matrixRestrictedTraceSet (S : (n : Nat) → Set (CMatrix (dims n))) (K : ℝ) :
    Set (MatrixTraceHilbert dims hd U) :=
  {x | ∃ A : BoundedMatrixSequence dims, (∀ n, A.val n ∈ S n) ∧
    (∀ n, matrixOpNorm (A.val n) ≤ K) ∧
    matrixHilbertEmbedding dims hd U (matrixQuotientMk dims (U : Filter Nat) A) = x}

theorem matrixRestrictedTraceSet_subset_ball (S : (n : Nat) → Set (CMatrix (dims n))) (K : ℝ) :
    matrixRestrictedTraceSet dims hd U S K ⊆ matrixBoundedTraceBall dims hd U K := by
  rintro x ⟨A, _, hA, hAx⟩
  exact ⟨A, hA, hAx⟩

theorem matrixRestrictedTraceSet_isClosed (hU : (U : Filter Nat) ≤ atTop)
    (S : (n : Nat) → Set (CMatrix (dims n))) (K : ℝ) (hK : 0 ≤ K) :
    IsClosed (matrixRestrictedTraceSet dims hd U S K) := by
  classical
  apply IsSeqClosed.isClosed
  intro v x hv hx
  have hchoose : ∀ k : Nat, ∃ n : Nat, dist (v n) x < 1 / ((k : ℝ) + 1) := by
    intro k
    obtain ⟨n, hn⟩ := Metric.tendsto_atTop.1 hx (1 / ((k : ℝ) + 1)) (by positivity)
    exact ⟨n, hn n le_rfl⟩
  choose s hs using hchoose
  have ha : ∀ k, ∃ A : BoundedMatrixSequence dims, (∀ n, A.val n ∈ S n) ∧
      (∀ n, matrixOpNorm (A.val n) ≤ K) ∧
      matrixHilbertEmbedding dims hd U (matrixQuotientMk dims (U : Filter Nat) A) = v (s k) :=
    fun k => hv (s k)
  choose A hS hA hAv using ha
  obtain ⟨B, hB, hBx⟩ := exists_matrixDiagonal_of_fast_approximation dims hd U hU K hK A hA x
    (fun k => by rw [hAv k]; exact (hs k).le)
  refine ⟨B, ?_, ?_, hBx⟩
  · intro n
    obtain ⟨k, hk⟩ := hB n
    rw [hk]
    exact hS k n
  · intro n
    obtain ⟨k, hk⟩ := hB n
    rw [hk]
    exact hA k n

theorem matrixRestrictedTraceSet_isComplete (hU : (U : Filter Nat) ≤ atTop)
    (S : (n : Nat) → Set (CMatrix (dims n))) (K : ℝ) (hK : 0 ≤ K) :
    IsComplete (matrixRestrictedTraceSet dims hd U S K) :=
  (matrixRestrictedTraceSet_isClosed dims hd U hU S K hK).isComplete

theorem matrixInternalTraceBall_isClosed (hU : (U : Filter Nat) ≤ atTop)
    (S : (n : Nat) → StarSubalgebra ℂ (CMatrix (dims n))) (K : ℝ) (hK : 0 ≤ K) :
    IsClosed (matrixRestrictedTraceSet dims hd U (fun n => (S n : Set (CMatrix (dims n)))) K) :=
  matrixRestrictedTraceSet_isClosed dims hd U hU _ K hK

end ThomGame.Analysis
