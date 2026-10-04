module

public import ThomGame.Analysis.FilterDiagonal
public import ThomGame.Analysis.MatrixTraceMetric
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Sequences

/-!
# Completeness of uniformly bounded matrix representatives in the trace norm

For a nonprincipal ultrafilter on `Nat`, vectors represented by matrix
sequences with a fixed uniform operator bound form a closed subset of the
trace Hilbert space. The proof selects an actual diagonal representative;
there is no assumption of completeness of the original algebraic quotient.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

variable {ι : Type*}

def matrixBoundedTraceBall (dims : ι → Nat) (hd : ∀ i, 0 < dims i) (U : Ultrafilter ι)
    (K : ℝ) : Set (MatrixTraceHilbert dims hd U) :=
  {x | ∃ A : BoundedMatrixSequence dims, (∀ i, matrixOpNorm (A.val i) ≤ K) ∧
    matrixHilbertEmbedding dims hd U (matrixQuotientMk dims (U : Filter ι) A) = x}

theorem matrixBoundedTraceBall_norm_le (dims : ι → Nat) (hd : ∀ i, 0 < dims i)
    (U : Ultrafilter ι) (K : ℝ) {x : MatrixTraceHilbert dims hd U}
    (hx : x ∈ matrixBoundedTraceBall dims hd U K) : ‖x‖ ≤ K := by
  obtain ⟨A, hA, rfl⟩ := hx
  exact matrixHilbertEmbedding_norm_le dims hd U A K hA

variable (dims : Nat → Nat) (hd : ∀ n, 0 < dims n) (U : Ultrafilter Nat)

theorem exists_matrixDiagonal_of_fast_approximation
    (hU : (U : Filter Nat) ≤ atTop) (K : ℝ) (hK : 0 ≤ K)
    (A : Nat → BoundedMatrixSequence dims) (hA : ∀ k n, matrixOpNorm ((A k).val n) ≤ K)
    (x : MatrixTraceHilbert dims hd U)
    (hx : ∀ k, dist (matrixHilbertEmbedding dims hd U
      (matrixQuotientMk dims (U : Filter Nat) (A k))) x ≤ 1 / ((k : ℝ) + 1)) :
    ∃ B : BoundedMatrixSequence dims, (∀ n, ∃ k, B.val n = (A k).val n) ∧
      matrixHilbertEmbedding dims hd U (matrixQuotientMk dims (U : Filter Nat) B) = x := by
  classical
  let r : Nat → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hr : ∀ k, 0 < r k := by intro k; dsimp [r]; positivity
  have hranti : Antitone r := by
    intro k m hkm
    dsimp [r]
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hkm 1
  let v := fun k => matrixHilbertEmbedding dims hd U
    (matrixQuotientMk dims (U : Filter Nat) (A k))
  have hpair : ∀ m k, k ≤ m → dist (v m) (v k) < 3 * r k := by
    intro m k hkm
    have ht := dist_triangle (v m) x (v k)
    rw [dist_comm x (v k)] at ht
    have hm := hx m
    have hk := hx k
    have ha := hranti hkm
    have hp := hr k
    change dist (v m) x ≤ r m at hm
    change dist (v k) x ≤ r k at hk
    linarith
  let P : Nat → Nat → Prop := fun m n =>
    ∀ k ∈ Finset.range (m + 1), hsNorm ((A m).val n - (A k).val n) ≤ 3 * r k
  have hP : ∀ m, ∀ᶠ n in (U : Filter Nat), P m n := by
    intro m
    apply (eventually_all_finset (Finset.range (m + 1))).2
    intro k hk
    have hkm : k ≤ m := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
    exact ((matrixHilbertEmbedding_dist_tendsto dims hd U (A m) (A k)).eventually
      (gt_mem_nhds (hpair m k hkm))).mono (fun _ h => h.le)
  let B : BoundedMatrixSequence dims :=
    ⟨fun n => (A (diagonalDepth P n - 1)).val n, K, hK, fun n => hA _ n⟩
  let y := matrixHilbertEmbedding dims hd U (matrixQuotientMk dims (U : Filter Nat) B)
  have hy : ∀ k, dist y (v k) ≤ 3 * r k := by
    intro k
    apply le_of_tendsto (matrixHilbertEmbedding_dist_tendsto dims hd U B (A k))
    filter_upwards [diagonalDepth_pred_eventually P (U : Filter Nat) hU hP k] with n hn
    exact hn.2 k (Finset.mem_range.mpr (by omega))
  have hxy : y = x := by
    apply dist_eq_zero.mp
    apply le_antisymm _ dist_nonneg
    have hz : Tendsto (fun k => 4 * r k) atTop (𝓝 (0 : ℝ)) := by
      simpa only [mul_zero] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 4
    apply le_of_tendsto_of_tendsto' tendsto_const_nhds hz
    intro k
    have ht := dist_triangle y (v k) x
    have hb := hy k
    have hk := hx k
    change dist (v k) x ≤ r k at hk
    linarith
  exact ⟨B, fun n => ⟨diagonalDepth P n - 1, rfl⟩, hxy⟩

theorem matrixBoundedTraceBall_mem_of_fast_approximation
    (hU : (U : Filter Nat) ≤ atTop) (K : ℝ) (hK : 0 ≤ K)
    (A : Nat → BoundedMatrixSequence dims) (hA : ∀ k n, matrixOpNorm ((A k).val n) ≤ K)
    (x : MatrixTraceHilbert dims hd U)
    (hx : ∀ k, dist (matrixHilbertEmbedding dims hd U
      (matrixQuotientMk dims (U : Filter Nat) (A k))) x ≤ 1 / ((k : ℝ) + 1)) :
    x ∈ matrixBoundedTraceBall dims hd U K := by
  obtain ⟨B, hB, hBx⟩ := exists_matrixDiagonal_of_fast_approximation dims hd U hU K hK A hA x hx
  refine ⟨B, ?_, hBx⟩
  intro n
  obtain ⟨k, hk⟩ := hB n
  rw [hk]
  exact hA k n

theorem matrixBoundedTraceBall_isClosed (hU : (U : Filter Nat) ≤ atTop)
    (K : ℝ) (hK : 0 ≤ K) : IsClosed (matrixBoundedTraceBall dims hd U K) := by
  classical
  apply IsSeqClosed.isClosed
  intro v x hv hx
  have hchoose : ∀ k : Nat, ∃ n : Nat, dist (v n) x < 1 / ((k : ℝ) + 1) := by
    intro k
    obtain ⟨n, hn⟩ := Metric.tendsto_atTop.1 hx (1 / ((k : ℝ) + 1)) (by positivity)
    exact ⟨n, hn n le_rfl⟩
  choose s hs using hchoose
  have ha : ∀ k, ∃ A : BoundedMatrixSequence dims,
      (∀ n, matrixOpNorm (A.val n) ≤ K) ∧
      matrixHilbertEmbedding dims hd U (matrixQuotientMk dims (U : Filter Nat) A) = v (s k) :=
    fun k => hv (s k)
  choose A hA hAv using ha
  apply matrixBoundedTraceBall_mem_of_fast_approximation dims hd U hU K hK A hA x
  intro k
  rw [hAv k]
  exact (hs k).le

theorem matrixBoundedTraceBall_isComplete (hU : (U : Filter Nat) ≤ atTop)
    (K : ℝ) (hK : 0 ≤ K) : IsComplete (matrixBoundedTraceBall dims hd U K) :=
  (matrixBoundedTraceBall_isClosed dims hd U hU K hK).isComplete

instance matrixBoundedTraceBall_hyperfilter_completeSpace (K : NNReal) :
    CompleteSpace (matrixBoundedTraceBall dims hd (hyperfilter Nat) K) :=
  (matrixBoundedTraceBall_isComplete dims hd (hyperfilter Nat)
    Nat.hyperfilter_le_atTop K K.property).completeSpace_coe

end ThomGame.Analysis
