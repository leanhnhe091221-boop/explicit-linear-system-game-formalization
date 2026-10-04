module

public import ThomGame.Analysis.MatrixTracialAlgebra
public import ThomGame.Analysis.NormalizedTraceBounds
public import Mathlib.Topology.MetricSpace.ProperSpace.Real

/-!
# The normalized ultralimit trace on bounded matrix sequences

Uniform operator bounds put the normalized traces in a compact complex
ball. Their ultralimit is therefore an actual limit. It is complex linear,
tracial, star compatible, normalized, and zero on the 2-null ideal.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

variable {ι : Type*} (dims : ι → Nat)

noncomputable def matrixSequenceUltratrace (U : Ultrafilter ι) (A : BoundedMatrixSequence dims) : ℂ :=
  limUnder (U : Filter ι) (fun i => normalizedTrace (A.val i))

variable (hd : ∀ i, 0 < dims i) (U : Ultrafilter ι)

include hd

theorem matrixSequenceUltratrace_tendsto (A : BoundedMatrixSequence dims) :
    Tendsto (fun i => normalizedTrace (A.val i)) (U : Filter ι)
      (𝓝 (matrixSequenceUltratrace dims U A)) := by
  apply tendsto_nhds_limUnder
  obtain ⟨K, _, hK⟩ := BoundedMatrixSequence.bound dims A
  let f : ι → ℂ := fun i => normalizedTrace (A.val i)
  have hbound : ∀ i, f i ∈ Metric.closedBall (0 : ℂ) K := by
    intro i
    let : NeZero (dims i) := ⟨Nat.ne_of_gt (hd i)⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      (norm_normalizedTrace_le_matrixOpNorm (A.val i)).trans (hK i)
  obtain ⟨z, _, hz⟩ := (isCompact_closedBall (0 : ℂ) K).ultrafilter_le_nhds (U.map f)
    (le_principal_iff.mpr (by
      change ∀ᶠ i in (U : Filter ι), f i ∈ Metric.closedBall (0 : ℂ) K
      exact Eventually.of_forall hbound))
  exact ⟨z, hz⟩

@[simp] theorem matrixSequenceUltratrace_zero : matrixSequenceUltratrace dims U 0 = 0 := by
  apply tendsto_nhds_unique (matrixSequenceUltratrace_tendsto dims hd U 0)
  change Tendsto (fun i : ι => normalizedTrace (0 : CMatrix (dims i))) _ _
  simpa only [normalizedTrace_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : ℂ)) (U : Filter ι) (𝓝 0))

@[simp] theorem matrixSequenceUltratrace_one : matrixSequenceUltratrace dims U 1 = 1 := by
  apply tendsto_nhds_unique (matrixSequenceUltratrace_tendsto dims hd U 1)
  have hone (i : ι) : normalizedTrace ((1 : BoundedMatrixSequence dims).val i) = 1 := by
    let : NeZero (dims i) := ⟨Nat.ne_of_gt (hd i)⟩
    exact normalizedTrace_one
  simp_rw [hone]
  exact tendsto_const_nhds

theorem matrixSequenceUltratrace_add (A B : BoundedMatrixSequence dims) :
    matrixSequenceUltratrace dims U (A + B) =
      matrixSequenceUltratrace dims U A + matrixSequenceUltratrace dims U B := by
  apply tendsto_nhds_unique (matrixSequenceUltratrace_tendsto dims hd U (A + B))
  change Tendsto (fun i => normalizedTrace (A.val i + B.val i)) _ _
  simpa only [normalizedTrace_add] using
    (matrixSequenceUltratrace_tendsto dims hd U A).add (matrixSequenceUltratrace_tendsto dims hd U B)

theorem matrixSequenceUltratrace_sub (A B : BoundedMatrixSequence dims) :
    matrixSequenceUltratrace dims U (A - B) =
      matrixSequenceUltratrace dims U A - matrixSequenceUltratrace dims U B := by
  apply tendsto_nhds_unique (matrixSequenceUltratrace_tendsto dims hd U (A - B))
  change Tendsto (fun i => normalizedTrace (A.val i - B.val i)) _ _
  simpa only [normalizedTrace_sub] using
    (matrixSequenceUltratrace_tendsto dims hd U A).sub (matrixSequenceUltratrace_tendsto dims hd U B)

theorem matrixSequenceUltratrace_smul (c : ℂ) (A : BoundedMatrixSequence dims) :
    matrixSequenceUltratrace dims U (c • A) = c * matrixSequenceUltratrace dims U A := by
  apply tendsto_nhds_unique (matrixSequenceUltratrace_tendsto dims hd U (c • A))
  change Tendsto (fun i => normalizedTrace (c • A.val i)) _ _
  simpa only [normalizedTrace_smul] using
    (matrixSequenceUltratrace_tendsto dims hd U A).const_mul c

theorem matrixSequenceUltratrace_star (A : BoundedMatrixSequence dims) :
    matrixSequenceUltratrace dims U (star A) = star (matrixSequenceUltratrace dims U A) := by
  apply tendsto_nhds_unique (matrixSequenceUltratrace_tendsto dims hd U (star A))
  change Tendsto (fun i => normalizedTrace (star (A.val i))) _ _
  simpa only [normalizedTrace_star] using (matrixSequenceUltratrace_tendsto dims hd U A).star

theorem matrixSequenceUltratrace_mul_comm (A B : BoundedMatrixSequence dims) :
    matrixSequenceUltratrace dims U (A * B) = matrixSequenceUltratrace dims U (B * A) := by
  apply tendsto_nhds_unique (matrixSequenceUltratrace_tendsto dims hd U (A * B))
  change Tendsto (fun i => normalizedTrace (A.val i * B.val i)) _ _
  have h := matrixSequenceUltratrace_tendsto dims hd U (B * A)
  change Tendsto (fun i => normalizedTrace (B.val i * A.val i)) _ _ at h
  simpa only [normalizedTrace_mul_comm] using h

theorem matrixSequenceUltratrace_null (A : BoundedMatrixSequence dims)
    (hA : A ∈ matrixNullIdeal dims (U : Filter ι)) : matrixSequenceUltratrace dims U A = 0 := by
  apply tendsto_nhds_unique (matrixSequenceUltratrace_tendsto dims hd U A)
  apply squeeze_zero_norm (fun i => ?_) hA
  let : NeZero (dims i) := ⟨Nat.ne_of_gt (hd i)⟩
  exact norm_normalizedTrace_le_hsNorm (A.val i)

theorem matrixSequenceUltratrace_eq_of_null_sub (A B : BoundedMatrixSequence dims)
    (hAB : A - B ∈ matrixNullIdeal dims (U : Filter ι)) :
    matrixSequenceUltratrace dims U A = matrixSequenceUltratrace dims U B := by
  apply sub_eq_zero.mp
  rw [← matrixSequenceUltratrace_sub dims hd U]
  exact matrixSequenceUltratrace_null dims hd U _ hAB

end ThomGame.Analysis
