module

public import ThomGame.Analysis.MatrixFrameQuotientEquivalence
public import ThomGame.Analysis.MatrixUltratrace

/-!
# Preservation of the actual normalized ultratrace by stabilization

At each coordinate the trace is multiplied by d/N. This ratio tends to
one, so the constructed star equivalence preserves the ultralimit trace.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix Filter
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

theorem matrixFrameLift_normalizedTrace {d n : Nat} (hd : 0 < d) (hn : 0 < n)
    (F : Matrix (Fin n) (Fin d) ℂ) (hF : Fᴴ * F = 1) (X : CMatrix d) :
    normalizedTrace (matrixFrameLift F X) = ((d : ℂ) / n) * normalizedTrace X := by
  have ht : (matrixFrameLift F X).trace = X.trace := by
    rw [matrixFrameLift, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hF, Matrix.one_mul]
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  unfold normalizedTrace
  rw [ht]
  field_simp

variable {ι : Type*} (dims large : ι → Nat)
    (F : (i : ι) → Matrix (Fin (large i)) (Fin (dims i)) ℂ)
    (hF : ∀ i, (F i)ᴴ * F i = 1) (hd : ∀ i, 0 < dims i) (hN : ∀ i, 0 < large i)
    (U : Ultrafilter ι) (hratio : Tendsto (fun i => (large i : ℝ) / dims i) (U : Filter ι) (𝓝 1))

include hd hN hratio in
theorem matrixFrameSequenceLift_ultratrace (A : BoundedMatrixSequence dims) :
    matrixSequenceUltratrace large U (matrixFrameSequenceLift dims large F hF A) =
      matrixSequenceUltratrace dims U A := by
  apply tendsto_nhds_unique (matrixSequenceUltratrace_tendsto large hN U _)
  have hr : Tendsto (fun i => (dims i : ℂ) / large i) (U : Filter ι) (𝓝 1) := by
    simpa only [Function.comp_def, Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_one] using
      (Complex.continuous_ofReal.tendsto 1).comp
        (matrixDimensionRatio_inverse_tendsto dims large (U : Filter ι) hratio)
  change Tendsto (fun i => normalizedTrace (matrixFrameLift (F i) (A.val i))) _ _
  have he : (fun i => normalizedTrace (matrixFrameLift (F i) (A.val i))) =
      (fun i => ((dims i : ℂ) / large i) * normalizedTrace (A.val i)) :=
    funext fun i => matrixFrameLift_normalizedTrace (hd i) (hN i) (F i) (hF i) (A.val i)
  rw [he]
  simpa using hr.mul (matrixSequenceUltratrace_tendsto dims hd U A)

theorem matrixFrameQuotientEquiv_trace (x : MatrixTracialQuotient dims (U : Filter ι)) :
    matrixUltratrace large hN U (matrixFrameQuotientEquiv dims large F hF hd hN (U : Filter ι) hratio x) =
      matrixUltratrace dims hd U x := by
  obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims (U : Filter ι) x
  exact matrixFrameSequenceLift_ultratrace dims large F hF hd hN U hratio A

end ThomGame.Analysis
