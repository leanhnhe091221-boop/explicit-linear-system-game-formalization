module

public import ThomGame.Analysis.MatrixFiniteOperatorAlgebra
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Algebra.Order.Module.PositiveLinearMap

/-!
# Positivity and norm of the finite operator algebra trace

The identity vector is a unit vector. Its trace is positive for the
actual Loewner order on Hilbert-space operators and has operator norm
one. These assertions concern the concrete operator algebra, including
elements added by weak operator closure.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology ComplexOrder

variable {ι : Type*} (dims : ι → Nat) (hd : ∀ i, 0 < dims i) (U : Ultrafilter ι)

theorem matrixUnitVector_norm : ‖matrixHilbertEmbedding dims hd U 1‖ = 1 := by
  change ‖((matrixTraceSpaceEquiv dims hd U 1 : MatrixTraceSpace dims hd U) : MatrixTraceHilbert dims hd U)‖ = 1
  rw [UniformSpace.Completion.norm_coe, matrixTraceSpace_norm]
  simp only [star_one, one_mul, matrixUltratrace_one, Complex.one_re, Real.sqrt_one]

instance matrixFiniteOperatorAlgebra_nontrivial : Nontrivial (MatrixFiniteOperatorAlgebra dims hd U) := by
  apply nontrivial_of_ne (1 : MatrixFiniteOperatorAlgebra dims hd U) 0
  intro h
  have ht := congrArg (matrixFiniteTrace dims hd U) h
  rw [matrixFiniteTrace_one, map_zero] at ht
  exact one_ne_zero ht

theorem matrixFiniteTrace_norm_le (T : MatrixFiniteOperatorAlgebra dims hd U) :
    ‖matrixFiniteTrace dims hd U T‖ ≤ ‖T‖ := by
  change ‖inner ℂ (matrixHilbertEmbedding dims hd U 1)
    (T.val (matrixHilbertEmbedding dims hd U 1))‖ ≤ ‖T.val‖
  calc
    _ ≤ ‖matrixHilbertEmbedding dims hd U 1‖ * ‖T.val (matrixHilbertEmbedding dims hd U 1)‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖matrixHilbertEmbedding dims hd U 1‖ *
        (‖T.val‖ * ‖matrixHilbertEmbedding dims hd U 1‖) :=
      mul_le_mul_of_nonneg_left (T.val.le_opNorm _) (norm_nonneg _)
    _ = ‖T.val‖ := by rw [matrixUnitVector_norm, mul_one, one_mul]

theorem matrixFiniteTrace_norm : ‖matrixFiniteTrace dims hd U‖ = 1 := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro T
    simpa only [one_mul] using matrixFiniteTrace_norm_le dims hd U T
  · have h := (matrixFiniteTrace dims hd U).le_opNorm (1 : MatrixFiniteOperatorAlgebra dims hd U)
    simpa only [matrixFiniteTrace_one, norm_one, mul_one] using h

theorem matrixFiniteTrace_nonneg (T : MatrixFiniteOperatorAlgebra dims hd U) (hT : 0 ≤ T) :
    0 ≤ matrixFiniteTrace dims hd U T := by
  have hp : T.val.IsPositive := ContinuousLinearMap.nonneg_iff_isPositive.mp hT
  exact hp.inner_nonneg_right (matrixHilbertEmbedding dims hd U 1)

noncomputable def matrixFinitePositiveTrace : MatrixFiniteOperatorAlgebra dims hd U →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (matrixFiniteTrace dims hd U).toLinearMap (matrixFiniteTrace_nonneg dims hd U)

theorem matrixFiniteTrace_monotone : Monotone (matrixFiniteTrace dims hd U) :=
  (matrixFinitePositiveTrace dims hd U).monotone

theorem matrixFiniteTrace_wot_tendsto {κ : Type*} {L : Filter κ}
    {f : κ → MatrixFiniteOperatorAlgebra dims hd U} {T : MatrixFiniteOperatorAlgebra dims hd U}
    (hf : Tendsto (fun i => ContinuousLinearMapWOT.ofCLM (f i).val) L
      (𝓝 (ContinuousLinearMapWOT.ofCLM T.val))) :
    Tendsto (fun i => matrixFiniteTrace dims hd U (f i)) L (𝓝 (matrixFiniteTrace dims hd U T)) :=
  (matrixVectorTrace_continuous dims hd U).continuousAt.tendsto.comp hf

end ThomGame.Analysis
