module

public import ThomGame.Analysis.MatrixFiniteTraceProperties
public import ThomGame.Analysis.TraceClampEstimate
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# The trace two-distance on the concrete finite operator algebra

Evaluation at the cyclic separating unit vector realizes the trace
inner product. Star preserves its norm, taking the self-adjoint real
part is contractive, and clipping decreases distance to bounded
self-adjoint targets.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped ComplexOrder

variable {ι : Type*} (dims : ι → Nat) (hd : ∀ i, 0 < dims i) (U : Ultrafilter ι)

instance matrixFiniteOperatorAlgebra_starOrderedRing : StarOrderedRing (MatrixFiniteOperatorAlgebra dims hd U) :=
  Subtype.starOrderedRing (𝕜 := ℂ) (matrixOperatorAlgebra dims hd U)

noncomputable def matrixFiniteVector :
    MatrixFiniteOperatorAlgebra dims hd U →ₗ[ℂ] MatrixTraceHilbert dims hd U where
  toFun T := T.val (matrixHilbertEmbedding dims hd U 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem matrixFiniteVector_embedding (x : MatrixTracialQuotient dims (U : Filter ι)) :
    matrixFiniteVector dims hd U (matrixFiniteEmbedding dims hd U x) = matrixHilbertEmbedding dims hd U x := by
  change matrixLeftRepresentation dims hd U x (matrixHilbertEmbedding dims hd U 1) = _
  rw [matrixLeftRepresentation_apply, mul_one]

theorem matrixFiniteVector_inner (S T : MatrixFiniteOperatorAlgebra dims hd U) :
    inner ℂ (matrixFiniteVector dims hd U S) (matrixFiniteVector dims hd U T) =
      matrixFiniteTrace dims hd U (star S * T) := by
  change inner ℂ (S.val (matrixHilbertEmbedding dims hd U 1)) (T.val (matrixHilbertEmbedding dims hd U 1)) =
    inner ℂ (matrixHilbertEmbedding dims hd U 1)
      ((star S.val) (T.val (matrixHilbertEmbedding dims hd U 1)))
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

theorem matrixFiniteVector_eq_zero_iff (T : MatrixFiniteOperatorAlgebra dims hd U) :
    matrixFiniteVector dims hd U T = 0 ↔ T = 0 := by
  constructor
  · intro h
    apply (matrixFiniteTrace_faithful dims hd U T).mp
    rw [← matrixFiniteVector_inner, h, inner_zero_left]
  · rintro rfl
    exact map_zero _

theorem matrixFiniteVector_injective : Function.Injective (matrixFiniteVector dims hd U) := by
  intro S T h
  apply sub_eq_zero.mp
  apply (matrixFiniteVector_eq_zero_iff dims hd U (S - T)).mp
  rw [map_sub, h, sub_self]

noncomputable def matrixFiniteRealTrace : MatrixFiniteOperatorAlgebra dims hd U →ₗ[ℝ] ℝ :=
  Complex.reCLM.toLinearMap.comp ((matrixFiniteTrace dims hd U).toLinearMap.restrictScalars ℝ)

theorem matrixFiniteRealTrace_nonneg (T : MatrixFiniteOperatorAlgebra dims hd U) (hT : 0 ≤ T) :
    0 ≤ matrixFiniteRealTrace dims hd U T :=
  (matrixFiniteTrace_nonneg dims hd U T hT).1

theorem matrixFiniteRealTrace_mul_comm (S T : MatrixFiniteOperatorAlgebra dims hd U) :
    matrixFiniteRealTrace dims hd U (S * T) = matrixFiniteRealTrace dims hd U (T * S) :=
  congrArg Complex.re (matrixFiniteTrace_mul_comm dims hd U S T)

theorem matrixFiniteRealTrace_gram (T : MatrixFiniteOperatorAlgebra dims hd U) :
    matrixFiniteRealTrace dims hd U (star T * T) = ‖matrixFiniteVector dims hd U T‖ ^ 2 := by
  change (matrixFiniteTrace dims hd U (star T * T)).re = _
  rw [← matrixFiniteVector_inner]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (matrixFiniteVector dims hd U T)

theorem matrixFiniteVector_star_norm (T : MatrixFiniteOperatorAlgebra dims hd U) :
    ‖matrixFiniteVector dims hd U (star T)‖ = ‖matrixFiniteVector dims hd U T‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← matrixFiniteRealTrace_gram, ← matrixFiniteRealTrace_gram, star_star, matrixFiniteRealTrace_mul_comm]

theorem matrixFiniteVector_realPart_norm_le (T : MatrixFiniteOperatorAlgebra dims hd U) :
    ‖matrixFiniteVector dims hd U (realPart T)‖ ≤ ‖matrixFiniteVector dims hd U T‖ := by
  rw [realPart_apply_coe, LinearMap.map_smul_of_tower, map_add, norm_smul,
    Real.norm_of_nonneg (by positivity : 0 ≤ (2 : ℝ)⁻¹)]
  have h := norm_add_le (matrixFiniteVector dims hd U T) (matrixFiniteVector dims hd U (star T))
  rw [matrixFiniteVector_star_norm] at h
  linarith

theorem matrixFiniteRealTrace_selfAdjoint_square (T : MatrixFiniteOperatorAlgebra dims hd U)
    (hT : IsSelfAdjoint T) : matrixFiniteRealTrace dims hd U (T * T) = ‖matrixFiniteVector dims hd U T‖ ^ 2 := by
  simpa only [hT.star_eq] using matrixFiniteRealTrace_gram dims hd U T

theorem matrixFiniteVector_realPart_dist_le (S T : MatrixFiniteOperatorAlgebra dims hd U)
    (hT : IsSelfAdjoint T) :
    dist (matrixFiniteVector dims hd U (realPart S)) (matrixFiniteVector dims hd U T) ≤
      dist (matrixFiniteVector dims hd U S) (matrixFiniteVector dims hd U T) := by
  have h := matrixFiniteVector_realPart_norm_le dims hd U (S - T)
  have hp : (realPart (S - T) : MatrixFiniteOperatorAlgebra dims hd U) = (realPart S : MatrixFiniteOperatorAlgebra dims hd U) - T := by
    rw [map_sub]
    change (realPart S : MatrixFiniteOperatorAlgebra dims hd U) - (realPart T : MatrixFiniteOperatorAlgebra dims hd U) = _
    rw [hT.coe_realPart]
  rw [hp, map_sub, map_sub] at h
  simpa only [dist_eq_norm] using h

theorem matrixFiniteVector_clamp_dist_le (K : ℝ) (hK : 0 ≤ K)
    (S T : MatrixFiniteOperatorAlgebra dims hd U) (hS : IsSelfAdjoint S) (hT : IsSelfAdjoint T)
    (hbound : ‖T‖ ≤ K) :
    dist (matrixFiniteVector dims hd U (cstarNormClamp K S)) (matrixFiniteVector dims hd U T) ≤
      dist (matrixFiniteVector dims hd U S) (matrixFiniteVector dims hd U T) := by
  have h := trace_clamp_sq_sub_le (matrixFiniteRealTrace dims hd U) (matrixFiniteRealTrace_nonneg dims hd U)
    (matrixFiniteRealTrace_mul_comm dims hd U) K hK S T hS hT hbound
  rw [matrixFiniteRealTrace_selfAdjoint_square dims hd U _ ((cstarNormClamp_selfAdjoint K S).sub hT),
    matrixFiniteRealTrace_selfAdjoint_square dims hd U _ (hS.sub hT), map_sub, map_sub] at h
  apply (sq_le_sq₀ dist_nonneg dist_nonneg).mp
  simpa only [dist_eq_norm] using h

end ThomGame.Analysis
