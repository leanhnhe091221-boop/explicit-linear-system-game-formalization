module

public import ThomGame.Analysis.MatrixUltratrace
public import Mathlib.Analysis.InnerProductSpace.Completion

/-!
# The Hilbert space of the faithful matrix trace

The algebraic quotient has the positive definite inner product
`inner x y = trace (star x * y)`. A separate type carries its 2-norm,
so it cannot be confused with an operator norm. Its Hilbert completion
contains the actual quotient faithfully and densely.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

variable {ι : Type*}

def MatrixTraceSpace (dims : ι → Nat) (_hd : ∀ i, 0 < dims i) (U : Ultrafilter ι) : Type _ :=
  MatrixTracialQuotient dims (U : Filter ι)

variable (dims : ι → Nat) (hd : ∀ i, 0 < dims i) (U : Ultrafilter ι)

instance matrixTraceSpaceAddCommGroup : AddCommGroup (MatrixTraceSpace dims hd U) :=
  inferInstanceAs (AddCommGroup (MatrixTracialQuotient dims (U : Filter ι)))

instance matrixTraceSpaceModule : Module ℂ (MatrixTraceSpace dims hd U) :=
  inferInstanceAs (Module ℂ (MatrixTracialQuotient dims (U : Filter ι)))

def matrixTraceSpaceEquiv : MatrixTracialQuotient dims (U : Filter ι) ≃ₗ[ℂ] MatrixTraceSpace dims hd U :=
  LinearEquiv.refl ℂ _

@[instance_reducible] noncomputable def matrixTraceInnerCore : InnerProductSpace.Core ℂ (MatrixTraceSpace dims hd U) where
  inner x y := matrixUltratrace dims hd U
    (star ((matrixTraceSpaceEquiv dims hd U).symm x) * (matrixTraceSpaceEquiv dims hd U).symm y)
  conj_inner_symm x y := by
    change star (matrixUltratrace dims hd U _) = matrixUltratrace dims hd U _
    rw [← matrixUltratrace_star, star_mul, star_star]
  re_inner_nonneg x := matrixUltratrace_gram_nonneg dims hd U _
  add_left x y z := by
    rw [map_add, star_add, add_mul, matrixUltratrace_add]
  smul_left x y c := by
    rw [map_smul, star_smul, smul_mul_assoc, matrixUltratrace_smul]
    rfl
  definite x hx := by
    apply (matrixTraceSpaceEquiv dims hd U).symm.injective
    exact (matrixUltratrace_faithful dims hd U _).mp hx

noncomputable instance matrixTraceSpaceNormedAddCommGroup : NormedAddCommGroup (MatrixTraceSpace dims hd U) :=
  InnerProductSpace.Core.toNormedAddCommGroup (cd := matrixTraceInnerCore dims hd U)

noncomputable instance matrixTraceSpaceInnerProductSpace : InnerProductSpace ℂ (MatrixTraceSpace dims hd U) :=
  letI := matrixTraceInnerCore dims hd U
  InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (MatrixTraceSpace dims hd U))

theorem matrixTraceSpace_inner (x y : MatrixTracialQuotient dims (U : Filter ι)) :
    inner ℂ (matrixTraceSpaceEquiv dims hd U x) (matrixTraceSpaceEquiv dims hd U y) =
      matrixUltratrace dims hd U (star x * y) := rfl

theorem matrixTraceSpace_norm (x : MatrixTracialQuotient dims (U : Filter ι)) :
    ‖matrixTraceSpaceEquiv dims hd U x‖ = Real.sqrt (matrixUltratrace dims hd U (star x * x)).re := rfl

theorem matrixTraceSpace_norm_tendsto (A : BoundedMatrixSequence dims) :
    Tendsto (fun i => hsNorm (A.val i)) (U : Filter ι)
      (𝓝 ‖matrixTraceSpaceEquiv dims hd U (matrixQuotientMk dims (U : Filter ι) A)‖) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    (matrixUltratrace_gram_tendsto dims hd U A)
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp h
  simpa only [Function.comp_def, ← Complex.ofReal_pow, Complex.ofReal_re,
    Real.sqrt_sq (hsNorm_nonneg _), matrixTraceSpace_norm] using hs

abbrev MatrixTraceHilbert := UniformSpace.Completion (MatrixTraceSpace dims hd U)

noncomputable def matrixHilbertEmbedding : MatrixTracialQuotient dims (U : Filter ι) →ₗ[ℂ] MatrixTraceHilbert dims hd U :=
  UniformSpace.Completion.toComplₗᵢ.toLinearMap.comp (matrixTraceSpaceEquiv dims hd U).toLinearMap

theorem matrixHilbertEmbedding_injective : Function.Injective (matrixHilbertEmbedding dims hd U) :=
  (UniformSpace.Completion.toComplₗᵢ : MatrixTraceSpace dims hd U →ₗᵢ[ℂ] MatrixTraceHilbert dims hd U).injective.comp
    (matrixTraceSpaceEquiv dims hd U).injective

theorem matrixHilbertEmbedding_dense : DenseRange (matrixHilbertEmbedding dims hd U) := by
  exact UniformSpace.Completion.denseRange_coe.comp
    (matrixTraceSpaceEquiv dims hd U).surjective.denseRange
    (UniformSpace.Completion.continuous_coe (MatrixTraceSpace dims hd U))

theorem matrixHilbertEmbedding_inner (x y : MatrixTracialQuotient dims (U : Filter ι)) :
    inner ℂ (matrixHilbertEmbedding dims hd U x) (matrixHilbertEmbedding dims hd U y) =
      matrixUltratrace dims hd U (star x * y) := by
  exact UniformSpace.Completion.inner_coe (𝕜 := ℂ)
    (matrixTraceSpaceEquiv dims hd U x) (matrixTraceSpaceEquiv dims hd U y)

end ThomGame.Analysis
