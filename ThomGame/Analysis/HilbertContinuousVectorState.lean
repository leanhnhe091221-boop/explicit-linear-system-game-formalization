module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.Tactic

/-! Positive real functionals obtained from actual Hilbert-space vector states. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open scoped CompactlySupported

variable {X : Type*} [TopologicalSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def continuousComplexify (f : C(X, ℝ)) : C(X, ℂ) where
  toFun x := (f x : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp f.continuous

@[simp] theorem continuousComplexify_apply (f : C(X, ℝ)) (x : X) :
    continuousComplexify f x = (f x : ℂ) := rfl

theorem continuousComplexify_add (f g : C(X, ℝ)) :
    continuousComplexify (f + g) = continuousComplexify f + continuousComplexify g := by
  ext x
  simp

theorem continuousComplexify_smul (r : ℝ) (f : C(X, ℝ)) :
    continuousComplexify (r • f) = (r : ℂ) • continuousComplexify f := by
  ext x
  simp

@[simp] theorem continuousComplexify_one : continuousComplexify (1 : C(X, ℝ)) = 1 := by
  ext x
  simp

def hilbertContinuousVectorState (π : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    C(X, ℝ) →ₗ[ℝ] ℝ where
  toFun f := (inner ℂ ξ (π (continuousComplexify f) ξ)).re
  map_add' f g := by
    rw [continuousComplexify_add, map_add]
    simp only [add_apply, inner_add_right, Complex.add_re]
  map_smul' r f := by
    rw [continuousComplexify_smul, map_smul]
    simp only [smul_apply, inner_smul_right, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, RingHom.id_apply, smul_eq_mul]

theorem hilbertContinuousVectorState_apply (π : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ξ : H) (f : C(X, ℝ)) :
    hilbertContinuousVectorState π ξ f = (inner ℂ ξ (π (continuousComplexify f) ξ)).re := rfl

theorem continuousComplexify_nonneg_factor (f : C(X, ℝ)) (hf : 0 ≤ f) :
    ∃ g : C(X, ℂ), continuousComplexify f = star g * g := by
  let g : C(X, ℂ) := ⟨fun x => (Real.sqrt (f x) : ℂ), by fun_prop⟩
  refine ⟨g, ?_⟩
  ext x
  change (f x : ℂ) = star (Real.sqrt (f x) : ℂ) * (Real.sqrt (f x) : ℂ)
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
  exact congrArg Complex.ofReal (Real.mul_self_sqrt (show 0 ≤ f x from hf x)).symm

theorem hilbertContinuousVectorState_nonneg (π : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ξ : H) (f : C(X, ℝ)) (hf : 0 ≤ f) : 0 ≤ hilbertContinuousVectorState π ξ f := by
  obtain ⟨g, hg⟩ := continuousComplexify_nonneg_factor f hf
  rw [hilbertContinuousVectorState_apply, hg, map_mul, map_star]
  change 0 ≤ (inner ℂ ξ ((π g).adjoint (π g ξ))).re
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact inner_self_nonneg (𝕜 := ℂ)

theorem hilbertContinuousVectorState_one (π : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    hilbertContinuousVectorState π ξ 1 = ‖ξ‖ ^ 2 := by
  rw [hilbertContinuousVectorState_apply, continuousComplexify_one, map_one]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) ξ

def hilbertCompactVectorState (π : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun f := hilbertContinuousVectorState π ξ f.toContinuousMap
      map_add' f g := map_add (hilbertContinuousVectorState π ξ) f.toContinuousMap g.toContinuousMap
      map_smul' r f := map_smul (hilbertContinuousVectorState π ξ) r f.toContinuousMap }
    (fun f hf => hilbertContinuousVectorState_nonneg π ξ f.toContinuousMap hf)

theorem hilbertCompactVectorState_apply (π : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ξ : H) (f : C_c(X, ℝ)) :
    hilbertCompactVectorState π ξ f = hilbertContinuousVectorState π ξ f.toContinuousMap := rfl

end ThomGame.Analysis
