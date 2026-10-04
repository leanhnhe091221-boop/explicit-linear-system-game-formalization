module

public import ThomGame.Analysis.MatrixResolventDerivative

/-!
# The resolvent potential

The potential used in ALT Lemma 3.2 is built from actual inverses and
normalized traces. Its derivative along a positive affine step is
obtained by differentiating those matrices.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {d : Nat}

noncomputable def normalizedTraceRealCLM : CMatrix d →L[ℝ] ℝ :=
  ({ toFun := fun A => (normalizedTrace A).re
     map_add' := fun A B => by simp
     map_smul' := fun c A => by simp [normalizedTrace]; ring } :
    CMatrix d →ₗ[ℝ] ℝ).toContinuousLinearMap

@[simp] theorem normalizedTraceRealCLM_apply (A : CMatrix d) :
    normalizedTraceRealCLM A = (normalizedTrace A).re := rfl

theorem normalizedTrace_re_hasDerivAt {A : ℝ → CMatrix d} {B : CMatrix d} {t : ℝ}
    (hA : HasDerivAt A B t) :
    HasDerivAt (fun s => (normalizedTrace (A s)).re) (normalizedTrace B).re t := by
  simpa only [normalizedTraceRealCLM_apply, Function.comp_def] using!
    normalizedTraceRealCLM.hasFDerivAt.comp_hasDerivAt t hA

noncomputable def matrixResolventPotential (A U : CMatrix d) : ℝ :=
  (normalizedTrace (A * U * A⁻¹ * U)).re - 1

theorem matrixResolventPotential_hasDerivAt {lam t : ℝ} {S F : CMatrix d}
    (hlam : 0 < lam) (hS : 0 ≤ S) (hF : 0 ≤ F) (ht : 0 ≤ t) (U : CMatrix d) :
    HasDerivAt (fun s : ℝ => matrixResolventPotential (lam • 1 + S + s • F) U)
      (normalizedTrace (F * U * matrixAffineResolvent lam S F t * U -
        (lam • 1 + S + t • F) * U * matrixAffineResolvent lam S F t * F *
          matrixAffineResolvent lam S F t * U)).re t := by
  have hA : HasDerivAt (fun s : ℝ => lam • (1 : CMatrix d) + S + s • F) F t := by
    simpa using ((hasDerivAt_id t).smul_const F).const_add (lam • (1 : CMatrix d) + S)
  have hD := matrixAffineResolvent_hasDerivAt hlam hS hF ht
  have he := (normalizedTrace_re_hasDerivAt (((hA.mul_const U).mul hD).mul_const U)).sub_const 1
  convert! he using 1
  congr 2
  noncomm_ring

end ThomGame.Analysis
