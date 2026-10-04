module

public import ThomGame.Quantum.ProjectiveMeasurement
public import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-! Local measurements act on the two actual Hilbert tensor factors. -/

@[expose] public section
namespace ThomGame.Quantum.ProjectiveMeasurement

open scoped TensorProduct BigOperators

variable {H K O : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [CompleteSpace (H ⊗[ℂ] K)] [Fintype O]

noncomputable def tensorLeft (P : ProjectiveMeasurement H O) :
    ProjectiveMeasurement (H ⊗[ℂ] K) O where
  proj a := (P.proj a).rTensor K
  selfAdjoint a := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff']
    simp only [ContinuousLinearMap.adjoint_rTensor, (P.selfAdjoint a).adjoint_eq]
  idempotent a := by rw [← ContinuousLinearMap.rTensor_mul, P.idempotent]
  orthogonal a b hab := by
    rw [← ContinuousLinearMap.rTensor_mul, P.orthogonal a b hab]
    exact ContinuousLinearMap.rTensor_zero K
  complete := by
    let L : (H →L[ℂ] H) →+ ((H ⊗[ℂ] K) →L[ℂ] (H ⊗[ℂ] K)) := {
      toFun := fun T => T.rTensor K
      map_zero' := by simp
      map_add' := by intros; simp }
    change ∑ a, L (P.proj a) = 1
    rw [← map_sum, P.complete]
    exact ContinuousLinearMap.rTensor_one K

noncomputable def tensorRight (P : ProjectiveMeasurement K O) :
    ProjectiveMeasurement (H ⊗[ℂ] K) O where
  proj a := (P.proj a).lTensor H
  selfAdjoint a := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff']
    simp only [ContinuousLinearMap.adjoint_lTensor, (P.selfAdjoint a).adjoint_eq]
  idempotent a := by rw [← ContinuousLinearMap.lTensor_mul, P.idempotent]
  orthogonal a b hab := by
    rw [← ContinuousLinearMap.lTensor_mul, P.orthogonal a b hab]
    exact ContinuousLinearMap.lTensor_zero H
  complete := by
    let L : (K →L[ℂ] K) →+ ((H ⊗[ℂ] K) →L[ℂ] (H ⊗[ℂ] K)) := {
      toFun := fun T => T.lTensor H
      map_zero' := by simp
      map_add' := by intros; simp }
    change ∑ a, L (P.proj a) = 1
    rw [← map_sum, P.complete]
    exact ContinuousLinearMap.lTensor_one H

theorem tensorLeft_tmul (P : ProjectiveMeasurement H O) (a : O) (ξ : H) (ζ : K) :
    (P.tensorLeft (K := K)).proj a (ξ ⊗ₜ[ℂ] ζ) = P.proj a ξ ⊗ₜ[ℂ] ζ := rfl

theorem tensorRight_tmul (P : ProjectiveMeasurement K O) (a : O) (ξ : H) (ζ : K) :
    (P.tensorRight (H := H)).proj a (ξ ⊗ₜ[ℂ] ζ) = ξ ⊗ₜ[ℂ] P.proj a ζ := rfl

theorem tensor_commute {O' : Type*} [Fintype O']
    (P : ProjectiveMeasurement H O) (Q : ProjectiveMeasurement K O') (a : O) (b : O') :
    Commute ((P.tensorLeft (K := K)).proj a) ((Q.tensorRight (H := H)).proj b) := by
  change (P.proj a).rTensor K ∘L (Q.proj b).lTensor H =
    (Q.proj b).lTensor H ∘L (P.proj a).rTensor K
  rw [ContinuousLinearMap.rTensor_comp_lTensor, ContinuousLinearMap.lTensor_comp_rTensor]

end ThomGame.Quantum.ProjectiveMeasurement
