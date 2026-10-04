module

public import ThomGame.Quantum.TensorStateMatrix
public import ThomGame.Analysis.MatrixDensityIntertwiner

/-! The actual Bob reduced density and its positive square root. -/

@[expose] public section
namespace ThomGame.Quantum

open Analysis Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable def reducedDensity {d e : Nat} (ψ : BipartiteSpace d e) : CMatrix e :=
  tensorStateMatrix d e ψ * (tensorStateMatrix d e ψ)ᴴ

noncomputable def densityRoot {d e : Nat} (ψ : BipartiteSpace d e) : CMatrix e :=
  matrixRectAbs (tensorStateMatrix d e ψ)ᴴ

theorem reducedDensity_nonneg {d e : Nat} (ψ : BipartiteSpace d e) : 0 ≤ reducedDensity ψ :=
  (Matrix.posSemidef_self_mul_conjTranspose _).nonneg

theorem densityRoot_nonneg {d e : Nat} (ψ : BipartiteSpace d e) : 0 ≤ densityRoot ψ :=
  matrixRectAbs_nonneg _

theorem densityRoot_sq {d e : Nat} (ψ : BipartiteSpace d e) :
    densityRoot ψ * densityRoot ψ = reducedDensity ψ := by
  simp only [densityRoot, matrixRectAbs_mul_self, Matrix.conjTranspose_conjTranspose, reducedDensity]

theorem densityRoot_sqrt {d e : Nat} (ψ : BipartiteSpace d e) :
    densityRoot ψ = CFC.sqrt (reducedDensity ψ) := by
  simp only [densityRoot, matrixRectAbs, Matrix.conjTranspose_conjTranspose, reducedDensity]

theorem densityRoot_norm {d e : Nat} (ψ : BipartiteSpace d e) :
    rectHSNorm 1 (densityRoot ψ) = ‖ψ‖ := by
  rw [densityRoot, rectHSNorm_rectAbs, rectHSNorm_conjTranspose, tensorStateMatrix_norm]

theorem reducedDensity_trace {d e : Nat} (ψ : BipartiteSpace d e) :
    (reducedDensity ψ).trace = ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
  have ht := rectangular_trace_gram (tensorStateMatrix d e ψ)ᴴ
  rw [Matrix.conjTranspose_conjTranspose] at ht
  have hn := congrArg (fun t : ℝ => t ^ 2) (tensorStateMatrix_norm ψ)
  rw [← rectHSNorm_conjTranspose 1 (tensorStateMatrix d e ψ), rectHSNorm_sq,
    Nat.cast_one, div_one] at hn
  exact ht.trans (congrArg (fun t : ℝ => (t : ℂ)) hn)

theorem densityRoot_weighted_norm {d e : Nat} (ψ : BipartiteSpace d e)
    (B : LocalSpace e →L[ℂ] LocalSpace e) :
    rectHSNorm 1 (localMatrix B * densityRoot ψ) = ‖B.lTensor (LocalSpace d) ψ‖ := by
  rw [densityRoot, rectHSNorm_mul_left_density, tensorStateMatrix_bob_norm]

theorem densityRoot_weighted_sub_smul_norm {d e : Nat} (ψ : BipartiteSpace d e)
    (B : LocalSpace e →L[ℂ] LocalSpace e) (z : ℂ) :
    rectHSNorm 1 ((localMatrix B - z • 1) * densityRoot ψ) =
      ‖B.lTensor (LocalSpace d) ψ - z • ψ‖ := by
  rw [densityRoot, rectHSNorm_mul_left_density, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul,
    tensorStateMatrix_bob_sub_smul_norm]

theorem densityRoot_commutator_le {d e : Nat} (ψ : BipartiteSpace d e)
    (A : LocalSpace d →L[ℂ] LocalSpace d) (B : LocalSpace e →L[ℂ] LocalSpace e)
    (hA : IsSelfAdjoint A) (hAq : A * A = 1) (hB : IsSelfAdjoint B) (hBq : B * B = 1) :
    rectHSNorm 1 (localMatrix B * densityRoot ψ - densityRoot ψ * localMatrix B) ≤
      Real.sqrt 2 * ‖B.lTensor (LocalSpace d) ψ - A.rTensor (LocalSpace e) ψ‖ := by
  have h := rectHSNorm_left_density_commutator_le 1 (localMatrixUnitary B hB hBq)
    (Matrix.UnitaryGroup.transpose (localMatrixUnitary A hA hAq)) (tensorStateMatrix d e ψ)
  change rectHSNorm 1 (localMatrix B * densityRoot ψ - densityRoot ψ * localMatrix B) ≤
    Real.sqrt 2 * rectHSNorm 1 (localMatrix B * tensorStateMatrix d e ψ -
      tensorStateMatrix d e ψ * (localMatrix A)ᵀ) at h
  rw [tensorStateMatrix_consistency_norm] at h
  exact h

end ThomGame.Quantum
