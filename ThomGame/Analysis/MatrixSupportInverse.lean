module

public import ThomGame.Analysis.MatrixSelfAdjointDilation

/-!
# Spectral supports and generalized inverses

These are actual functions of a finite Hermitian matrix. The reciprocal
is zero on the kernel; its continuity is needed only on the finite spectrum.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def matrixRealSupport (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  cfc (fun t : ℝ => if t = 0 then 0 else 1) A

noncomputable def matrixRealInv (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  cfc (fun t : ℝ => t⁻¹) A

theorem matrixRealSupport_isStarProjection (A : Matrix ι ι ℂ) :
    IsStarProjection (matrixRealSupport A) := by
  constructor
  · show matrixRealSupport A * matrixRealSupport A = matrixRealSupport A
    rw [matrixRealSupport, ← cfc_mul _ _ A
      (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
    apply cfc_congr
    intro t _
    dsimp only
    split_ifs <;> simp
  · exact IsSelfAdjoint.cfc

theorem matrixRealInv_isSelfAdjoint (A : Matrix ι ι ℂ) :
    IsSelfAdjoint (matrixRealInv A) := IsSelfAdjoint.cfc

theorem matrixRealSupport_mul {A : Matrix ι ι ℂ} (hA : Matrix.IsHermitian A) :
    matrixRealSupport A * A = A := by
  have hid : cfc (fun t : ℝ => t) A = A := cfc_id ℝ A
  conv_lhs => rhs; rw [← hid]
  rw [matrixRealSupport, ← cfc_mul _ _ A
    (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
  calc
    _ = cfc (fun t : ℝ => t) A := by
      apply cfc_congr
      intro t _
      dsimp only
      split_ifs with ht <;> simp_all
    _ = A := hid

theorem mul_matrixRealSupport {A : Matrix ι ι ℂ} (hA : Matrix.IsHermitian A) :
    A * matrixRealSupport A = A := by
  have he := congrArg star (matrixRealSupport_mul hA)
  simpa only [star_mul, hA.star_eq,
    (matrixRealSupport_isStarProjection A).isSelfAdjoint.star_eq] using he

theorem matrixRealInv_mul {A : Matrix ι ι ℂ} (hA : Matrix.IsHermitian A) :
    matrixRealInv A * A = matrixRealSupport A := by
  have hid : cfc (fun t : ℝ => t) A = A := cfc_id ℝ A
  conv_lhs => rhs; rw [← hid]
  rw [matrixRealInv, matrixRealSupport, ← cfc_mul _ _ A
    (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
  apply cfc_congr
  intro t _
  dsimp only
  split_ifs with ht <;> simp_all

theorem mul_matrixRealInv {A : Matrix ι ι ℂ} (hA : Matrix.IsHermitian A) :
    A * matrixRealInv A = matrixRealSupport A := by
  have he := congrArg star (matrixRealInv_mul hA)
  simpa only [star_mul, hA.star_eq, (matrixRealInv_isSelfAdjoint A).star_eq,
    (matrixRealSupport_isStarProjection A).isSelfAdjoint.star_eq] using he

theorem matrixRealSupport_mul_inv (A : Matrix ι ι ℂ) :
    matrixRealSupport A * matrixRealInv A = matrixRealInv A := by
  rw [matrixRealSupport, matrixRealInv, ← cfc_mul _ _ A
    (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
  apply cfc_congr
  intro t _
  dsimp only
  split_ifs with ht <;> simp_all

theorem matrixRealInv_mul_support (A : Matrix ι ι ℂ) :
    matrixRealInv A * matrixRealSupport A = matrixRealInv A := by
  have he := congrArg star (matrixRealSupport_mul_inv A)
  simpa only [star_mul, (matrixRealInv_isSelfAdjoint A).star_eq,
    (matrixRealSupport_isStarProjection A).isSelfAdjoint.star_eq] using he

end ThomGame.Analysis
