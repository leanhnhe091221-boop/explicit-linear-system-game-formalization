module

public import ThomGame.Analysis.MatrixUCPTraceBounds
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Data.Matrix.Basis

/-!
# Actual finite Kraus representations of completely positive matrix maps

The positive Choi matrix is factored inside its actual block C-star algebra.
Reshaping the rows of its square root gives d squared concrete Kraus matrices.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra BigOperators

variable {d : Nat} [NeZero d]

theorem matrixChoi_input_nonneg :
    0 ≤ (CStarMatrix.ofMatrix (fun i j : Fin d => Matrix.single i j (1 : ℂ)) :
      CStarMatrix (Fin d) (Fin d) (CMatrix d)) := by
  let V : CStarMatrix (Fin d) (Fin d) (CMatrix d) :=
    CStarMatrix.ofMatrix (fun k i => if k = 0 then Matrix.single 0 i 1 else 0)
  have he : star V * V = CStarMatrix.ofMatrix (fun i j : Fin d => Matrix.single i j (1 : ℂ)) := by
    apply CStarMatrix.ext
    intro i j
    change (∑ k : Fin d, star (if k = 0 then Matrix.single 0 i (1 : ℂ) else 0) *
      (if k = 0 then Matrix.single 0 j (1 : ℂ) else 0)) = Matrix.single i j 1
    simp [
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single, Matrix.single_mul_single_same]
  rw [← he]
  exact star_mul_self_nonneg V

def matrixChoiKraus (S : CStarMatrix (Fin d) (Fin d) (CMatrix d)) :
    Fin d × Fin d → CMatrix d := fun k i j => S k.1 i k.2 j

omit [NeZero d] in
theorem matrixKraus_of_choi_factor (F : CMatrix d →CP CMatrix d)
    (S : CStarMatrix (Fin d) (Fin d) (CMatrix d))
    (hS : star S * S = (CStarMatrix.ofMatrix (fun i j : Fin d => Matrix.single i j (1 : ℂ))).map F)
    (X : CMatrix d) :
    F X = ∑ k, star (matrixChoiKraus S k) * X * matrixChoiKraus S k := by
  let a := matrixChoiKraus S
  change F X = ∑ k, star (a k) * X * a k
  have he (i j : Fin d) : F (Matrix.single i j 1) =
      ∑ k, star (a k) * Matrix.single i j 1 * a k := by
    ext p q
    have hh := congrArg (fun M : CStarMatrix (Fin d) (Fin d) (CMatrix d) => M i j p q) hS
    change (∑ k, star (S k i) * S k j) p q = F (Matrix.single i j 1) p q at hh
    rw [← hh]
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, Fintype.sum_prod_type]
    change (∑ k, ∑ r, star (S k i r p) * S k j r q) =
      ∑ k, ∑ r, ∑ t, (∑ s, star (S k s r p) * (Matrix.single i j (1 : ℂ)) s t) * S k t r q
    simp [Matrix.single, ite_and]
  refine Matrix.induction_on' X (by simp) (fun P Q hP hQ => ?_) (fun i j c => ?_)
  · simp only [map_add, hP, hQ, mul_add, add_mul, Finset.sum_add_distrib]
  · have hc : Matrix.single i j c = c • Matrix.single i j (1 : ℂ) := by
      simp only [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [hc, map_smul, he, Finset.smul_sum]
    simp only [Matrix.mul_smul, Matrix.smul_mul]

theorem exists_matrix_kraus (F : CMatrix d →CP CMatrix d) :
    ∃ a : Fin d × Fin d → CMatrix d, ∀ X, F X = ∑ k, star (a k) * X * a k := by
  let : NonUnitalIsometricContinuousFunctionalCalculus ℝ
      (CStarMatrix (Fin d) (Fin d) (CMatrix d)) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalIsometricContinuousFunctionalCalculus
  let : NonnegSpectrumClass ℝ (CStarMatrix (Fin d) (Fin d) (CMatrix d)) :=
    CStarAlgebra.instNonnegSpectrumClass
  let G : CStarMatrix (Fin d) (Fin d) (CMatrix d) :=
    CStarMatrix.ofMatrix (fun i j => Matrix.single i j 1)
  let C := G.map F
  have hC : 0 ≤ C := F.map_cstarMatrix_nonneg G matrixChoi_input_nonneg
  let S := CFC.sqrt C
  have hS : star S * S = C := by
    rw [(CFC.sqrt_nonneg C).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self C hC]
  exact ⟨matrixChoiKraus S, matrixKraus_of_choi_factor F S hS⟩

end ThomGame.Analysis
