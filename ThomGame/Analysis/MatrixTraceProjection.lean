module

public import ThomGame.Analysis.FiniteMatrixHilbert
public import Mathlib.Algebra.Star.Subalgebra

/-!
# Trace orthogonal projection onto a matrix star subalgebra

The map is constructed by Hilbert orthogonal projection and then
transported to the original matrix algebra. Its range, fixed points,
trace pairing, normalized Hilbert--Schmidt contraction, star compatibility,
and bimodularity are proved.
-/

@[expose] public section
namespace ThomGame.Analysis

variable {d : Nat} [NeZero d] (S : StarSubalgebra ℂ (CMatrix d))

def matrixTraceSubmodule : Submodule ℂ (FiniteMatrixHilbert d) :=
  S.toSubalgebra.toSubmodule.comap (finiteMatrixHilbertEquiv d).symm.toLinearMap

noncomputable def matrixTraceProjection : CMatrix d →ₗ[ℂ] CMatrix d :=
  (finiteMatrixHilbertEquiv d).symm.toLinearMap.comp
    ((matrixTraceSubmodule S).starProjection.toLinearMap.comp (finiteMatrixHilbertEquiv d).toLinearMap)

theorem matrixTraceProjection_embedding (X : CMatrix d) :
    finiteMatrixHilbertEquiv d (matrixTraceProjection S X) =
      (matrixTraceSubmodule S).starProjection (finiteMatrixHilbertEquiv d X) :=
  (finiteMatrixHilbertEquiv d).apply_symm_apply _

theorem matrixTraceProjection_mem (X : CMatrix d) : matrixTraceProjection S X ∈ S :=
  (matrixTraceSubmodule S).starProjection_apply_mem (finiteMatrixHilbertEquiv d X)

theorem matrixTraceProjection_eq_self (X : CMatrix d) (hX : X ∈ S) : matrixTraceProjection S X = X := by
  apply (finiteMatrixHilbertEquiv d).injective
  rw [matrixTraceProjection_embedding]
  exact (matrixTraceSubmodule S).starProjection_eq_self_iff.mpr hX

@[simp] theorem matrixTraceProjection_one : matrixTraceProjection S 1 = 1 :=
  matrixTraceProjection_eq_self S 1 S.one_mem

@[simp] theorem matrixTraceProjection_idem (X : CMatrix d) :
    matrixTraceProjection S (matrixTraceProjection S X) = matrixTraceProjection S X :=
  matrixTraceProjection_eq_self S _ (matrixTraceProjection_mem S X)

theorem matrixTraceProjection_hsNorm_le (X : CMatrix d) : hsNorm (matrixTraceProjection S X) ≤ hsNorm X := by
  rw [← finiteMatrixHilbert_norm, ← finiteMatrixHilbert_norm, matrixTraceProjection_embedding]
  exact (matrixTraceSubmodule S).norm_starProjection_apply_le _

theorem matrixTraceProjection_pairing (X B : CMatrix d) (hB : B ∈ S) :
    normalizedTrace (star B * matrixTraceProjection S X) = normalizedTrace (star B * X) := by
  have h : inner ℂ (finiteMatrixHilbertEquiv d B)
      (finiteMatrixHilbertEquiv d X - (matrixTraceSubmodule S).starProjection (finiteMatrixHilbertEquiv d X)) = 0 :=
    (matrixTraceSubmodule S).sub_starProjection_mem_orthogonal (finiteMatrixHilbertEquiv d X)
      (finiteMatrixHilbertEquiv d B) hB
  rw [inner_sub_right, ← matrixTraceProjection_embedding, finiteMatrixHilbert_inner, finiteMatrixHilbert_inner] at h
  exact (sub_eq_zero.mp h).symm

theorem matrixTraceProjection_orthogonal (X B : CMatrix d) (hB : B ∈ S) :
    normalizedTrace (star B * (X - matrixTraceProjection S X)) = 0 := by
  rw [mul_sub, normalizedTrace_sub, matrixTraceProjection_pairing S X B hB, sub_self]

theorem matrixTraceProjection_trace (X : CMatrix d) :
    normalizedTrace (matrixTraceProjection S X) = normalizedTrace X := by
  simpa only [star_one, one_mul] using matrixTraceProjection_pairing S X 1 S.one_mem

theorem matrixTraceProjection_unique (X Z : CMatrix d) (hZ : Z ∈ S)
    (horth : ∀ B ∈ S, normalizedTrace (star B * (X - Z)) = 0) : matrixTraceProjection S X = Z := by
  apply (finiteMatrixHilbertEquiv d).injective
  rw [matrixTraceProjection_embedding]
  refine (matrixTraceSubmodule S).eq_starProjection_of_mem_orthogonal
    (v := finiteMatrixHilbertEquiv d Z) hZ ?_
  intro B hB
  rw [← map_sub]
  have he := finiteMatrixHilbert_inner d ((finiteMatrixHilbertEquiv d).symm B) (X - Z)
  rw [(finiteMatrixHilbertEquiv d).apply_symm_apply] at he
  exact he.trans (horth _ hB)

theorem matrixTraceProjection_mul_left (A X : CMatrix d) (hA : A ∈ S) :
    matrixTraceProjection S (A * X) = A * matrixTraceProjection S X := by
  apply matrixTraceProjection_unique S _ _ (S.mul_mem hA (matrixTraceProjection_mem S X))
  intro B hB
  rw [← mul_sub]
  simpa only [star_mul, star_star, mul_assoc] using
    matrixTraceProjection_orthogonal S X (star A * B) (S.mul_mem (S.star_mem' hA) hB)

theorem matrixTraceProjection_mul_right (X A : CMatrix d) (hA : A ∈ S) :
    matrixTraceProjection S (X * A) = matrixTraceProjection S X * A := by
  apply matrixTraceProjection_unique S _ _ (S.mul_mem (matrixTraceProjection_mem S X) hA)
  intro B hB
  rw [← sub_mul, ← mul_assoc, normalizedTrace_mul_comm, ← mul_assoc]
  simpa only [star_mul, star_star, mul_assoc] using
    matrixTraceProjection_orthogonal S X (B * star A) (S.mul_mem hB (S.star_mem' hA))

theorem matrixTraceProjection_bimodule (A X B : CMatrix d) (hA : A ∈ S) (hB : B ∈ S) :
    matrixTraceProjection S (A * X * B) = A * matrixTraceProjection S X * B := by
  rw [matrixTraceProjection_mul_right S _ B hB, matrixTraceProjection_mul_left S A X hA]

@[simp] theorem matrixTraceProjection_star (X : CMatrix d) :
    matrixTraceProjection S (star X) = star (matrixTraceProjection S X) := by
  apply matrixTraceProjection_unique S _ _ (star_mem (matrixTraceProjection_mem S X))
  intro B hB
  rw [← star_sub, ← star_mul, normalizedTrace_star, normalizedTrace_mul_comm]
  have h := matrixTraceProjection_orthogonal S X (star B) (star_mem hB)
  rw [star_star] at h
  rw [h, star_zero]

end ThomGame.Analysis
