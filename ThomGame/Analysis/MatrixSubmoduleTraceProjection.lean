module

public import ThomGame.Analysis.MatrixTraceProjection

/-!
# Normalized trace projection onto any actual matrix submodule
-/

@[expose] public section
namespace ThomGame.Analysis

variable {d : Nat} [NeZero d]

def matrixSubmoduleTraceHilbert (S : Submodule ℂ (CMatrix d)) : Submodule ℂ (FiniteMatrixHilbert d) :=
  S.comap (finiteMatrixHilbertEquiv d).symm.toLinearMap

noncomputable def matrixSubmoduleTraceProjection (S : Submodule ℂ (CMatrix d)) :
    CMatrix d →ₗ[ℂ] CMatrix d :=
  (finiteMatrixHilbertEquiv d).symm.toLinearMap.comp
    ((matrixSubmoduleTraceHilbert S).starProjection.toLinearMap.comp (finiteMatrixHilbertEquiv d).toLinearMap)

theorem matrixSubmoduleTraceProjection_embedding (S : Submodule ℂ (CMatrix d)) (X : CMatrix d) :
    finiteMatrixHilbertEquiv d (matrixSubmoduleTraceProjection S X) =
      (matrixSubmoduleTraceHilbert S).starProjection (finiteMatrixHilbertEquiv d X) :=
  (finiteMatrixHilbertEquiv d).apply_symm_apply _

theorem matrixSubmoduleTraceProjection_mem (S : Submodule ℂ (CMatrix d)) (X : CMatrix d) :
    matrixSubmoduleTraceProjection S X ∈ S :=
  (matrixSubmoduleTraceHilbert S).starProjection_apply_mem (finiteMatrixHilbertEquiv d X)

theorem matrixSubmoduleTraceProjection_eq_self (S : Submodule ℂ (CMatrix d))
    (X : CMatrix d) (hX : X ∈ S) : matrixSubmoduleTraceProjection S X = X := by
  apply (finiteMatrixHilbertEquiv d).injective
  rw [matrixSubmoduleTraceProjection_embedding]
  exact (matrixSubmoduleTraceHilbert S).starProjection_eq_self_iff.mpr hX

theorem matrixSubmoduleTraceProjection_orthogonal (S : Submodule ℂ (CMatrix d))
    (X B : CMatrix d) (hB : B ∈ S) :
    normalizedTrace (star B * (X - matrixSubmoduleTraceProjection S X)) = 0 := by
  have h := (matrixSubmoduleTraceHilbert S).sub_starProjection_mem_orthogonal
    (finiteMatrixHilbertEquiv d X) (finiteMatrixHilbertEquiv d B) hB
  rw [← matrixSubmoduleTraceProjection_embedding, ← map_sub, finiteMatrixHilbert_inner] at h
  exact h

theorem matrixSubmoduleTraceProjection_unique (S : Submodule ℂ (CMatrix d))
    (X Z : CMatrix d) (hZ : Z ∈ S)
    (horth : ∀ B ∈ S, normalizedTrace (star B * (X - Z)) = 0) :
    matrixSubmoduleTraceProjection S X = Z := by
  apply (finiteMatrixHilbertEquiv d).injective
  rw [matrixSubmoduleTraceProjection_embedding]
  refine (matrixSubmoduleTraceHilbert S).eq_starProjection_of_mem_orthogonal
    (v := finiteMatrixHilbertEquiv d Z) hZ ?_
  intro B hB
  rw [← map_sub]
  have he := finiteMatrixHilbert_inner d ((finiteMatrixHilbertEquiv d).symm B) (X - Z)
  rw [(finiteMatrixHilbertEquiv d).apply_symm_apply] at he
  exact he.trans (horth _ hB)

theorem matrixSubmoduleTraceProjection_hsNorm_le (S : Submodule ℂ (CMatrix d)) (X : CMatrix d) :
    hsNorm (matrixSubmoduleTraceProjection S X) ≤ hsNorm X := by
  rw [← finiteMatrixHilbert_norm, ← finiteMatrixHilbert_norm, matrixSubmoduleTraceProjection_embedding]
  exact (matrixSubmoduleTraceHilbert S).norm_starProjection_apply_le _

end ThomGame.Analysis
