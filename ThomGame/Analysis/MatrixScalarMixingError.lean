module

public import ThomGame.Analysis.MatrixUCPTraceBounds
public import ThomGame.Analysis.MatrixUniformCornerDecay

/-!
# The actual scalar-corner error for arbitrary matrix maps

This is the finite maximum of the real two-to-two operator norms used
in ALT (5.3). It supplies the scalar bounds on every corner and agrees
exactly with the already constructed Markov-power error in Corollary 5.1.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d]

noncomputable def matrixCornerMapError (F : CMatrix d →ₗ[ℂ] CMatrix d) (P : CMatrix d) :
    matrixCornerHilbert P →L[ℂ] FiniteMatrixHilbert d :=
  (matrixMapHilbert (F - matrixCornerTraceScalar P)).domRestrict (matrixCornerHilbert P)

@[simp] theorem matrixCornerMapError_apply (F : CMatrix d →ₗ[ℂ] CMatrix d) (P : CMatrix d)
    (ξ : matrixCornerHilbert P) :
    matrixCornerMapError F P ξ = finiteMatrixHilbertEquiv d
      (F ((finiteMatrixHilbertEquiv d).symm ξ.val) -
        (normalizedTrace ((finiteMatrixHilbertEquiv d).symm ξ.val) / normalizedTrace P) • P) := rfl

theorem matrixCornerMapError_markov {h : Nat} (U : Fin h → UnitaryMatrix d) (P : CMatrix d) (n : Nat) :
    matrixCornerMapError (matrixLazyMarkov U ^ n) P = matrixCornerMarkovError U P n := rfl

variable {μ : Type*} [Fintype μ]

noncomputable def matrixScalarMixingError (E : μ → CMatrix d) (F : CMatrix d →ₗ[ℂ] CMatrix d) : ℝ :=
  ↑(Finset.univ.sup (fun i => ‖matrixCornerMapError F (E i)‖₊))

theorem matrixScalarMixingError_nonneg (E : μ → CMatrix d) (F : CMatrix d →ₗ[ℂ] CMatrix d) :
    0 ≤ matrixScalarMixingError E F := NNReal.coe_nonneg _

theorem matrixCornerMapError_norm_le (E : μ → CMatrix d) (F : CMatrix d →ₗ[ℂ] CMatrix d) (i : μ) :
    ‖matrixCornerMapError F (E i)‖ ≤ matrixScalarMixingError E F := by
  exact_mod_cast (Finset.le_sup (f := fun j => ‖matrixCornerMapError F (E j)‖₊) (Finset.mem_univ i))

theorem matrixScalarMixingError_hsNorm_le (E : μ → CMatrix d) (F : CMatrix d →ₗ[ℂ] CMatrix d)
    (i : μ) (X : CMatrix d) (hleft : E i * X = X) (hright : X * E i = X) :
    hsNorm (F X - (normalizedTrace X / normalizedTrace (E i)) • E i) ≤
      matrixScalarMixingError E F * hsNorm X := by
  let ξ : matrixCornerHilbert (E i) := ⟨finiteMatrixHilbertEquiv d X, ⟨hleft, hright⟩⟩
  have hn := (matrixCornerMapError F (E i)).le_opNorm ξ
  have he : ‖ξ‖ = hsNorm X := finiteMatrixHilbert_norm d X
  rw [matrixCornerMapError_apply, finiteMatrixHilbert_norm, he] at hn
  exact hn.trans (mul_le_mul_of_nonneg_right (matrixCornerMapError_norm_le E F i) (hsNorm_nonneg X))

theorem matrixScalarMixingError_le (E : μ → CMatrix d) (F : CMatrix d →ₗ[ℂ] CMatrix d)
    (sigma : ℝ) (hsigma : 0 ≤ sigma)
    (hF : ∀ i X, E i * X = X → X * E i = X →
      hsNorm (F X - (normalizedTrace X / normalizedTrace (E i)) • E i) ≤ sigma * hsNorm X) :
    matrixScalarMixingError E F ≤ sigma := by
  let K : NNReal := ⟨sigma, hsigma⟩
  change (↑(Finset.univ.sup (fun i => ‖matrixCornerMapError F (E i)‖₊)) : ℝ) ≤ ↑K
  apply NNReal.coe_le_coe.mpr
  apply Finset.sup_le
  intro i _
  apply NNReal.coe_le_coe.mp
  apply ContinuousLinearMap.opNorm_le_bound _ hsigma
  intro ξ
  let X := (finiteMatrixHilbertEquiv d).symm ξ.val
  have hnorm : hsNorm X = ‖ξ‖ := by
    rw [← finiteMatrixHilbert_norm]
    change ‖finiteMatrixHilbertEquiv d ((finiteMatrixHilbertEquiv d).symm ξ.val)‖ = ‖ξ‖
    rw [(finiteMatrixHilbertEquiv d).apply_symm_apply]
    rfl
  rw [matrixCornerMapError_apply, finiteMatrixHilbert_norm, ← hnorm]
  exact hF i X ξ.property.1 ξ.property.2

omit [Fintype μ] in
theorem matrixScalarMixingError_markov {h : Nat} {U : Fin h → UnitaryMatrix d} {c : ℝ}
    (Q : MatrixScalarGapPartition U c) (n : Nat) :
    matrixScalarMixingError Q.E (matrixLazyMarkov U ^ n) = matrixScalarCornerError Q n := rfl

end ThomGame.Analysis
