module

public import ThomGame.Analysis.MatrixCornerMarkovDecay

/-!
# Uniform corner error in the actual Hilbert operator norm

The maximum is over the actual finite family of nonzero corners. Its
bound is independent of the number and sizes of those corners.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology BigOperators Matrix.Norms.L2Operator

section Matrix

variable {d h : Nat}

def matrixCornerSubmodule (P : CMatrix d) : Submodule ℂ (CMatrix d) where
  carrier := {X | P * X = X ∧ X * P = X}
  zero_mem' := ⟨mul_zero P, zero_mul P⟩
  add_mem' := by
    intro X Y hX hY
    exact ⟨by rw [mul_add, hX.1, hY.1], by rw [add_mul, hX.2, hY.2]⟩
  smul_mem' := by
    intro c X hX
    exact ⟨by rw [mul_smul_comm, hX.1], by rw [smul_mul_assoc, hX.2]⟩

def matrixCornerHilbert (P : CMatrix d) : Submodule ℂ (FiniteMatrixHilbert d) :=
  (matrixCornerSubmodule P).comap (finiteMatrixHilbertEquiv d).symm.toLinearMap

noncomputable def matrixCornerTraceScalar (P : CMatrix d) : CMatrix d →ₗ[ℂ] CMatrix d where
  toFun X := (normalizedTrace X / normalizedTrace P) • P
  map_add' X Y := by rw [normalizedTrace_add, add_div, add_smul]
  map_smul' c X := by
    change (normalizedTrace (c • X) / normalizedTrace P) • P = c • ((normalizedTrace X / normalizedTrace P) • P)
    rw [normalizedTrace_smul, mul_div_assoc, smul_smul]

variable [NeZero d]

noncomputable def matrixCornerMarkovError (U : Fin h → UnitaryMatrix d) (P : CMatrix d) (n : Nat) :
    matrixCornerHilbert P →L[ℂ] FiniteMatrixHilbert d :=
  (((finiteMatrixHilbertEquiv d).toLinearMap.comp
    ((matrixLazyMarkov U ^ n - matrixCornerTraceScalar P).comp
      (finiteMatrixHilbertEquiv d).symm.toLinearMap)).toContinuousLinearMap).domRestrict (matrixCornerHilbert P)

@[simp] theorem matrixCornerMarkovError_apply (U : Fin h → UnitaryMatrix d) (P : CMatrix d) (n : Nat)
    (ξ : matrixCornerHilbert P) :
    matrixCornerMarkovError U P n ξ = finiteMatrixHilbertEquiv d
      ((matrixLazyMarkov U ^ n) ((finiteMatrixHilbertEquiv d).symm ξ.val) -
        (normalizedTrace ((finiteMatrixHilbertEquiv d).symm ξ.val) / normalizedTrace P) • P) := rfl

noncomputable def matrixScalarCornerError {U : Fin h → UnitaryMatrix d} {c : ℝ}
    (Q : MatrixScalarGapPartition U c) (n : Nat) : ℝ :=
  ↑(Finset.univ.sup (fun i => ‖matrixCornerMarkovError U (Q.E i) n‖₊))

theorem matrixScalarCornerError_nonneg {U : Fin h → UnitaryMatrix d} {c : ℝ}
    (Q : MatrixScalarGapPartition U c) (n : Nat) : 0 ≤ matrixScalarCornerError Q n := NNReal.coe_nonneg _

variable [NeZero h]

theorem MatrixScalarGapPartition.corner_markov_error_norm_le {U : Fin h → UnitaryMatrix d} {c : ℝ}
    (Q : MatrixScalarGapPartition U c) (hc : c ≤ 1) (i : Fin Q.n) (hi : Q.E i ≠ 0) (n : Nat) :
    ‖matrixCornerMarkovError U (Q.E i) n‖ ≤ (1 - c) ^ n := by
  apply ContinuousLinearMap.opNorm_le_bound _ (pow_nonneg (sub_nonneg.mpr hc) n)
  intro ξ
  let X := (finiteMatrixHilbertEquiv d).symm ξ.val
  have hx : Q.E i * X = X ∧ X * Q.E i = X := ξ.property
  have hnorm : hsNorm X = ‖ξ‖ := by
    rw [← finiteMatrixHilbert_norm]
    change ‖finiteMatrixHilbertEquiv d ((finiteMatrixHilbertEquiv d).symm ξ.val)‖ = ‖ξ‖
    rw [(finiteMatrixHilbertEquiv d).apply_symm_apply]
    rfl
  rw [matrixCornerMarkovError_apply, finiteMatrixHilbert_norm, ← hnorm]
  exact Q.corner_markov_pow_scalar_le hc i hi n X hx.1 hx.2

theorem MatrixScalarGapPartition.scalarCornerError_le {U : Fin h → UnitaryMatrix d} {c : ℝ}
    (Q : MatrixScalarGapPartition U c) (hc : c ≤ 1) (hne : ∀ i, Q.E i ≠ 0) (n : Nat) :
    matrixScalarCornerError Q n ≤ (1 - c) ^ n := by
  let K : NNReal := ⟨(1 - c) ^ n, pow_nonneg (sub_nonneg.mpr hc) n⟩
  change (↑(Finset.univ.sup (fun i => ‖matrixCornerMarkovError U (Q.E i) n‖₊)) : ℝ) ≤ ↑K
  apply (NNReal.coe_le_coe).mpr
  apply Finset.sup_le
  intro i _
  exact (NNReal.coe_le_coe).mp (Q.corner_markov_error_norm_le hc i (hne i) n)

end Matrix

variable {ι : Type*} (dims : ι → Nat) {h : Nat}
  (U : (k : ι) → Fin h → UnitaryMatrix (dims k)) (hd : ∀ k, 0 < dims k)
  {c : ℝ} (Q : (k : ι) → MatrixScalarGapPartition (U k) c) (N : ι → Nat)

noncomputable def matrixScalarCornerErrorSequence (k : ι) : ℝ := by
  let : NeZero (dims k) := ⟨Nat.ne_of_gt (hd k)⟩
  exact matrixScalarCornerError (Q k) (N k)

theorem matrixScalarCornerErrorSequence_nonneg (k : ι) :
    0 ≤ matrixScalarCornerErrorSequence dims U hd Q N k := by
  let : NeZero (dims k) := ⟨Nat.ne_of_gt (hd k)⟩
  exact matrixScalarCornerError_nonneg (Q k) (N k)

theorem matrixScalarCornerErrorSequence_tendsto_zero [NeZero h] (hc₀ : 0 < c) (hc₁ : c ≤ 1)
    (hne : ∀ k i, (Q k).E i ≠ 0) (L : Filter ι) (hN : Tendsto N L atTop) :
    Tendsto (matrixScalarCornerErrorSequence dims U hd Q N) L (𝓝 0) := by
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.mpr hc₁)
    (by linarith only [hc₀] : 1 - c < 1)).comp hN
  apply squeeze_zero (matrixScalarCornerErrorSequence_nonneg dims U hd Q N) _ ht
  intro k
  let : NeZero (dims k) := ⟨Nat.ne_of_gt (hd k)⟩
  exact (Q k).scalarCornerError_le hc₁ (hne k) (N k)

end ThomGame.Analysis
