module

public import ThomGame.Analysis.MatrixMarkovBimodule
public import ThomGame.Analysis.PositiveInvariantSubspace

/-!
# The invariant trace-zero Hilbert subspace of a reducing corner

All norms are inherited from the original ambient normalized trace.
No change of normalization is made on the smaller corner.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {d h : Nat}

def matrixCornerTraceZeroSubmodule (P : CMatrix d) : Submodule ℂ (CMatrix d) where
  carrier := {X | P * X = X ∧ X * P = X ∧ normalizedTrace X = 0}
  zero_mem' := ⟨mul_zero P, zero_mul P, normalizedTrace_zero⟩
  add_mem' := by
    intro X Y hX hY
    exact ⟨by rw [mul_add, hX.1, hY.1], by rw [add_mul, hX.2.1, hY.2.1],
      by rw [normalizedTrace_add, hX.2.2, hY.2.2, zero_add]⟩
  smul_mem' := by
    intro c X hX
    exact ⟨by rw [mul_smul_comm, hX.1], by rw [smul_mul_assoc, hX.2.1],
      by rw [normalizedTrace_smul, hX.2.2, mul_zero]⟩

def matrixCornerTraceZeroHilbert (P : CMatrix d) : Submodule ℂ (FiniteMatrixHilbert d) :=
  (matrixCornerTraceZeroSubmodule P).comap (finiteMatrixHilbertEquiv d).symm.toLinearMap

@[simp] theorem mem_matrixCornerTraceZeroHilbert (P X : CMatrix d) :
    finiteMatrixHilbertEquiv d X ∈ matrixCornerTraceZeroHilbert P ↔
      P * X = X ∧ X * P = X ∧ normalizedTrace X = 0 := Iff.rfl

theorem matrixLazyMarkov_corner_support (U : Fin h → UnitaryMatrix d) (P : CMatrix d)
    (hred : ∀ j, Commute P (U j).val) (X : CMatrix d)
    (hleft : P * X = X) (hright : X * P = X) :
    P * matrixLazyMarkov U X = matrixLazyMarkov U X ∧
      matrixLazyMarkov U X * P = matrixLazyMarkov U X := by
  constructor
  · have he := matrixLazyMarkov_bimodule U P X 1 (fun j => (hred j).symm) (fun j => Commute.one_right _)
    simpa only [mul_one, hleft] using he.symm
  · have he := matrixLazyMarkov_bimodule U 1 X P (fun j => Commute.one_right _) (fun j => (hred j).symm)
    simpa only [one_mul, hright] using he.symm

variable [NeZero d] [NeZero h]

theorem matrixCornerTraceZeroHilbert_invariant (U : Fin h → UnitaryMatrix d) (P : CMatrix d)
    (hred : ∀ j, Commute P (U j).val) :
    ∀ ξ ∈ matrixCornerTraceZeroHilbert P,
      lazyHilbertAverage (fun j => matrixConjugationHilbertEquiv (U j)) ξ ∈ matrixCornerTraceZeroHilbert P := by
  intro ξ hξ
  obtain ⟨X, rfl⟩ := (finiteMatrixHilbertEquiv d).surjective ξ
  rw [mem_matrixCornerTraceZeroHilbert] at hξ
  rw [← matrixLazyMarkov_hilbert, mem_matrixCornerTraceZeroHilbert]
  have hs := matrixLazyMarkov_corner_support U P hred X hξ.1 hξ.2.1
  exact ⟨hs.1, hs.2, (matrixLazyMarkov_trace U X).trans hξ.2.2⟩

theorem matrixLazyMarkov_traceZero_corner_pow_le (U : Fin h → UnitaryMatrix d) (P : CMatrix d)
    (hred : ∀ j, Commute P (U j).val) (c : ℝ) (hc : c ≤ 1)
    (hgap : ∀ X : CMatrix d, P * X = X → X * P = X → normalizedTrace X = 0 →
      c * hsNorm X ^ 2 ≤ matrixCoordinateEnergy U X)
    (n : Nat) (X : CMatrix d) (hleft : P * X = X) (hright : X * P = X) (htrace : normalizedTrace X = 0) :
    hsNorm ((matrixLazyMarkov U ^ n) X) ≤ (1 - c) ^ n * hsNorm X := by
  let T := lazyHilbertAverage (fun j => matrixConjugationHilbertEquiv (U j))
  let S := matrixCornerTraceZeroHilbert P
  let : CompleteSpace S := FiniteDimensional.complete ℂ S
  have hform : ∀ ξ ∈ S, (inner ℂ ξ (T ξ)).re ≤ (1 - c) * ‖ξ‖ ^ 2 := by
    intro ξ hξ
    obtain ⟨Y, rfl⟩ := (finiteMatrixHilbertEquiv d).surjective ξ
    change P * Y = Y ∧ Y * P = Y ∧ normalizedTrace Y = 0 at hξ
    have hg := hgap Y hξ.1 hξ.2.1 hξ.2.2
    rw [matrixCoordinateEnergy, ← matrixLazyMarkov_energy, mul_sub, normalizedTrace_sub,
      Complex.sub_re, normalizedTrace_gram, Complex.ofReal_re] at hg
    change (inner ℂ (finiteMatrixHilbertEquiv d Y)
      (lazyHilbertAverage (fun j => matrixConjugationHilbertEquiv (U j)) (finiteMatrixHilbertEquiv d Y))).re ≤ _
    rw [← matrixLazyMarkov_hilbert, finiteMatrixHilbert_inner, finiteMatrixHilbert_norm]
    linarith only [hg]
  have he := positive_operator_invariant_pow_norm_le T S
    (matrixCornerTraceZeroHilbert_invariant U P hred) (lazyHilbertAverage_nonneg _)
    (1 - c) (sub_nonneg.mpr hc) hform n (finiteMatrixHilbertEquiv d X) ⟨hleft, hright, htrace⟩
  simpa only [T, ← matrixLazyMarkov_pow_hilbert, finiteMatrixHilbert_norm] using he

end ThomGame.Analysis
