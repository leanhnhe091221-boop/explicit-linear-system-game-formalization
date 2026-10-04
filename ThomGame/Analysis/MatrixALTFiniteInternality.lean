module

public import ThomGame.Analysis.MatrixALTTheorem5_2
public import ThomGame.Analysis.MatrixFiniteInternalCommutants
public import ThomGame.Analysis.MatrixFiniteRelativeExpectation

/-!
# ALT internality and centers in the actual finite weakly closed algebra

The reconstructed coordinate algebras represent the relative commutant
in the entire finite operator algebra, with the same conditional
expectation and coordinate centers. The actual spectral-gap hypothesis
is retained explicitly.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter

theorem exists_matrixALT_finite_internal_relative_commutant_and_center
    (dims : Nat → Nat) {h : Nat} [NeZero h]
    (V : (n : Nat) → Fin h → UnitaryMatrix (dims n)) (hd : ∀ n, 0 < dims n)
    (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop) (κ : ℝ)
    (hgap : MatrixMarkovSpectralGap dims V hd L κ) :
    ∃ A : (n : Nat) → StarSubalgebra ℂ (CMatrix (dims n)),
      matrixFiniteRelativeExpectation dims V hd L hL = matrixFiniteExpectation dims A hd L hL ∧
      matrixFiniteRelativeCommutant dims V hd L = matrixInternalFiniteAlgebra dims A hd L ∧
      starSubalgebraCenter (matrixFiniteRelativeCommutant dims V hd L) =
        matrixInternalFiniteAlgebra dims (fun n => starSubalgebraCenter (A n)) hd L := by
  obtain ⟨A, hE, hC, _⟩ := exists_matrixALT_internal_relative_commutant_and_center dims V hd L hL κ hgap
  have hCf : matrixFiniteRelativeCommutant dims V hd L = matrixInternalFiniteAlgebra dims A hd L := by
    ext T
    obtain ⟨x, rfl⟩ := matrixFiniteEmbedding_surjective dims hd L hL T
    rw [matrixFiniteEmbedding_mem_relativeCommutant_iff, matrixFiniteEmbedding_mem_internal_iff, hC]
  refine ⟨A, ?_, hCf, ?_⟩
  · apply LinearMap.ext
    intro T
    obtain ⟨x, rfl⟩ := matrixFiniteEmbedding_surjective dims hd L hL T
    rw [matrixFiniteRelativeExpectation_embedding, matrixFiniteExpectation_embedding, hE]
  · rw [hCf, matrixInternalFiniteAlgebra_center dims A hd L hL]

end ThomGame.Analysis
