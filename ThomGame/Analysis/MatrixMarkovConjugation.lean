module

public import ThomGame.Analysis.MatrixHilbertConjugation
public import ThomGame.Analysis.MatrixRelativeCommutant

/-! The actual matrix Markov map equals the lazy average of its trace Hilbert conjugations. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open Filter
open scoped BigOperators

variable {ι : Type*} (dims : ι → Nat) {h : Nat} [NeZero h]
  (U : (i : ι) → Fin h → UnitaryMatrix (dims i)) (hd : ∀ i, 0 < dims i)

theorem matrixUniformLazyMarkov_sequence_formula (A : BoundedMatrixSequence dims) :
    (matrixUniformLazyMarkov dims U hd).sequenceMap A = ((1 / 2 : ℝ) : ℂ) • A +
      (lazyMarkovWeight h : ℂ) • ∑ j, (boundedUnitarySequence dims (fun i => U i j) * A *
        star (boundedUnitarySequence dims (fun i => U i j)) +
        star (boundedUnitarySequence dims (fun i => U i j)) * A *
          boundedUnitarySequence dims (fun i => U i j)) := by
  apply Subtype.ext
  funext i
  change (matrixUniformLazyMarkov dims U hd).toLinearMap i (A.val i) = _
  simp [matrixUniformLazyMarkov_apply, matrixLazyMarkov_apply, matrixUnitaryConjugation_apply,
    Matrix.UnitaryGroup.inv_val, Finset.sum_apply]

theorem matrixQuotientLazyMarkov_formula (L : Filter ι) (x : MatrixTracialQuotient dims L) :
    matrixQuotientLazyMarkov dims U hd L x = ((1 / 2 : ℝ) : ℂ) • x +
      (lazyMarkovWeight h : ℂ) • ∑ j, (matrixTupleClass dims U L j * x * star (matrixTupleClass dims U L j) +
        star (matrixTupleClass dims U L j) * x * matrixTupleClass dims U L j) := by
  obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims L x
  rw [matrixQuotientLazyMarkov_mk, matrixUniformLazyMarkov_sequence_formula]
  change matrixQuotientStarAlgHom dims L _ = _
  simp only [map_add, map_smul, map_sum, map_mul, map_star]
  rfl

omit [NeZero h] in
def matrixTupleUnitary (L : Filter ι) (j : Fin h) : unitary (MatrixTracialQuotient dims L) :=
  ⟨matrixTupleClass dims U L j, matrixTupleClass_unitary dims U L j⟩

theorem matrixLazyMarkov_hilbertMap_eq_average (L : Ultrafilter ι) :
    (matrixUniformLazyMarkov dims U hd).hilbertMap hd L =
      lazyHilbertAverage (fun j => matrixHilbertConjugationHom dims hd L (matrixTupleUnitary dims U (L : Filter ι) j)) := by
  apply matrixHilbertOperator_ext dims hd L
  intro x
  rw [UniformMatrixMap.hilbertMap_embedding, lazyHilbertAverage_apply]
  change matrixHilbertEmbedding dims hd L (matrixQuotientLazyMarkov dims U hd (L : Filter ι) x) = _
  rw [matrixQuotientLazyMarkov_formula]
  simp only [map_add, map_smul, map_sum, matrixHilbertConjugationHom_embedding,
    matrixHilbertConjugationHom_symm_embedding, matrixTupleUnitary]

theorem matrixLazyMarkov_hilbert_conjugation_energy (L : Ultrafilter ι) (ξ : MatrixTraceHilbert dims hd L) :
    (inner ℂ ξ ((1 - (matrixUniformLazyMarkov dims U hd).hilbertMap hd L) ξ)).re =
      lazyMarkovWeight h * ∑ j, ‖matrixHilbertConjugationHom dims hd L
        (matrixTupleUnitary dims U (L : Filter ι) j) ξ - ξ‖ ^ 2 := by
  rw [matrixLazyMarkov_hilbertMap_eq_average, sub_apply, one_apply_eq_self]
  exact lazyHilbertAverage_energy _ ξ

end ThomGame.Analysis
