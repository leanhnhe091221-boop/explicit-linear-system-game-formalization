module

public import ThomGame.Analysis.MatrixMarkovConjugation
public import ThomGame.Analysis.HilbertRepresentationAverage
public import ThomGame.Analysis.MatrixMarkovSpectralGap

/-! Exact transfer of a genuine group representation gap to the actual trace Hilbert Markov gap. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open Filter
open scoped BigOperators

section GeneralIndex

variable {G ι : Type*} [Group G] (dims : ι → Nat) (hd : ∀ i, 0 < dims i) (L : Ultrafilter ι)

def matrixConjugationRepresentation (φ : G →* unitary (MatrixTracialQuotient dims (L : Filter ι))) :
    G →* (MatrixTraceHilbert dims hd L ≃ₗᵢ[ℂ] MatrixTraceHilbert dims hd L) :=
  (matrixHilbertConjugationHom dims hd L).comp φ

theorem matrixConjugationRepresentation_embedding
    (φ : G →* unitary (MatrixTracialQuotient dims (L : Filter ι))) (g : G)
    (x : MatrixTracialQuotient dims (L : Filter ι)) :
    matrixConjugationRepresentation dims hd L φ g (matrixHilbertEmbedding dims hd L x) =
      matrixHilbertEmbedding dims hd L ((φ g).val * x * star (φ g).val) :=
  matrixHilbertConjugationHom_embedding dims hd L (φ g) x

variable {h : Nat} [NeZero h] (V : (i : ι) → Fin h → UnitaryMatrix (dims i))
  (φ : G →* unitary (MatrixTracialQuotient dims (L : Filter ι))) (s : Fin h → G)
  (hV : ∀ j, matrixTupleClass dims V (L : Filter ι) j = (φ (s j)).val)

include hV in
theorem matrixRepresentation_hilbertMap_eq_average :
    (matrixUniformLazyMarkov dims V hd).hilbertMap hd L =
      lazyHilbertAverage (fun j => matrixConjugationRepresentation dims hd L φ (s j)) := by
  rw [matrixLazyMarkov_hilbertMap_eq_average]
  congr 1
  funext j
  change matrixHilbertConjugationHom dims hd L (matrixTupleUnitary dims V (L : Filter ι) j) =
    matrixHilbertConjugationHom dims hd L (φ (s j))
  exact congrArg (matrixHilbertConjugationHom dims hd L) (Subtype.ext (hV j))

include hV in
theorem matrixRepresentation_hilbert_energy (ξ : MatrixTraceHilbert dims hd L) :
    (inner ℂ ξ ((1 - (matrixUniformLazyMarkov dims V hd).hilbertMap hd L) ξ)).re =
      lazyMarkovWeight h * ∑ j, ‖matrixConjugationRepresentation dims hd L φ (s j) ξ - ξ‖ ^ 2 := by
  rw [matrixRepresentation_hilbertMap_eq_average dims hd L V φ s hV, sub_apply, one_apply_eq_self]
  exact lazyHilbertAverage_energy _ ξ

end GeneralIndex

section NatIndex

variable {G : Type*} [Group G] {h : Nat} [NeZero h]

variable (dims : Nat → Nat) (hd : ∀ n, 0 < dims n) (L : Ultrafilter Nat)
  (hL : (L : Filter Nat) ≤ atTop) (V : (n : Nat) → Fin h → UnitaryMatrix (dims n))
  (φ : G →* unitary (MatrixTracialQuotient dims (L : Filter Nat))) (K : Subgroup G)
  (s : Fin h → G) (hgen : Subgroup.closure (Set.range s) = K)
  (hV : ∀ j, matrixTupleClass dims V (L : Filter Nat) j = (φ (s j)).val)

include hL hgen hV in
theorem matrixRepresentation_relativeTrace_eq_invariants :
    matrixRelativeCommutantTraceSubspace dims V hd L =
      hilbertUnitaryInvariants ((matrixConjugationRepresentation dims hd L φ).comp K.subtype) := by
  rw [matrixRelativeCommutantTraceSubspace_eq_fixed dims V hd L hL,
    matrixRepresentation_hilbertMap_eq_average dims hd L V φ s hV]
  exact (hilbertUnitaryInvariants_eq_average_fixed (matrixConjugationRepresentation dims hd L φ) K s hgen).symm

include hL hgen hV in
theorem matrixMarkovSpectralGap_of_representation_energy (c : ℝ) (hc : 0 < c)
    (hgap : ∀ ξ ∈ (hilbertUnitaryInvariants ((matrixConjugationRepresentation dims hd L φ).comp K.subtype))ᗮ,
      c * ‖ξ‖ ^ 2 ≤ ∑ j, ‖matrixConjugationRepresentation dims hd L φ (s j) ξ - ξ‖ ^ 2) :
    MatrixMarkovSpectralGap dims V hd L (representationMarkovGapConstant h c) := by
  refine ⟨representationMarkovGapConstant_pos h c hc, representationMarkovGapConstant_lt_one h c, ?_⟩
  intro ξ hξ
  rw [matrixRepresentation_relativeTrace_eq_invariants dims hd L hL V φ K s hgen hV] at hξ
  rw [matrixRepresentation_hilbert_energy dims hd L V φ s hV]
  calc
    representationMarkovGapConstant h c * ‖ξ‖ ^ 2 ≤ (lazyMarkovWeight h * c) * ‖ξ‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)
    _ ≤ lazyMarkovWeight h * ∑ j, ‖matrixConjugationRepresentation dims hd L φ (s j) ξ - ξ‖ ^ 2 := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hgap ξ hξ) (lazyMarkovWeight_nonneg h)

end NatIndex
end ThomGame.Analysis
