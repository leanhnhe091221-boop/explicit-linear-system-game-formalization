module

public import ThomGame.Analysis.CompressorPositiveGeneratorGap
public import ThomGame.Analysis.MatrixRepresentationMarkovGap
public import ThomGame.Analysis.MatrixUnitaryTupleLifting

/-! The H spectral gap on the actual matrix trace Hilbert space, with exact coordinate unitary lifts. -/

@[expose] public noncomputable section
namespace ThomGame.Compressor

open Analysis Filter

def positiveMarkovGapConstant : ℝ :=
  representationMarkovGapConstant 24 (positiveGeneratorKazhdanConstant ^ 2)

theorem positiveMarkovGapConstant_pos : 0 < positiveMarkovGapConstant :=
  representationMarkovGapConstant_pos 24 _ (sq_pos_of_pos positiveGeneratorKazhdanConstant_pos)

theorem positiveMarkovGapConstant_lt_one : positiveMarkovGapConstant < 1 :=
  representationMarkovGapConstant_lt_one 24 _

theorem positiveMarkovGapConstant_formula :
    positiveMarkovGapConstant = min (1 / 2) (positiveGeneratorKazhdanConstant ^ 2 / 96) := by
  norm_num [positiveMarkovGapConstant, representationMarkovGapConstant, lazyMarkovWeight,
    div_eq_mul_inv, mul_comm]

variable (dims : Nat → Nat) (hd : ∀ n, 0 < dims n) (L : Ultrafilter Nat)
  (hL : (L : Filter Nat) ≤ atTop)
  (φ : GroupQ →* unitary (MatrixTracialQuotient dims (L : Filter Nat)))

include hL in
theorem positiveGeneratorTuple_matrixGap (V : (n : Nat) → Fin 24 → UnitaryMatrix (dims n))
    (hV : ∀ j, matrixTupleClass dims V (L : Filter Nat) j = (φ (positiveGeneratorTuple j)).val) :
    MatrixMarkovSpectralGap dims V hd L positiveMarkovGapConstant := by
  apply matrixMarkovSpectralGap_of_representation_energy dims hd L hL V φ positiveSubgroup
    positiveGeneratorTuple positiveGeneratorTuple_generates hV (positiveGeneratorKazhdanConstant ^ 2)
    (sq_pos_of_pos positiveGeneratorKazhdanConstant_pos)
  intro ξ hξ
  exact positiveGeneratorTuple_energy_gap (matrixConjugationRepresentation dims hd L φ) ξ hξ

include hL in
theorem exists_positiveGeneratorTuple_matrixGap :
    ∃ V : (n : Nat) → Fin 24 → UnitaryMatrix (dims n),
      (∀ j, matrixTupleClass dims V (L : Filter Nat) j = (φ (positiveGeneratorTuple j)).val) ∧
      MatrixMarkovSpectralGap dims V hd L positiveMarkovGapConstant := by
  obtain ⟨V, hV⟩ := exists_matrixTuple_unitary_lift dims hd (L : Filter Nat) (fun j => φ (positiveGeneratorTuple j))
  exact ⟨V, hV, positiveGeneratorTuple_matrixGap dims hd L hL φ V hV⟩

end ThomGame.Compressor
