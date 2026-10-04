module

public import ThomGame.Analysis.CompressorShearKazhdanGap
public import ThomGame.Analysis.MatrixRepresentationMarkovGap
public import ThomGame.Analysis.MatrixUnitaryTupleLifting

/-! The shear Kazhdan hypothesis gives the actual Q trace Hilbert gap, uniformly in dimension. -/

@[expose] public noncomputable section
namespace ThomGame.Compressor

open Analysis Filter

def shearMarkovGapConstant (S : Finset IntegralShear.ShearGroup) (b : ℝ) : ℝ :=
  representationMarkovGapConstant 48 (shearGeneratorKazhdanConstant S b ^ 2)

theorem shearMarkovGapConstant_pos (S : Finset IntegralShear.ShearGroup) {b : ℝ} (hb : 0 < b) :
    0 < shearMarkovGapConstant S b :=
  representationMarkovGapConstant_pos 48 _ (sq_pos_of_pos (shearGeneratorKazhdanConstant_pos S hb))

theorem shearMarkovGapConstant_lt_one (S : Finset IntegralShear.ShearGroup) (b : ℝ) :
    shearMarkovGapConstant S b < 1 := representationMarkovGapConstant_lt_one 48 _

theorem shearMarkovGapConstant_formula (S : Finset IntegralShear.ShearGroup) (b : ℝ) :
    shearMarkovGapConstant S b = min (1 / 2) (shearGeneratorKazhdanConstant S b ^ 2 / 192) := by
  norm_num [shearMarkovGapConstant, representationMarkovGapConstant, lazyMarkovWeight,
    div_eq_mul_inv, mul_comm]

variable (S : Finset IntegralShear.ShearGroup) (b : ℝ) (hb : 0 < b)
  (hS : HilbertKazhdanBound.{0} S b)
  (dims : Nat → Nat) (hd : ∀ n, 0 < dims n) (L : Ultrafilter Nat)
  (hL : (L : Filter Nat) ≤ atTop)
  (φ : GroupQ →* unitary (MatrixTracialQuotient dims (L : Filter Nat)))

include hb hS hL in
theorem generatorTuple_matrixGap_of_shear (V : (n : Nat) → Fin 48 → UnitaryMatrix (dims n))
    (hV : ∀ j, matrixTupleClass dims V (L : Filter Nat) j = (φ (generatorTuple j)).val) :
    MatrixMarkovSpectralGap dims V hd L (shearMarkovGapConstant S b) := by
  apply matrixMarkovSpectralGap_of_representation_energy dims hd L hL V φ ⊤
    generatorTuple generatorTuple_generates hV (shearGeneratorKazhdanConstant S b ^ 2)
    (sq_pos_of_pos (shearGeneratorKazhdanConstant_pos S hb))
  intro ξ hξ
  have htop : Function.Surjective (⊤ : Subgroup GroupQ).subtype := fun g => ⟨⟨g, trivial⟩, rfl⟩
  rw [hilbertUnitaryInvariants_comp_surjective _ _ htop] at hξ
  exact generatorTuple_energy_of_shear S b hb hS (matrixConjugationRepresentation dims hd L φ) ξ hξ

include hb hS hL in
theorem exists_generatorTuple_matrixGap_of_shear :
    ∃ V : (n : Nat) → Fin 48 → UnitaryMatrix (dims n),
      (∀ j, matrixTupleClass dims V (L : Filter Nat) j = (φ (generatorTuple j)).val) ∧
      MatrixMarkovSpectralGap dims V hd L (shearMarkovGapConstant S b) := by
  obtain ⟨V, hV⟩ := exists_matrixTuple_unitary_lift dims hd (L : Filter Nat) (fun j => φ (generatorTuple j))
  exact ⟨V, hV, generatorTuple_matrixGap_of_shear S b hb hS dims hd L hL φ V hV⟩

theorem exists_uniform_generatorTuple_matrixGap_of_shear
    (hShear : HasFiniteHilbertKazhdanSet.{0} IntegralShear.ShearGroup) :
    ∃ κ : ℝ, 0 < κ ∧ κ < 1 ∧
      ∀ (dims : Nat → Nat) (hd : ∀ n, 0 < dims n) (L : Ultrafilter Nat), (L : Filter Nat) ≤ atTop →
        ∀ (φ : GroupQ →* unitary (MatrixTracialQuotient dims (L : Filter Nat))),
          ∃ V : (n : Nat) → Fin 48 → UnitaryMatrix (dims n),
            (∀ j, matrixTupleClass dims V (L : Filter Nat) j = (φ (generatorTuple j)).val) ∧
            MatrixMarkovSpectralGap dims V hd L κ := by
  obtain ⟨S, b, hb, hS⟩ := hShear
  refine ⟨shearMarkovGapConstant S b, shearMarkovGapConstant_pos S hb,
    shearMarkovGapConstant_lt_one S b, ?_⟩
  intro dims hd L hL φ
  exact exists_generatorTuple_matrixGap_of_shear S b hb hS dims hd L hL φ

end ThomGame.Compressor
