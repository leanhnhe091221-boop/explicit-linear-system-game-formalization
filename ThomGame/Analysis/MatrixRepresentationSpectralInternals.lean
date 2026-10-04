module

public import ThomGame.Analysis.UnitaryRepresentationGenerators
public import ThomGame.Analysis.MatrixALTTheorem5_2
public import ThomGame.Analysis.MatrixThomGroupNormalization

/-!
# From genuine representation spectral gaps to Thom normalization

The finite tuples represent generators of the actual subgroups. ALT
constructs their internal commutants, and the proved normalization chain
then applies. The Hilbert-space spectral gaps remain explicit inputs.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter

theorem exists_matrixRepresentation_internal_commutant_of_gap {G : Type*} [Group G]
    (dims : Nat → Nat) (hd : ∀ n, 0 < dims n) (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop)
    (φ : G →* unitary (MatrixTracialQuotient dims (L : Filter Nat)))
    (H : Subgroup G) {h : Nat} [NeZero h] (s : Fin h → G)
    (hgen : Subgroup.closure (Set.range s) = H)
    (V : (n : Nat) → Fin h → UnitaryMatrix (dims n))
    (hV : ∀ j, matrixTupleClass dims V (L : Filter Nat) j = (φ (s j)).val)
    (κ : ℝ) (hgap : MatrixMarkovSpectralGap dims V hd L κ) :
    ∃ A : (n : Nat) → StarSubalgebra ℂ (CMatrix (dims n)),
      unitaryRepresentationCommutant φ H = matrixInternalQuotient dims A (L : Filter Nat) := by
  obtain ⟨A, _, hA, _⟩ := exists_matrixALT_internal_relative_commutant_and_center dims V hd L hL κ hgap
  refine ⟨A, ?_⟩
  rw [unitaryRepresentationCommutant_eq_generatorCommutant φ H s hgen]
  have he : matrixTupleClass dims V (L : Filter Nat) = fun j => (φ (s j)).val := funext hV
  rw [← he]
  exact hA

theorem matrixThom_groupCentralizer_normalized_of_spectral_gaps {G : Type*} [Group G]
    (dims : Nat → Nat) (hd : ∀ n, 0 < dims n) (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop)
    (H : Subgroup G) {h : Nat} (t : Fin h → G)
    (hgen : Subgroup.closure ((H : Set G) ∪ Set.range t) = ⊤)
    (hcomp : ∀ j g, g ∈ H → t j * g * (t j)⁻¹ ∈ H)
    (φ : G →* unitary (MatrixTracialQuotient dims (L : Filter Nat)))
    {kH kG : Nat} [NeZero kH] [NeZero kG] (sH : Fin kH → G) (sG : Fin kG → G)
    (hgenH : Subgroup.closure (Set.range sH) = H) (hgenG : Subgroup.closure (Set.range sG) = ⊤)
    (VH : (n : Nat) → Fin kH → UnitaryMatrix (dims n))
    (VG : (n : Nat) → Fin kG → UnitaryMatrix (dims n))
    (hVH : ∀ j, matrixTupleClass dims VH (L : Filter Nat) j = (φ (sH j)).val)
    (hVG : ∀ j, matrixTupleClass dims VG (L : Filter Nat) j = (φ (sG j)).val)
    (κH κG : ℝ) (hgapH : MatrixMarkovSpectralGap dims VH hd L κH)
    (hgapG : MatrixMarkovSpectralGap dims VG hd L κG) :
    ∀ g, φ g ∈ Subgroup.normalizer
      (Subgroup.centralizer (Set.range (φ.comp H.subtype)) :
        Set (unitary (MatrixTracialQuotient dims (L : Filter Nat)))) := by
  let : ∀ n, NeZero (dims n) := fun n => ⟨ne_of_gt (hd n)⟩
  exact matrixThom_groupCentralizer_normalized dims L H t hgen hcomp φ
    (exists_matrixRepresentation_internal_commutant_of_gap dims hd L hL φ H sH hgenH VH hVH κH hgapH)
    (exists_matrixRepresentation_internal_commutant_of_gap dims hd L hL φ ⊤ sG hgenG VG hVG κG hgapG)

end ThomGame.Analysis
