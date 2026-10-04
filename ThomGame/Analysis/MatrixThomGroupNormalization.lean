module

public import ThomGame.Analysis.MatrixThomInternalNormalization
public import ThomGame.Analysis.UnitaryRepresentationCommutants

/-!
# Thom normalization for arbitrary homomorphisms with internal commutants

The internality of the two actual representation commutants is the only
analytic premise. Generation and compression supply the anchor and
inclusions; alignment and Theorem 4.2 supply equality. Normalization of
the unitary-group centralizer follows for every group element.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter

theorem matrixThom_groupCentralizer_normalized {ι G : Type*} [Group G]
    (dims : ι → Nat) [∀ n, NeZero (dims n)] (L : Ultrafilter ι)
    (H : Subgroup G) {h : Nat} (t : Fin h → G)
    (hgen : Subgroup.closure ((H : Set G) ∪ Set.range t) = ⊤)
    (hcomp : ∀ j g, g ∈ H → t j * g * (t j)⁻¹ ∈ H)
    (φ : G →* unitary (MatrixTracialQuotient dims (L : Filter ι)))
    (hH : ∃ A : (n : ι) → StarSubalgebra ℂ (CMatrix (dims n)),
      unitaryRepresentationCommutant φ H = matrixInternalQuotient dims A (L : Filter ι))
    (hG : ∃ D : (n : ι) → StarSubalgebra ℂ (CMatrix (dims n)),
      unitaryRepresentationCommutant φ ⊤ = matrixInternalQuotient dims D (L : Filter ι)) :
    ∀ g, φ g ∈ Subgroup.normalizer
      (Subgroup.centralizer (Set.range (φ.comp H.subtype)) : Set (unitary (MatrixTracialQuotient dims (L : Filter ι)))) := by
  obtain ⟨A, hA⟩ := hH
  obtain ⟨D, hD⟩ := hG
  have hanchor := unitaryRepresentationCommutant_generator_anchor φ H t hgen
  rw [hA, hD] at hanchor
  have hi j : (matrixInternalQuotient dims A (L : Filter ι)).map
      (Unitary.conjStarAlgAut ℂ (MatrixTracialQuotient dims (L : Filter ι)) (φ (t j))).symm.toStarAlgHom ≤
        matrixInternalQuotient dims A (L : Filter ι) := by
    rw [← hA]
    exact unitaryRepresentationCommutant_compressor_inclusion φ H (t j) (hcomp j)
  have he := matrixThom_internal_normalization dims A D L (fun j => φ (t j)) hi hanchor
  let C := Subgroup.centralizer (Set.range (φ.comp H.subtype))
  let K := (Subgroup.normalizer (C : Set (unitary (MatrixTracialQuotient dims (L : Filter ι))))).comap φ
  have hK : Subgroup.closure ((H : Set G) ∪ Set.range t) ≤ K := by
    apply (Subgroup.closure_le K).mpr
    rintro g (hg | ⟨j, rfl⟩)
    · apply Subgroup.centralizer_le_normalizer
      intro v hv
      exact (hv (φ g) ⟨⟨g, hg⟩, rfl⟩).symm
    · apply unitaryRepresentationCommutant_normalizer_of_pullback_eq φ H (φ (t j))
      simpa only [hA] using he j
  rw [hgen] at hK
  exact fun g => hK (Subgroup.mem_top g)

end ThomGame.Analysis
