module

public import ThomGame.Analysis.ApproximationCriterion

/-!
# Approximate triviality passes along actual homomorphisms

For finite relator sets, restrict exact representations in the unitary
sequence quotient along the given homomorphism, then apply the proved
approximation criterion. No injectivity or extension of an approximate
matrix assignment is needed. Equality in the presented group therefore
also preserves approximate triviality.
-/

@[expose] public section
namespace ThomGame.Analysis

variable {S T : Type*} {rels : Set (FreeGroup S)} {rels' : Set (FreeGroup T)}

theorem approximatelyTrivial_map (hrels : rels.Finite) (hrels' : rels'.Finite)
    (φ : PresentedGroup rels →* PresentedGroup rels') (v : FreeGroup S) (w : FreeGroup T)
    (he : φ (PresentedGroup.mk rels v) = PresentedGroup.mk rels' w)
    (h : ApproximatelyTrivial rels v) : ApproximatelyTrivial rels' w := by
  apply (approximatelyTrivial_iff_hyperfilter_killed rels' w hrels').mpr
  intro dims hd ψ
  have hk := (approximatelyTrivial_iff_hyperfilter_killed rels v hrels).mp h dims hd (ψ.comp φ)
  simpa only [MonoidHom.comp_apply, he] using hk

theorem approximatelyTrivial_congr (hrels : rels.Finite) (v w : FreeGroup S)
    (he : PresentedGroup.mk rels v = PresentedGroup.mk rels w) :
    ApproximatelyTrivial rels v ↔ ApproximatelyTrivial rels w := by
  constructor
  · exact approximatelyTrivial_map hrels hrels (MonoidHom.id _) v w he
  · exact approximatelyTrivial_map hrels hrels (MonoidHom.id _) w v he.symm

theorem approximatelyTrivial_of_eq_one (hrels : rels.Finite) (v : FreeGroup S)
    (he : PresentedGroup.mk rels v = 1) : ApproximatelyTrivial rels v := by
  apply (approximatelyTrivial_iff_hyperfilter_killed rels v hrels).mpr
  intro dims hd φ
  rw [he, map_one]

end ThomGame.Analysis
