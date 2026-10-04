module

public import ThomGame.Analysis.UnitaryAlgebraTransport
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Lattice

/-!
# Algebraic commutants of arbitrary unitary representations

Generation gives the anchor, and a compressor gives the required
one-sided algebra inclusion. Equality under conjugation implies
normalization of the actual unitary-group centralizer. Injectivity of
the representation is never assumed.
-/

@[expose] public section
namespace ThomGame.Analysis

variable {R G : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R] [Group G]

def unitaryRepresentationCommutant (φ : G →* unitary R) (H : Subgroup G) : StarSubalgebra ℂ R :=
  StarSubalgebra.centralizer ℂ (Set.range (fun g : H => (φ g.val).val))

theorem unitaryRepresentationCommutant_mem_iff (φ : G →* unitary R) (H : Subgroup G) (x : R) :
    x ∈ unitaryRepresentationCommutant φ H ↔ ∀ g ∈ H, Commute (φ g).val x := by
  rw [unitaryRepresentationCommutant, unitaryRangeCommutant_mem_iff]
  exact ⟨fun h g hg => h ⟨g, hg⟩, fun h g => h g.val g.property⟩

omit [StarModule ℂ R] in
def unitaryCommutingSubgroup (x : R) : Subgroup (unitary R) where
  carrier := {u | Commute u.val x}
  one_mem' := Commute.one_left x
  mul_mem' hu hv := hu.mul_left hv
  inv_mem' {u} hu := by
    have he := (commute_unitary_iff_star_left_conjugate u.property).mp hu
    exact (commute_unitary_iff_star_right_conjugate (Unitary.star_mem u.property)).mpr
      (by simpa only [star_star] using he)

theorem unitaryRepresentationCommutant_generator_anchor (φ : G →* unitary R)
    (H : Subgroup G) {α : Type*} (t : α → G)
    (hgen : Subgroup.closure ((H : Set G) ∪ Set.range t) = ⊤) :
    unitaryRepresentationCommutant φ H ⊓
      StarSubalgebra.centralizer ℂ (Set.range (fun j => (φ (t j)).val)) =
        unitaryRepresentationCommutant φ ⊤ := by
  ext x
  change (x ∈ unitaryRepresentationCommutant φ H ∧
    x ∈ StarSubalgebra.centralizer ℂ (Set.range (fun j => (φ (t j)).val))) ↔
      x ∈ unitaryRepresentationCommutant φ ⊤
  rw [unitaryRepresentationCommutant_mem_iff, unitaryRangeCommutant_mem_iff,
    unitaryRepresentationCommutant_mem_iff]
  constructor
  · rintro ⟨hH, ht⟩ g _
    let K := (unitaryCommutingSubgroup x).comap φ
    have hK : Subgroup.closure ((H : Set G) ∪ Set.range t) ≤ K := by
      apply (Subgroup.closure_le K).mpr
      rintro z (hz | ⟨j, rfl⟩)
      · exact hH z hz
      · exact ht j
    rw [hgen] at hK
    exact hK (Subgroup.mem_top g)
  · intro h
    exact ⟨fun g _ => h g (Subgroup.mem_top g), fun j => h (t j) (Subgroup.mem_top _)⟩

theorem unitaryRepresentationCommutant_compressor_inclusion (φ : G →* unitary R)
    (H : Subgroup G) (t : G) (ht : ∀ g ∈ H, t * g * t⁻¹ ∈ H) :
    (unitaryRepresentationCommutant φ H).map
      (Unitary.conjStarAlgAut ℂ R (φ t)).symm.toStarAlgHom ≤ unitaryRepresentationCommutant φ H := by
  rintro z ⟨x, hx, rfl⟩
  change x ∈ unitaryRepresentationCommutant φ H at hx
  rw [unitaryRepresentationCommutant_mem_iff] at hx ⊢
  intro g hg
  let e := Unitary.conjStarAlgAut ℂ R (φ t)
  apply (starAlgEquiv_commute_iff e (φ g).val (e.symm x)).mp
  change Commute (e (φ g).val) (e (e.symm x))
  rw [StarAlgEquiv.apply_symm_apply]
  have he : e (φ g).val = (φ (t * g * t⁻¹)).val := by
    simp only [e, Unitary.conjStarAlgAut_apply, map_mul, map_inv, Submonoid.coe_mul]
    rfl
  rw [he]
  exact hx _ (ht g hg)

theorem unitaryRepresentationCommutant_unitary_mem_iff (φ : G →* unitary R)
    (H : Subgroup G) (u : unitary R) :
    u.val ∈ unitaryRepresentationCommutant φ H ↔
      u ∈ Subgroup.centralizer (Set.range (φ.comp H.subtype)) := by
  rw [unitaryRepresentationCommutant_mem_iff, Subgroup.mem_centralizer_iff]
  constructor
  · rintro hc _ ⟨g, rfl⟩
    exact Subtype.ext (hc g.val g.property).eq
  · intro hc g hg
    exact congrArg Subtype.val (hc (φ g) ⟨⟨g, hg⟩, rfl⟩)

theorem starAlgEquiv_mem_iff_of_symm_map_eq (A : StarSubalgebra ℂ R) (e : R ≃⋆ₐ[ℂ] R)
    (he : A.map e.symm.toStarAlgHom = A) (x : R) : x ∈ A ↔ e x ∈ A := by
  constructor
  · intro hx
    have hx' : x ∈ A.map e.symm.toStarAlgHom := by rwa [he]
    obtain ⟨y, hy, hyx⟩ := hx'
    have hxy : e x = y := by
      change e.symm y = x at hyx
      rw [← hyx, StarAlgEquiv.apply_symm_apply]
    rwa [hxy]
  · intro hx
    have hx' : e.symm (e x) ∈ A.map e.symm.toStarAlgHom := ⟨e x, hx, rfl⟩
    simpa only [StarAlgEquiv.symm_apply_apply, he] using hx'

theorem unitaryRepresentationCommutant_normalizer_of_pullback_eq (φ : G →* unitary R)
    (H : Subgroup G) (u : unitary R)
    (he : (unitaryRepresentationCommutant φ H).map
      (Unitary.conjStarAlgAut ℂ R u).symm.toStarAlgHom = unitaryRepresentationCommutant φ H) :
    u ∈ Subgroup.normalizer (Subgroup.centralizer (Set.range (φ.comp H.subtype)) : Set (unitary R)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro v
  rw [← unitaryRepresentationCommutant_unitary_mem_iff, ← unitaryRepresentationCommutant_unitary_mem_iff]
  exact starAlgEquiv_mem_iff_of_symm_map_eq _ (Unitary.conjStarAlgAut ℂ R u) he v.val

end ThomGame.Analysis
