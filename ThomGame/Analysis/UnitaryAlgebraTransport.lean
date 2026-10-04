module

public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import Mathlib.Basic.Complex.Basic

/-!
# Unitary commutants under actual star algebra maps

The maps below use the given algebra homomorphism on unitary elements.
An equivalence preserves conjugation and reflects the full commutant.
-/

@[expose] public section
namespace ThomGame.Analysis

variable {R S : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
    [Ring S] [StarRing S] [Algebra ℂ S] [StarModule ℂ S]

def starAlgHomUnitary (f : R →⋆ₐ[ℂ] S) : unitary R →* unitary S where
  toFun u := ⟨f u.val, Unitary.map_mem f u.property⟩
  map_one' := Subtype.ext (map_one f)
  map_mul' u v := Subtype.ext (map_mul f u.val v.val)

omit [StarModule ℂ R] [StarModule ℂ S] in
@[simp] theorem starAlgHomUnitary_val (f : R →⋆ₐ[ℂ] S) (u : unitary R) :
    (starAlgHomUnitary f u).val = f u.val := rfl

theorem unitaryRangeCommutant_mem_iff {α : Type*} (u : α → unitary R) (x : R) :
    x ∈ StarSubalgebra.centralizer ℂ (Set.range (fun j => (u j).val)) ↔
      ∀ j, Commute (u j).val x := by
  rw [StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro hx j
    exact (hx _ ⟨j, rfl⟩).1
  · rintro hx _ ⟨j, rfl⟩
    refine ⟨(hx j).eq, ?_⟩
    have he := (commute_unitary_iff_star_left_conjugate (u j).property).mp (hx j)
    exact ((commute_unitary_iff_star_right_conjugate (Unitary.star_mem (u j).property)).mpr
      (by simpa only [star_star] using he)).eq

omit [StarModule ℂ R] [StarModule ℂ S] in
theorem starAlgEquiv_commute_iff (e : R ≃⋆ₐ[ℂ] S) (a b : R) :
    Commute (e a) (e b) ↔ Commute a b := by
  change e a * e b = e b * e a ↔ a * b = b * a
  rw [← map_mul, ← map_mul]
  exact e.injective.eq_iff

omit [StarModule ℂ R] [StarModule ℂ S] in
theorem starAlgEquiv_unitaryPullback_apply (e : R ≃⋆ₐ[ℂ] S) (u : unitary R) (x : R) :
    e ((Unitary.conjStarAlgAut ℂ R u).symm x) =
      (Unitary.conjStarAlgAut ℂ S (starAlgHomUnitary e.toStarAlgHom u)).symm (e x) := by
  change e (star u.val * x * u.val) = star (e u.val) * e x * e u.val
  rw [map_mul, map_mul, map_star]

theorem starAlgEquiv_unitaryCommutant_mem_iff {α : Type*} (e : R ≃⋆ₐ[ℂ] S)
    (u : α → unitary R) (x : R) :
    e x ∈ StarSubalgebra.centralizer ℂ
        (Set.range (fun j => (starAlgHomUnitary e.toStarAlgHom (u j)).val)) ↔
      x ∈ StarSubalgebra.centralizer ℂ (Set.range (fun j => (u j).val)) := by
  rw [unitaryRangeCommutant_mem_iff, unitaryRangeCommutant_mem_iff]
  exact forall_congr' fun j => starAlgEquiv_commute_iff e (u j).val x

end ThomGame.Analysis
