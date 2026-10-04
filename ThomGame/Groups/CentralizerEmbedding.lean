module

public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Pulling centralizer normalization back along an injective homomorphism

The centralizer in the larger group need not be contained in the image.
Its preimage is precisely the original centralizer, which suffices to
pull back its normalizer. Surjectivity is not required.
-/

@[expose] public section
namespace ThomGame

variable {G K H : Type*} [Group G] [Group K] [Group H]

theorem centralizer_comap_image_of_injective (f : G →* K) (hf : Function.Injective f)
    (s : Set G) : (Subgroup.centralizer (f '' s)).comap f = Subgroup.centralizer s := by
  ext x
  change (∀ y ∈ f '' s, y * f x = f x * y) ↔ ∀ y ∈ s, y * x = x * y
  constructor
  · intro hx y hy
    apply hf
    simpa only [map_mul] using hx (f y) ⟨y, hy, rfl⟩
  · rintro hx _ ⟨y, hy, rfl⟩
    simpa only [map_mul] using congrArg f (hx y hy)

theorem normalizes_centralizer_of_injective (f : G →* K) (hf : Function.Injective f)
    (s : Set G) (x : G)
    (hx : f x ∈ Subgroup.normalizer (Subgroup.centralizer (f '' s) : Set K)) :
    x ∈ Subgroup.normalizer (Subgroup.centralizer s : Set G) := by
  have h := Subgroup.le_normalizer_comap (H := Subgroup.centralizer (f '' s)) f hx
  simpa only [centralizer_comap_image_of_injective f hf s] using h

theorem normalizes_centralizer_range_of_injective (f : G →* K) (hf : Function.Injective f)
    (φ : H →* G) (x : G)
    (hx : f x ∈ Subgroup.normalizer (Subgroup.centralizer (Set.range (f.comp φ)) : Set K)) :
    x ∈ Subgroup.normalizer (Subgroup.centralizer (Set.range φ) : Set G) := by
  apply normalizes_centralizer_of_injective f hf (Set.range φ) x
  simpa only [MonoidHom.coe_comp, Set.range_comp] using hx

end ThomGame
