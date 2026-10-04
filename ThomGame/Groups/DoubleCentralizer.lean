module

public import ThomGame.Groups.DoubleToLambda
public import ThomGame.Groups.CompressorCompression
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.Group

/-!
# The algebraic centralizer argument for the specified word

The difference t₁⁻¹t₂ centralizes H in the actual double. Consequently,
any homomorphism whose image of t₁ normalizes the centralizer of the image
of H kills the specified obstruction word. No injectivity is assumed.
Proving this normalizer condition for matrix ultraproducts is separate.
-/

@[expose] public section
namespace ThomGame.Double

def positiveHom : Compressor.positiveSubgroup →* GroupD :=
  (copyHom false).comp Compressor.positiveSubgroup.subtype

theorem positiveHom_h :
    positiveHom ⟨Compressor.hElement, Compressor.h_mem_positiveSubgroup⟩ = hElement := copy_h false

theorem common_conjugate (x : Compressor.positiveSubgroup) :
    t₁Element * positiveHom x * t₁Element⁻¹ = t₂Element * positiveHom x * t₂Element⁻¹ := by
  have h := copyHom_positive
    ⟨Compressor.tElement * x.val * Compressor.tElement⁻¹,
      Compressor.shear_compresses Compressor.root12 x.val x.property⟩
  change copyHom false (Compressor.tElement * x.val * Compressor.tElement⁻¹) =
    copyHom true (Compressor.tElement * x.val * Compressor.tElement⁻¹) at h
  simp only [map_mul, map_inv, Compressor.tElement, copy_t₁, copy_t₂] at h
  rw [← copyHom_positive x] at h
  exact h

def centralizingDifference : GroupD := t₁Element⁻¹ * t₂Element

theorem difference_commutes (x : Compressor.positiveSubgroup) :
    Commute (positiveHom x) centralizingDifference := by
  have h := congrArg (fun y => t₁Element⁻¹ * y * t₁Element) (common_conjugate x).symm
  have hc : centralizingDifference * positiveHom x * centralizingDifference⁻¹ = positiveHom x := by
    simpa [centralizingDifference, mul_assoc] using h
  exact (mul_inv_eq_iff_eq_mul.mp hc).symm

variable {G : Type*} [Group G]

def imageCentralizer (φ : GroupD →* G) : Subgroup G :=
  Subgroup.centralizer (Set.range (φ.comp positiveHom))

theorem difference_image_mem (φ : GroupD →* G) : φ centralizingDifference ∈ imageCentralizer φ := by
  rintro y ⟨x, rfl⟩
  exact ((difference_commutes x).map φ).eq

theorem hom_obstruction_eq_one_of_normalizes_centralizer (φ : GroupD →* G)
    (hn : φ t₁Element ∈ Subgroup.normalizer (imageCentralizer φ : Set G)) :
    φ obstructionElement = 1 := by
  have hc : φ (t₂Element * t₁Element⁻¹) ∈ imageCentralizer φ := by
    have h := (Subgroup.mem_normalizer_iff.mp hn (φ centralizingDifference)).mp (difference_image_mem φ)
    simpa [centralizingDifference, map_mul, map_inv, mul_assoc] using h
  have hh : φ hElement ∈ Set.range (φ.comp positiveHom) := by
    refine ⟨⟨Compressor.hElement, Compressor.h_mem_positiveSubgroup⟩, ?_⟩
    simp only [MonoidHom.comp_apply, positiveHom_h]
  have he := hc (φ hElement) hh
  rw [obstruction_formula]
  simp only [map_mul, map_inv] at he ⊢
  rw [he]
  group

end ThomGame.Double

namespace ThomGame.Lambda
variable {G : Type*} [Group G]

theorem hom_J_eq_one_of_normalizes_centralizer (φ : GroupLambda →* G)
    (hn : (φ.comp Double.toLambda) Double.t₁Element ∈
      Subgroup.normalizer (Double.imageCentralizer (φ.comp Double.toLambda) : Set G)) :
    φ JElement = 1 := by
  apply hom_J_eq_one_of_obstruction_eq_one
  have h := Double.hom_obstruction_eq_one_of_normalizes_centralizer (φ.comp Double.toLambda) hn
  simpa only [MonoidHom.comp_apply, Double.toLambda_obstruction] using h

end ThomGame.Lambda
