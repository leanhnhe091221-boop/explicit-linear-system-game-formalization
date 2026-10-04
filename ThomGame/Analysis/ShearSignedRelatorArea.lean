module

public import ThomGame.Analysis.RelatorAreaCalculus
public import ThomGame.Groups.IntegralShearPresentation

/-! Signed elementary shear identities with explicit defining-relator area. -/

@[expose] public section
namespace ThomGame.Analysis

open Compressor

def shearSigned (r : Root) (positive : Bool) : FreeGroup Root :=
  if positive then FreeGroup.of r else (FreeGroup.of r)⁻¹

theorem shear_separated_area (r s : Root) (hrs : separated r s) :
    RelatorEquality IntegralShear.relators
      (FreeGroup.of r * FreeGroup.of s) (FreeGroup.of s * FreeGroup.of r) 1 := by
  refine ⟨1, le_rfl, ?_⟩
  have h := RelatorArea.relator (rels := IntegralShear.relators)
    (show IntegralShear.relator (.separated ⟨(r,s), hrs⟩) ∈ IntegralShear.relators
      from ⟨_, rfl⟩)
  simpa only [IntegralShear.relator, PrimeFiveRankThreeCover.comm, mul_inv_rev,
    mul_assoc] using h

theorem shear_signed_separated_area (r s : Root) (hrs : separated r s) (a b : Bool) :
    RelatorEquality IntegralShear.relators
      (shearSigned r a * shearSigned s b) (shearSigned s b * shearSigned r a) 1 := by
  have h := shear_separated_area r s hrs
  cases a <;> cases b
  · exact h.commute_inv_left.commute_inv_right
  · exact h.commute_inv_left
  · exact h.commute_inv_right
  · exact h

theorem shear_root_area (r : Root) :
    RelatorEquality IntegralShear.relators
      (FreeGroup.of r * FreeGroup.of (right r))
      (FreeGroup.of (across r) * FreeGroup.of (right r) * FreeGroup.of r) 1 := by
  refine ⟨1, le_rfl, ?_⟩
  have h := RelatorArea.relator (rels := IntegralShear.relators)
    (show IntegralShear.relator (.adjacent r) ∈ IntegralShear.relators from ⟨_, rfl⟩)
  simpa only [IntegralShear.relator, PrimeFiveRankThreeCover.comm, mul_inv_rev,
    mul_assoc] using h

theorem shear_signed_root_area (r : Root) (a b : Bool) :
    RelatorEquality IntegralShear.relators
      (shearSigned r a * shearSigned (right r) b)
      (shearSigned (across r) (a == b) * shearSigned (right r) b * shearSigned r a) 3 := by
  have hac := shear_separated_area r (across r)
    ((by decide +kernel : ∀ r : Root, separated r (across r)) r)
  have hbc := shear_separated_area (right r) (across r)
    ((by decide +kernel : ∀ r : Root, separated (right r) (across r)) r)
  have h := shear_root_area r
  cases a <;> cases b
  · simpa [shearSigned] using
      (h.root_inv_left hac).root_inv_right hbc.commute_inv_right
  · exact (h.root_inv_left hac).mono (by decide)
  · exact (h.root_inv_right hbc).mono (by decide)
  · exact h.mono (by decide)

end ThomGame.Analysis
