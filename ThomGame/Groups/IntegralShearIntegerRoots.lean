module

public import ThomGame.Groups.IntegralShearPresentation
public import ThomGame.Groups.CentralCommutatorIntegerPowers

/-! Derive all integer-parameter Steinberg root relations from the actual six generators. -/

@[expose] public section
namespace ThomGame.IntegralShear

open Compressor
open scoped commutatorElement

set_option backward.isDefEq.respectTransparency false in
theorem of_commute (r s : Root) (hrs : separated r s) : Commute (of r) (of s) := by
  apply commutatorElement_eq_one_iff_commute.mp
  change @Eq (PresentedGroup relators) ⁅PresentedGroup.of r, PresentedGroup.of s⁆ 1
  have h := PresentedGroup.one_of_mem (rels := relators)
    ⟨Relation.separated ⟨(r, s), hrs⟩, rfl⟩
  simpa only [relator, PrimeFiveRankThreeCover.comm, map_mul, map_inv, PresentedGroup.of,
    commutatorElement_def] using h

set_option backward.isDefEq.respectTransparency false in
theorem of_commutator (r : Root) : ⁅of r, of (right r)⁆ = of (across r) := by
  change @Eq (PresentedGroup relators) ⁅PresentedGroup.of r, PresentedGroup.of (right r)⁆
    (PresentedGroup.of (across r))
  have h := PresentedGroup.one_of_mem (rels := relators) ⟨Relation.adjacent r, rfl⟩
  simpa only [relator, PrimeFiveRankThreeCover.comm, map_mul, map_inv,
    mul_inv_eq_one, PresentedGroup.of, commutatorElement_def] using h

set_option backward.isDefEq.respectTransparency false in
theorem of_torsion : (of root12 * (of (reverse root12))⁻¹ * of root12) ^ 4 = 1 := by
  have h : (PresentedGroup.mk relators : FreeGroup Root →* ShearGroup) (relator Relation.torsion) = 1 :=
    PresentedGroup.one_of_mem (rels := relators) ⟨Relation.torsion, rfl⟩
  simpa only [relator, map_mul, map_inv, map_pow, of, PresentedGroup.of] using h

def rootElement (r : Root) (m : ℤ) : ShearGroup := of r ^ m

@[simp] theorem rootElement_zero (r : Root) : rootElement r 0 = 1 := zpow_zero _

@[simp] theorem rootElement_one (r : Root) : rootElement r 1 = of r := zpow_one _

theorem rootElement_add (r : Root) (m n : ℤ) : rootElement r (m + n) = rootElement r m * rootElement r n :=
  zpow_add _ _ _

theorem rootElement_neg (r : Root) (m : ℤ) : rootElement r (-m) = (rootElement r m)⁻¹ := zpow_neg _ _

theorem rootElement_commute (r s : Root) (hrs : separated r s) (m n : ℤ) :
    Commute (rootElement r m) (rootElement s n) := (of_commute r s hrs).zpow_zpow m n

theorem rootElement_commutator (r : Root) (m n : ℤ) :
    ⁅rootElement r m, rootElement (right r) n⁆ = rootElement (across r) (m * n) := by
  have ha : Commute (of r) ⁅of r, of (right r)⁆ := by
    rw [of_commutator]
    exact of_commute r (across r) (by revert r; decide +kernel)
  have hb : Commute (of (right r)) ⁅of r, of (right r)⁆ := by
    rw [of_commutator]
    exact of_commute (right r) (across r) (by clear ha; revert r; decide +kernel)
  simpa only [rootElement, of_commutator] using centralCommutator_zpow_zpow ha hb m n

theorem rootElement_conjugate (r : Root) (m n : ℤ) :
    rootElement r m * rootElement (right r) n * (rootElement r m)⁻¹ =
      rootElement (across r) (m * n) * rootElement (right r) n := by
  calc
    _ = ⁅rootElement r m, rootElement (right r) n⁆ * rootElement (right r) n := by
      simp only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one]
    _ = _ := by rw [rootElement_commutator]

theorem rootElements_generate : Subgroup.closure (Set.range of) = ⊤ := by
  apply top_unique
  intro x _
  exact PresentedGroup.generated_by relators (Subgroup.closure (Set.range of))
    (fun r => Subgroup.subset_closure (Set.mem_range_self r)) x

end ThomGame.IntegralShear
