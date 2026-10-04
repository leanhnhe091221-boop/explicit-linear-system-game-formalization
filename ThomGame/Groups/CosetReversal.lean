module

public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.Group

/-!
# Reversing the subgroup coordinate of a coset

Choose one representative t of each left coset of H. The map t h ↦ t h⁻¹
is an involution of G. If H is abelian, it reverses right multiplication by
every element of H. This construction will supply the reflections used to
represent the substitution g ↦ (u_g v_g)^2 faithfully.
-/

@[expose] public section
namespace ThomGame.CosetReversal

variable {G : Type*} [Group G] (H : Subgroup G)

noncomputable def representative (x : G) : G := (QuotientGroup.mk x : G ⧸ H).out

theorem representative_coset (x : G) :
    (QuotientGroup.mk (representative H x) : G ⧸ H) = QuotientGroup.mk x :=
  Quotient.out_eq' _

theorem inv_mul_representative_mem (x : G) : x⁻¹ * representative H x ∈ H :=
  QuotientGroup.eq.mp (representative_coset H x).symm

theorem representative_mul (x h : G) (hh : h ∈ H) :
    representative H (x * h) = representative H x := by
  unfold representative
  rw [QuotientGroup.mk_mul_of_mem x hh]

noncomputable def reverse (x : G) : G := representative H x * x⁻¹ * representative H x

theorem representative_reverse (x : G) : representative H (reverse H x) = representative H x := by
  have h : (QuotientGroup.mk (reverse H x) : G ⧸ H) = QuotientGroup.mk x := by
    rw [reverse, mul_assoc, QuotientGroup.mk_mul_of_mem _ (inv_mul_representative_mem H x)]
    exact representative_coset H x
  exact congrArg Quotient.out h

theorem reverse_reverse (x : G) : reverse H (reverse H x) = x := by
  change representative H (reverse H x) * (reverse H x)⁻¹ *
    representative H (reverse H x) = x
  rw [representative_reverse]
  unfold reverse
  group

/-- This is a permutation for every subgroup, whether or not H is abelian. -/
noncomputable def equiv : Equiv.Perm G where
  toFun := reverse H
  invFun := reverse H
  left_inv := reverse_reverse H
  right_inv := reverse_reverse H

theorem reverse_mul [IsMulCommutative H] (x h : G) (hh : h ∈ H) :
    reverse H (x * h) = reverse H x * h⁻¹ := by
  have hcomm : h⁻¹ * (x⁻¹ * representative H x) = (x⁻¹ * representative H x) * h⁻¹ :=
    setLike_mul_comm (H.inv_mem hh) (inv_mul_representative_mem H x)
  simp only [reverse, representative_mul H x h hh, mul_inv_rev]
  simp only [mul_assoc] at hcomm ⊢
  rw [hcomm]

end ThomGame.CosetReversal
