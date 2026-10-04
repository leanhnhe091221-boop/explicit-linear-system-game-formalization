module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.FiniteAbelian.Basic

/-! Finite commuting torsion generators give an actual finite subgroup. -/

@[expose] public section
namespace ThomGame

open scoped IsMulCommutative

theorem commutingClosure_pow {G : Type*} [Group G] {S : Set G}
    (hcomm : S.Pairwise Commute) (p : Nat) (hpow : ∀ x ∈ S, x ^ p = 1)
    (x : G) (hx : x ∈ Subgroup.closure S) : x ^ p = 1 := by
  let : IsMulCommutative (Subgroup.closure S) := Subgroup.isMulCommutative_closure hcomm
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hpow x hx
  | one => exact one_pow p
  | mul x y hx hy ihx ihy =>
      have hxy : Commute x y := congrArg Subtype.val
        (mul_comm (⟨x, hx⟩ : Subgroup.closure S) (⟨y, hy⟩ : Subgroup.closure S))
      rw [hxy.mul_pow, ihx, ihy, one_mul]
  | inv x hx ih => rw [inv_pow, ih, inv_one]

theorem commutingClosure_finite {G : Type*} [Group G] {S : Set G}
    (hS : S.Finite) (hcomm : S.Pairwise Commute) (p : Nat) (hp : 0 < p)
    (hpow : ∀ x ∈ S, x ^ p = 1) : Finite (Subgroup.closure S) := by
  let : Finite S := hS.to_subtype
  let : IsMulCommutative (Subgroup.closure S) := Subgroup.isMulCommutative_closure hcomm
  exact CommGroup.finite_of_fg_isMulTorsion (Subgroup.closure S) (fun x =>
    isOfFinOrder_iff_pow_eq_one.mpr ⟨p, hp, Subtype.ext (commutingClosure_pow hcomm p hpow x.val x.property)⟩)

theorem finite_of_commuting_generators {G : Type*} [Group G] {S : Set G}
    (hS : S.Finite) (hgen : Subgroup.closure S = ⊤) (hcomm : S.Pairwise Commute)
    (p : Nat) (hp : 0 < p) (hpow : ∀ x ∈ S, x ^ p = 1) : Finite G := by
  have hf := commutingClosure_finite hS hcomm p hp hpow
  rw [hgen] at hf
  let : Finite (⊤ : Subgroup G) := hf
  exact Finite.of_equiv (⊤ : Subgroup G) Subgroup.topEquiv.toEquiv

end ThomGame
