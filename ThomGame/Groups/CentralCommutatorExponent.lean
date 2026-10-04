module

public import ThomGame.Groups.CentralCommutatorGenerators
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.PGroup

/-! Exponent and nilpotency bounds derived from the actual generators. -/

@[expose] public section
namespace ThomGame

open scoped commutatorElement IsMulCommutative

variable {G : Type*} [Group G]

theorem generatorCommutatorSubgroup_pow {S : Set G} (hgen : Subgroup.closure S = ⊤)
    (htriple : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, Commute ⁅x, y⁆ z)
    (p : Nat) (hpow : ∀ x ∈ S, x ^ p = 1)
    (z : G) (hz : z ∈ generatorCommutatorSubgroup S) : z ^ p = 1 := by
  have hC := generatorCommutatorSubgroup_le_center hgen htriple
  refine commutingClosure_pow ?_ p ?_ z hz
  · intro x hx y _ _
    exact (Subgroup.mem_center_iff.mp (hC (Subgroup.subset_closure hx)) y).symm
  · rintro _ ⟨⟨x, y⟩, rfl⟩
    rw [(htriple x.val x.property y.val y.property x.val x.property).symm.commutatorElement_pow_left,
      hpow x.val x.property, commutatorElement_one_left]

theorem pow_square_of_central_commutator_generators {S : Set G} (hgen : Subgroup.closure S = ⊤)
    (htriple : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, Commute ⁅x, y⁆ z)
    (p : Nat) (hpow : ∀ x ∈ S, x ^ p = 1) (g : G) : g ^ (p * p) = 1 := by
  let N := generatorCommutatorSubgroup S
  let : N.Normal := Subgroup.normal_of_le_center (generatorCommutatorSubgroup_le_center hgen htriple)
  let : IsMulCommutative (G ⧸ N) := quotient_commutes_of_generator_commutators hgen N
    (fun x hx y hy => Subgroup.subset_closure ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩)
  have hq : ((QuotientGroup.mk' N) g) ^ p = 1 := by
    apply commutingClosure_pow (S := (QuotientGroup.mk' N) '' S)
      (fun _ _ _ _ _ => Commute.all _ _) p
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hpow x hx, map_one]
    · rw [quotient_generators_generate hgen N]
      trivial
  have hg : g ^ p ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    simpa only [QuotientGroup.mk'_apply, QuotientGroup.mk_pow] using hq
  rw [pow_mul]
  exact generatorCommutatorSubgroup_pow hgen htriple p hpow (g ^ p) hg

theorem isPGroup_of_central_commutator_generators {S : Set G} (hgen : Subgroup.closure S = ⊤)
    (htriple : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, Commute ⁅x, y⁆ z)
    (p : Nat) (hpow : ∀ x ∈ S, x ^ p = 1) : IsPGroup p G := by
  apply isPGroup_iff_pow_pow_eq_one.mpr
  intro g
  exact ⟨2, by simpa only [pow_two] using pow_square_of_central_commutator_generators hgen htriple p hpow g⟩

theorem upperCentralSeries_two_of_commutator_le_center
    (hC : _root_.commutator G ≤ Subgroup.center G) : Subgroup.upperCentralSeries G 2 = ⊤ := by
  apply top_unique
  intro x _
  change ∀ y, ⁅x, y⁆ ∈ Subgroup.upperCentralSeries G 1
  rw [Subgroup.upperCentralSeries_one]
  intro y
  exact hC (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))

theorem nilpotent_of_commutator_le_center (hC : _root_.commutator G ≤ Subgroup.center G) : Group.IsNilpotent G :=
  ⟨⟨2, upperCentralSeries_two_of_commutator_le_center hC⟩⟩

theorem nilpotencyClass_le_two_of_commutator_le_center (hC : _root_.commutator G ≤ Subgroup.center G) :
    Group.nilpotencyClass G ≤ 2 := by
  let : Group.IsNilpotent G := nilpotent_of_commutator_le_center hC
  exact Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le.mp (upperCentralSeries_two_of_commutator_le_center hC)

theorem prime_le_index_of_proper {p : Nat} [Fact p.Prime] [Finite G]
    (hG : IsPGroup p G) (H : Subgroup G) (hH : H ≠ ⊤) : p ≤ H.index := by
  obtain ⟨k, hk⟩ := hG.index H
  have hkpos : 0 < k := by
    by_contra hk0
    have hkzero : k = 0 := Nat.eq_zero_of_not_pos hk0
    exact hH (Subgroup.index_eq_one.mp (by simpa only [hkzero, pow_zero] using hk))
  rw [hk]
  exact Nat.le_pow hkpos

end ThomGame
