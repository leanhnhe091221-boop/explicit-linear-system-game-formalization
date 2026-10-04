module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Group.Commute.Basic

/-! Integer powers of a commutator which commutes with both factors. -/

@[expose] public section
namespace ThomGame

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem centralCommutator_inv_left {a b : G} (h : Commute a ⁅a, b⁆) :
    ⁅a⁻¹, b⁆ = ⁅a, b⁆⁻¹ := by
  rw [commutatorElement_inv_left, ← commutatorElement_inv,
    (h.inv_left.inv_right).eq, inv_mul_cancel_right]

theorem centralCommutator_zpow_left {a b : G} (h : Commute a ⁅a, b⁆) (m : ℤ) :
    ⁅a ^ m, b⁆ = ⁅a, b⁆ ^ m := by
  cases m with
  | ofNat n =>
      change ⁅a ^ (n : ℤ), b⁆ = ⁅a, b⁆ ^ (n : ℤ)
      simpa only [zpow_natCast] using (h.commutatorElement_pow_left n).symm
  | negSucc n =>
      simp only [zpow_negSucc]
      have hn : Commute (a ^ (n + 1)) ⁅a ^ (n + 1), b⁆ := by
        rw [← h.commutatorElement_pow_left]
        exact h.pow_pow _ _
      rw [centralCommutator_inv_left hn, ← h.commutatorElement_pow_left]

theorem centralCommutator_zpow_right {a b : G} (h : Commute b ⁅a, b⁆) (m : ℤ) :
    ⁅a, b ^ m⁆ = ⁅a, b⁆ ^ m := by
  have hs : Commute b ⁅b, a⁆ := by
    rw [← commutatorElement_inv]
    exact h.inv_right
  have hz := centralCommutator_zpow_left hs m
  have hi := congrArg Inv.inv hz
  simpa only [← inv_zpow, commutatorElement_inv] using hi

theorem centralCommutator_zpow_zpow {a b : G}
    (ha : Commute a ⁅a, b⁆) (hb : Commute b ⁅a, b⁆) (m n : ℤ) :
    ⁅a ^ m, b ^ n⁆ = ⁅a, b⁆ ^ (m * n) := by
  have hb' : Commute b ⁅a ^ m, b⁆ := by
    rw [centralCommutator_zpow_left ha]
    exact hb.zpow_right m
  rw [centralCommutator_zpow_right hb', centralCommutator_zpow_left ha, zpow_mul]

end ThomGame
