module

public import ThomGame.Groups.CosetReversal
public import Mathlib.GroupTheory.Perm.Basic

/-!
# A faithful permutation model for the squared-pair substitution

On G × Bool, use the right regular representation x ↦ x g⁻¹ on the first
coordinate. For each g commuting with an involution j, reversing the
coordinate in a coset of ⟨g,j⟩ supplies two involutions whose product squared
is the regular image of g. Both commute with the regular image of j.
-/

@[expose] public section
namespace ThomGame.InvolutionPermutation

variable {G : Type*} [Group G]

def regularPerm (g : G) : Equiv.Perm (G × Bool) where
  toFun p := (p.1 * g⁻¹, p.2)
  invFun p := (p.1 * g, p.2)
  left_inv p := by simp
  right_inv p := by simp

def regular : G →* Equiv.Perm (G × Bool) where
  toFun := regularPerm
  map_one' := by ext p <;> simp [regularPerm]
  map_mul' g h := by ext p <;> simp [regularPerm, mul_inv_rev, mul_assoc]

theorem regular_apply (g : G) (x : G) (b : Bool) : regular g (x, b) = (x * g⁻¹, b) := rfl

theorem regular_injective : Function.Injective (regular : G →* Equiv.Perm (G × Bool)) := by
  intro g h heq
  have hp := congrArg (fun p : Equiv.Perm (G × Bool) => (p (1, false)).1) heq
  simpa [regular, regularPerm] using congrArg Inv.inv hp

structure Reversal (g j : G) where
  toFun : G → G
  involutive : Function.Involutive toFun
  mul_g : ∀ x, toFun (x * g) = toFun x * g⁻¹
  mul_j_inv : ∀ x, toFun (x * j⁻¹) = toFun x * j⁻¹

noncomputable def reversal (g j : G) (hgj : Commute g j) (hj : j * j = 1) : Reversal g j := by
  let H := Subgroup.closure ({g, j} : Set G)
  have hcomm : ({g, j} : Set G).Pairwise Commute := by
    intro a ha b hb hab
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (hab rfl).elim
    · exact hgj
    · exact hgj.symm
    · exact (hab rfl).elim
  letI : IsMulCommutative H := Subgroup.isMulCommutative_closure hcomm
  have hg : g ∈ H := Subgroup.subset_closure (by simp)
  have hjmem : j ∈ H := Subgroup.subset_closure (by simp)
  refine ⟨CosetReversal.reverse H, CosetReversal.reverse_reverse H,
    (fun x => CosetReversal.reverse_mul H x g hg), ?_⟩
  intro x
  have hji : j⁻¹ = j := inv_eq_of_mul_eq_one_left hj
  simpa only [inv_inv, hji] using CosetReversal.reverse_mul H x j⁻¹ (H.inv_mem hjmem)

namespace Reversal

variable {g j : G} (r : Reversal g j)

theorem toFun_toFun (x : G) : r.toFun (r.toFun x) = x := r.involutive x

def flip (p : G × Bool) : G × Bool := (r.toFun p.1, !p.2)

def twist : G × Bool → G × Bool
  | (x, false) => (r.toFun x, false)
  | (x, true) => (r.toFun x * g, true)

theorem flip_involutive : Function.Involutive r.flip := by
  rintro ⟨x, b⟩
  simp [flip, r.involutive x]

theorem twist_involutive : Function.Involutive r.twist := by
  rintro ⟨x, b⟩
  cases b <;> simp [twist, r.mul_g, r.involutive x]

def u : Equiv.Perm (G × Bool) where
  toFun := r.flip
  invFun := r.flip
  left_inv := r.flip_involutive
  right_inv := r.flip_involutive

def v : Equiv.Perm (G × Bool) where
  toFun := r.twist
  invFun := r.twist
  left_inv := r.twist_involutive
  right_inv := r.twist_involutive

theorem u_square : r.u * r.u = 1 := by
  exact Equiv.ext r.flip_involutive

theorem v_square : r.v * r.v = 1 := by
  exact Equiv.ext r.twist_involutive

theorem pair_square : (r.u * r.v) ^ 2 = regular g := by
  apply Equiv.ext
  rintro ⟨x, b⟩
  change r.flip (r.twist (r.flip (r.twist (x, b)))) = (x * g⁻¹, b)
  cases b <;> simp [flip, twist, r.toFun_toFun, r.mul_g]

theorem u_commutes : Commute (regular j) r.u := by
  change regular j * r.u = r.u * regular j
  apply Equiv.ext
  rintro ⟨x, b⟩
  change (r.toFun x * j⁻¹, !b) = (r.toFun (x * j⁻¹), !b)
  rw [r.mul_j_inv]

theorem v_commutes (hgj : Commute g j) : Commute (regular j) r.v := by
  change regular j * r.v = r.v * regular j
  apply Equiv.ext
  rintro ⟨x, b⟩
  change ((r.twist (x, b)).1 * j⁻¹, (r.twist (x, b)).2) = r.twist (x * j⁻¹, b)
  cases b <;> simp [twist, r.mul_j_inv, mul_assoc,
    (hgj.inv_right).eq]

end Reversal
end ThomGame.InvolutionPermutation
