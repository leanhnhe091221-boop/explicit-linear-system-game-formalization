module

public import ThomGame.Pictures.RestrictedConnectivity

/-! # Forward closure and fixed-edge components of finite permutations -/

@[expose] public section
namespace ThomGame.Pictures.RibbonConnectivity

open Equiv

variable {A : Type*} [Finite A]

theorem predicate_of_sameCycle (p : Perm A) (M : A → Prop)
    (hp : ∀ x, M x → M (p x)) {x y : A} (h : p.SameCycle x y) (hx : M x) : M y := by
  obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction k with
  | zero => exact hx
  | succ k ih =>
    rw [pow_succ', Perm.mul_apply]
    exact hp _ ih

theorem predicate_apply_iff_of_forward (p : Perm A) (M : A → Prop)
    (hp : ∀ x, M x → M (p x)) (x : A) : M (p x) ↔ M x :=
  ⟨fun hx => predicate_of_sameCycle p M hp (Perm.SameCycle.rfl.apply_left) hx, hp x⟩

namespace Connected

theorem predicate_of_forward {p f : Perm A} (M : A → Prop)
    (hp : ∀ x, M x → M (p x)) (hf : ∀ x, M x → M (f x))
    {x y : A} (h : Connected p f x y) (hx : M x) : M y := by
  have he := h.invariant M
    (fun x => propext (predicate_apply_iff_of_forward p M hp x))
    (fun x => propext (predicate_apply_iff_of_forward f M hf x))
  exact he ▸ hx

omit [Finite A] in
theorem sameCycle_of_fixed_on_component {p f : Perm A} {x y : A}
    (h : Connected p f x y) (hf : ∀ z, Connected p f x z → f z = z) : p.SameCycle x y := by
  let M := fun z => Connected p f x z
  have hpM (z : A) : M (p z) ↔ M z :=
    ⟨fun hz => hz.trans (Connected.edge z).symm, fun hz => hz.trans (Connected.edge z)⟩
  have hfM (z : A) : M (f z) ↔ M z :=
    ⟨fun hz => hz.trans (Connected.circuit z).symm, fun hz => hz.trans (Connected.circuit z)⟩
  apply h.lift_restricted M hpM hfM (Connected.refl x) h Subtype.val (Perm.SameCycle.equivalence p)
  · intro z
    exact Perm.SameCycle.rfl.apply_right
  · intro z
    change p.SameCycle z.val (f z.val)
    rw [hf z.val z.property]

end Connected
end ThomGame.Pictures.RibbonConnectivity
