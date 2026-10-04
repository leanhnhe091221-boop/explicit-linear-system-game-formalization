module

public import ThomGame.Pictures.OrbitEnumeration
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.BigOperators

/-!
# Equal fibers of a finite map intertwining cyclic permutations

Powers of the actual source permutation give bijections of the fibers.
If the target permutation is transitive, every fiber has the same
positive size. Noninjectivity then gives two distinct points over any
specified target, not merely over some unspecified target.
-/

@[expose] public section
namespace ThomGame.Pictures.PermutationCover

open Equiv
open scoped Classical BigOperators

variable {A B : Type*} (f : Perm A) (g : Perm B) (π : A → B)
  (hπ : Function.Semiconj π f g)

include hπ in
theorem map_pow (k : Nat) (a : A) : π ((f ^ k) a) = (g ^ k) (π a) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Perm.mul_apply, hπ, ih, pow_succ', Perm.mul_apply]

noncomputable def fiberEquivOfPow (b c : B) (k : Nat) (hk : (g ^ k) b = c) :
    {a : A // π a = b} ≃ {a : A // π a = c} :=
  Equiv.ofBijective (fun a => ⟨(f ^ k) a.val,
    (map_pow f g π hπ k a.val).trans ((congrArg (g ^ k) a.property).trans hk)⟩) ⟨by
      intro a a' he
      exact Subtype.ext ((f ^ k).injective (congrArg Subtype.val he)), by
      intro a
      let x := (f ^ k).symm a.val
      have hx : π x = b := (g ^ k).injective
        ((map_pow f g π hπ k x).symm.trans
          ((congrArg π ((f ^ k).apply_symm_apply a.val)).trans (a.property.trans hk.symm)))
      exact ⟨⟨x, hx⟩, Subtype.ext ((f ^ k).apply_symm_apply a.val)⟩⟩

variable [Finite B]

noncomputable def fiberEquiv (b c : B) (hc : g.SameCycle b c) :
    {a : A // π a = b} ≃ {a : A // π a = c} :=
  fiberEquivOfPow f g π hπ b c hc.exists_nat_pow_eq.choose hc.exists_nat_pow_eq.choose_spec

variable (hg : ∀ b c : B, g.SameCycle b c)

include hπ hg in
theorem surjective (a₀ : A) : Function.Surjective π := by
  intro b
  let x := fiberEquiv f g π hπ (π a₀) b (hg _ _) ⟨a₀, rfl⟩
  exact ⟨x.val, x.property⟩

include hπ hg in
theorem repeated_over_every_target (hn : ¬ Function.Injective π) (b : B) :
    ∃ x y : A, x ≠ y ∧ π x = b ∧ π y = b := by
  change ¬ ∀ x y, π x = π y → x = y at hn
  obtain ⟨x, hx⟩ := not_forall.mp hn
  obtain ⟨y, hxy⟩ := not_forall.mp hx
  obtain ⟨he, hne⟩ := not_imp.mp hxy
  let e := fiberEquiv f g π hπ (π x) b (hg _ _)
  let u := e ⟨x, rfl⟩
  let v := e ⟨y, he.symm⟩
  refine ⟨u.val, v.val, ?_, u.property, v.property⟩
  intro huv
  exact hne (congrArg Subtype.val (e.injective (Subtype.ext huv)))

variable [Fintype A]

include hπ hg in
theorem fiber_card (b c : B) : Fintype.card {a : A // π a = b} = Fintype.card {a : A // π a = c} :=
  Fintype.card_congr (fiberEquiv f g π hπ b c (hg b c))

include hπ hg in
theorem fiber_card_pos (a₀ : A) (b : B) : 0 < Fintype.card {a : A // π a = b} := by
  obtain ⟨a, ha⟩ := surjective f g π hπ hg a₀ b
  exact Fintype.card_pos_iff.mpr ⟨⟨a, ha⟩⟩

include hπ hg in
theorem card_eq_mul_fiber [Fintype B] (b : B) : Fintype.card A = Fintype.card B * Fintype.card {a : A // π a = b} := by
  calc
    Fintype.card A = Fintype.card ((c : B) × {a : A // π a = c}) :=
      (Fintype.card_congr (Equiv.sigmaFiberEquiv π)).symm
    _ = ∑ c : B, Fintype.card {a : A // π a = c} := Fintype.card_sigma
    _ = ∑ _ : B, Fintype.card {a : A // π a = b} :=
      Finset.sum_congr rfl (fun c _ => fiber_card f g π hπ hg c b)
    _ = Fintype.card B * Fintype.card {a : A // π a = b} := by simp

end ThomGame.Pictures.PermutationCover
