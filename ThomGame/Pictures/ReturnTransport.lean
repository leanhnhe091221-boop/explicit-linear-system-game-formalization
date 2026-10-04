module

public import ThomGame.Pictures.NestedReturn

/-! # First-return equivalences and flattening nested retained subsets -/

@[expose] public section
namespace ThomGame.Pictures.MarkedReturn

variable {A B : Type*} [Finite A] [Finite B]

theorem perm_subtypeEquiv (f : Equiv.Perm A) (g : Equiv.Perm B) (e : A ≃ B)
    (he : ∀ x, g (e x) = e (f x)) (p : A → Prop) (q : B → Prop)
    (hp : ∀ x, p x ↔ q (e x)) (x : Subtype p) :
    perm g q (e.subtypeEquiv hp x) = e.subtypeEquiv hp (perm f p x) := by
  apply Subtype.ext
  exact (perm_preserved_of_commutes g q f p e he (fun x => (hp x).symm) x).symm

omit [Finite A] [Finite B] in
def nestedSubset (p q : A → Prop) (hqp : ∀ x, q x → p x) :
    {x : Subtype p // q x.val} ≃ Subtype q where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, hqp x.val x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem perm_nested_subset (f : Equiv.Perm A) (p q : A → Prop) (hqp : ∀ x, q x → p x)
    (x : {x : Subtype p // q x.val}) :
    perm f q (nestedSubset p q hqp x) =
      nestedSubset p q hqp (perm (perm f p) (fun x : Subtype p => q x.val) x) := by
  apply Subtype.ext
  exact ((perm_nested f p q x).trans
    (perm_eq_of_pred_iff f (fun x => p x ∧ q x) q
      (fun x => ⟨And.right, fun hx => ⟨hqp x hx, hx⟩⟩)
      ⟨x.val.val, x.val.property, x.property⟩)).symm

end ThomGame.Pictures.MarkedReturn
