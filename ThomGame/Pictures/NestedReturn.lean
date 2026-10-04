module

public import ThomGame.Pictures.ReturnPathOperations

/-!
# Nested first returns

Returning first to `p` and then to `q` returns to the same point as
returning directly to their intersection. Every intermediate point is
accounted for by the genuine return-path expansion.
-/

@[expose] public section
namespace ThomGame.Pictures.MarkedReturn

variable {A : Type*} [Finite A] (f : Equiv.Perm A) (p q : A → Prop)

theorem perm_nested (x : {a : Subtype p // q a.val}) :
    (perm (perm f p) (fun a : Subtype p => q a.val) x).val.val =
      (perm f (fun a => p a ∧ q a) ⟨x.val.val, x.val.property, x.property⟩).val := by
  exact perm_preserved_of_paths f (fun a => p a ∧ q a) (perm f p)
    (fun a : Subtype p => q a.val) Subtype.val
    (fun a => (hit_perm f p a).weaken (fun _ h => h.1))
    (fun a => ⟨And.right, fun h => ⟨a.property, h⟩⟩) x

theorem perm_eq_of_pred_iff (hpq : ∀ a, p a ↔ q a) (x : Subtype p) :
    (perm f p x).val = (perm f q ⟨x.val, (hpq x.val).mp x.property⟩).val :=
  eq_perm_of_hit f q _ ((hpq _).mp (perm f p x).property)
    ((hit_perm f p x).weaken (fun a h => (hpq a).mpr h))

end ThomGame.Pictures.MarkedReturn
