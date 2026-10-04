module

public import ThomGame.Pictures.GraphEdges

/-! # Invariant port predicates select actual edges and transport exactly -/

@[expose] public section
namespace ThomGame.Pictures.Pairing

variable {A B S T : Type*} {label : A → S} {label' : B → T}
  (p : Pairing label) (q : Pairing label')

/-- Select an actual edge by a predicate on its ports. -/
def EdgePred (M : A → Prop) (c : p.Edge) : Prop := ∃ x, p.edge x = c ∧ M x

theorem edgePred_edge_iff (M : A → Prop) (hM : ∀ x, M (p.twin x) ↔ M x) (x : A) :
    p.EdgePred M (p.edge x) ↔ M x := by
  constructor
  · rintro ⟨y, hy, hMy⟩
    rcases (p.edge_eq_iff y x).mp hy with rfl | hy
    · exact hMy
    · exact (hM x).mp (hy ▸ hMy)
  · exact fun hx => ⟨x, rfl, hx⟩

def edgeCongr (e : A ≃ B) (hp : ∀ x, q.twin (e x) = e (p.twin x)) : p.Edge ≃ q.Edge :=
  Quotient.congr e (by
    intro x y
    change (x = y ∨ x = p.twin y) ↔ (e x = e y ∨ e x = q.twin (e y))
    rw [hp y, e.injective.eq_iff, e.injective.eq_iff])

theorem edgeCongr_apply (e : A ≃ B) (hp : ∀ x, q.twin (e x) = e (p.twin x)) (x : A) :
    p.edgeCongr q e hp (p.edge x) = q.edge (e x) := rfl

def edgeSubsetEquiv (e : A ≃ B) (hp : ∀ x, q.twin (e x) = e (p.twin x))
    (M : A → Prop) (N : B → Prop) (hMN : ∀ x, M x ↔ N (e x)) :
    {c : p.Edge // p.EdgePred M c} ≃ {c : q.Edge // q.EdgePred N c} :=
  (p.edgeCongr q e hp).subtypeEquiv (by
    intro c
    constructor
    · rintro ⟨x, hx, hMx⟩
      exact ⟨e x, (p.edgeCongr_apply q e hp x).symm.trans (congrArg (p.edgeCongr q e hp) hx),
        (hMN x).mp hMx⟩
    · rintro ⟨y, hy, hNy⟩
      obtain ⟨x, rfl⟩ := e.surjective y
      exact ⟨x, (p.edgeCongr q e hp).injective ((p.edgeCongr_apply q e hp x).trans hy),
        (hMN x).mpr hNy⟩)

theorem edge_subset_card (e : A ≃ B) (hp : ∀ x, q.twin (e x) = e (p.twin x))
    (M : A → Prop) (N : B → Prop) (hMN : ∀ x, M x ↔ N (e x)) :
    Nat.card {c : p.Edge // p.EdgePred M c} = Nat.card {c : q.Edge // q.EdgePred N c} :=
  Nat.card_congr (p.edgeSubsetEquiv q e hp M N hMN)

end ThomGame.Pictures.Pairing
