module

public import ThomGame.Pictures.GraphEdges

/-! # Explicitly orienting the two ports of each pair in a finite matching -/

@[expose] public section
namespace ThomGame.Pictures.Pairing

variable {m : Nat} {S : Type*} {label : Fin m → S} (p : Pairing label)

abbrev OrderedEdge := {k : Fin m // k < p.twin k}

def orderedPort (x : p.OrderedEdge × Bool) : Fin m :=
  if x.2 then p.twin x.1.val else x.1.val

theorem orderedPort_injective : Function.Injective p.orderedPort := by
  rintro ⟨a, s⟩ ⟨b, t⟩ he
  cases s <;> cases t
  · exact Prod.ext (Subtype.ext he) rfl
  · change a.val = p.twin b.val at he
    have ha := a.property
    rw [he, p.involutive] at ha
    exact (lt_asymm ha b.property).elim
  · change p.twin a.val = b.val at he
    have hb := b.property
    rw [← he, p.involutive] at hb
    exact (lt_asymm a.property hb).elim
  · exact Prod.ext (Subtype.ext (p.involutive.injective he)) rfl

theorem orderedPort_surjective : Function.Surjective p.orderedPort := by
  intro k
  by_cases hk : k < p.twin k
  · exact ⟨(⟨k, hk⟩, false), rfl⟩
  · have hp : p.twin k < k := lt_of_le_of_ne (le_of_not_gt hk) (p.ne_self k)
    refine ⟨(⟨p.twin k, ?_⟩, true), p.involutive k⟩
    rwa [p.involutive]

noncomputable def orderedPorts : p.OrderedEdge × Bool ≃ Fin m :=
  Equiv.ofBijective p.orderedPort ⟨p.orderedPort_injective, p.orderedPort_surjective⟩

theorem orderedPort_twin (j : p.OrderedEdge) (side : Bool) :
    p.twin (p.orderedPorts (j, side)) = p.orderedPorts (j, !side) := by
  cases side
  · rfl
  · exact p.involutive j.val

theorem orderedPort_label (j : p.OrderedEdge) (side : Bool) :
    label (p.orderedPorts (j, side)) = label j.val := by
  cases side
  · rfl
  · exact p.label_twin j.val

theorem card_ordered_edges : m = 2 * Fintype.card p.OrderedEdge := by
  simpa only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, Nat.mul_comm] using
    (Fintype.card_congr p.orderedPorts).symm

end ThomGame.Pictures.Pairing
