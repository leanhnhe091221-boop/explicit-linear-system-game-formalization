module

public import ThomGame.Pictures.EdgeDeletionEuler
public import ThomGame.Pictures.ConnectedResidualMatching

/-!
# Euler saturation on invariant subsets

An invariant set and its complement split all vertex, edge, face and
component orbits. Both pieces obey the universal Euler upper bound, so
equality for their union forces equality on each piece.
-/

@[expose] public section
namespace ThomGame.Pictures.RotationEuler

open Equiv FiniteReturn RibbonConnectivity

section Sum

variable {A B : Type*} [Finite A] [Finite B]

theorem count_sum (r t : Perm A) (r' t' : Perm B) :
    count (Equiv.sumCongr r r') (Equiv.sumCongr t t') = count r t + count r' t' := by
  have hm : Equiv.sumCongr t t' * Equiv.sumCongr r r' =
      Equiv.sumCongr (t * r) (t' * r') := by
    ext a
    cases a <;> rfl
  unfold count
  rw [hm, orbit_card_sum, orbit_card_sum, orbit_card_sum, Nat.card_sum]
  push_cast
  omega

end Sum

variable {D : Type*} [Finite D] (r t : Perm D) (M : D → Prop)
    (hr : ∀ x, M (r x) ↔ M x) (ht : ∀ x, M (t x) ↔ M x)

theorem subtype_saturated (hi : Function.Involutive t)
    (hEuler : count r t = 2 * Nat.card (Component r t)) :
    count (r.subtypePerm hr) (t.subtypePerm ht) =
      2 * Nat.card (Component (r.subtypePerm hr) (t.subtypePerm ht)) := by
  classical
  let r' := r.subtypePerm (p := fun x => ¬ M x) (fun x => (hr x).not)
  let t' := t.subtypePerm (p := fun x => ¬ M x) (fun x => (ht x).not)
  let rs := Equiv.sumCongr (r.subtypePerm hr) r'
  let ts := Equiv.sumCongr (t.subtypePerm ht) t'
  have hrv : ∀ x, r (Equiv.sumCompl M x) = Equiv.sumCompl M (rs x) := by
    rintro (x | x) <;> rfl
  have htv : ∀ x, t (Equiv.sumCompl M x) = Equiv.sumCompl M (ts x) := by
    rintro (x | x) <;> rfl
  have he := count_congr rs ts r t (Equiv.sumCompl M) hrv htv
  have hc := Nat.card_congr (componentCongrEquiv rs ts r t (Equiv.sumCompl M) hrv htv)
  change count (Equiv.sumCongr (r.subtypePerm hr) r') (Equiv.sumCongr (t.subtypePerm ht) t') = _ at he
  rw [count_sum] at he
  change Nat.card (Component (Equiv.sumCongr (r.subtypePerm hr) r')
    (Equiv.sumCongr (t.subtypePerm ht) t')) = _ at hc
  rw [component_card_sum] at hc
  have hiM : Function.Involutive (t.subtypePerm ht) := fun x => Subtype.ext (hi x.val)
  have hiN : Function.Involutive t' := fun x => Subtype.ext (hi x.val)
  have hbM := count_le_twice_components (r.subtypePerm hr) (t.subtypePerm ht) hiM
  have hbN := count_le_twice_components r' t' hiN
  omega

end ThomGame.Pictures.RotationEuler
