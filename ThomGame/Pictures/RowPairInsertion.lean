module

public import ThomGame.Pictures.SolutionGraph
public import ThomGame.Pictures.GraphCharge
public import ThomGame.Pictures.PairingSurgery

/-!
# Inserting a pair of row vertices between two differently labelled edges

This is the underlying graph operation of Figure 19(b). Two old edges,
labelled by slots 1 and 2 of one row, are cut. Their chosen ends attach to
one new copy of that row, and their partners to a second copy. Slot 0
joins the new vertices. The vertices have opposite orientations.

Only the actual input ports and their labels are data. The pairing,
cardinality, character and sign assertions are proved from this data;
planarity and the facial-copy assertion are separate tasks.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv
open scoped Classical BigOperators

variable {R S : Type*} {A : SparseSystem R S} {u v : List S}
  (G : SolutionGroup.RowGraph A u v)

structure RowPairInsertion where
  row : R
  first : G.Dart
  second : G.Dart
  first_label : Port.label G.jointLabel first = A.column row 1
  second_label : Port.label G.jointLabel second = A.column row 2

namespace RowPairInsertion

variable {G} (s : G.RowPairInsertion)

abbrev hubLabel : G.Hub ⊕ Bool → R := Sum.elim G.hubLabel (fun _ => s.row)

abbrev Dart := Port (SolutionGroup.triangularPresentation A) u v
  (G.Hub ⊕ Bool) G.Joint s.hubLabel

def old : G.Dart → s.Dart
  | .top i => .top i
  | .bottom i => .bottom i
  | .hub h i => .hub (.inl h) i
  | .joint j b => .joint j b

def fresh (b : Bool) (i : Fin 3) : s.Dart := .hub (.inr b) i

def ports : G.Dart ⊕ (Bool × Fin 3) ≃ s.Dart where
  toFun := Sum.elim s.old (fun x => s.fresh x.1 x.2)
  invFun
    | .top i => .inl (.top i)
    | .bottom i => .inl (.bottom i)
    | .hub (.inl h) i => .inl (.hub h i)
    | .hub (.inr b) i => .inr (b, i)
    | .joint j b => .inl (.joint j b)
  left_inv x := by
    rcases x with x | ⟨b, i⟩
    · cases x <;> rfl
    · rfl
  right_inv x := by
    cases x with
    | top _ => rfl
    | bottom _ => rfl
    | joint _ _ => rfl
    | hub h i => cases h <;> rfl

theorem old_injective : Function.Injective s.old :=
  fun _ _ h => Sum.inl.inj (s.ports.injective h)

theorem fresh_injective {b c : Bool} {i j : Fin 3} :
    s.fresh b i = s.fresh c j ↔ b = c ∧ i = j := by
  constructor
  · intro h
    exact Prod.mk.inj (Sum.inr.inj (s.ports.injective h))
  · rintro ⟨rfl, rfl⟩
    rfl

theorem old_ne_fresh (x : G.Dart) (b : Bool) (i : Fin 3) : s.old x ≠ s.fresh b i := by
  intro h
  have he : (Sum.inl x : G.Dart ⊕ (Bool × Fin 3)) = Sum.inr (b, i) := s.ports.injective h
  cases he

theorem old_label (x : G.Dart) : Port.label G.jointLabel (s.old x) = Port.label G.jointLabel x := by
  cases x <;> rfl

theorem fresh_label (b : Bool) (i : Fin 3) :
    Port.label G.jointLabel (s.fresh b i) = A.column s.row i := by
  fin_cases i <;> rfl

def thetaPairing : Pairing (fun x : Bool × Fin 3 => A.column s.row x.2) where
  twin x := (!x.1, x.2)
  involutive x := by rcases x with ⟨b, i⟩; cases b <;> rfl
  ne_self x := by rcases x with ⟨b, i⟩; cases b <;> simp
  label_twin _ := rfl

def basePairing : Pairing (Port.label (P := SolutionGroup.triangularPresentation A)
    (u := u) (v := v) (hubLabel := s.hubLabel) G.jointLabel) :=
  (G.pairing.sum s.thetaPairing).transport s.ports _ (by
    rintro (x | ⟨b, i⟩)
    · exact s.old_label x
    · exact s.fresh_label b i)

theorem base_twin_old (x : G.Dart) : s.basePairing.twin (s.old x) = s.old (G.pairing.twin x) := by
  cases x <;> rfl

theorem base_twin_fresh (b : Bool) (i : Fin 3) :
    s.basePairing.twin (s.fresh b i) = s.fresh (!b) i := rfl

theorem first_fresh_label :
    Port.label G.jointLabel (s.old s.first) = Port.label G.jointLabel (s.fresh false 1) :=
  (s.old_label _).trans (s.first_label.trans (s.fresh_label _ _).symm)

theorem second_fresh_label :
    Port.label G.jointLabel (s.old s.second) = Port.label G.jointLabel (s.fresh false 2) :=
  (s.old_label _).trans (s.second_label.trans (s.fresh_label _ _).symm)

noncomputable def firstPairing := s.basePairing.splice
  (s.old s.first) (s.fresh false 1) s.first_fresh_label

noncomputable def pairing := s.firstPairing.splice
  (s.old s.second) (s.fresh false 2) s.second_fresh_label

theorem labels_distinct : A.column s.row (1 : Fin 3) ≠ A.column s.row 2 := by
  intro h
  have hh := A.column_injective s.row h
  exact (by decide +kernel : (1 : Fin 3) ≠ 2) hh

theorem first_ne_second : s.first ≠ s.second := by
  intro h
  apply s.labels_distinct
  exact s.first_label.symm.trans ((congrArg (Port.label G.jointLabel) h).trans s.second_label)

theorem first_ne_twin_second : s.first ≠ G.pairing.twin s.second := by
  intro h
  apply s.labels_distinct
  rw [← s.first_label, h, G.pairing.label_twin, s.second_label]

theorem first_twin_old_second : s.firstPairing.twin (s.old s.second) = s.old (G.pairing.twin s.second) := by
  apply (s.basePairing.splice_twin_unchanged s.first_fresh_label ?_ ?_ ?_ ?_).trans (s.base_twin_old _)
  · exact fun h => s.first_ne_second (s.old_injective h).symm
  · exact s.old_ne_fresh _ _ _
  · rw [s.base_twin_old]
    intro h
    have hh := congrArg G.pairing.twin (s.old_injective h)
    rw [G.pairing.involutive] at hh
    exact s.first_ne_twin_second hh.symm
  · rw [s.base_twin_fresh]
    exact s.old_ne_fresh _ _ _

theorem first_twin_fresh_away (b : Bool) (i : Fin 3) (hi : i ≠ 1) :
    s.firstPairing.twin (s.fresh b i) = s.fresh (!b) i := by
  apply (s.basePairing.splice_twin_unchanged s.first_fresh_label ?_ ?_ ?_ ?_).trans (s.base_twin_fresh _ _)
  · exact (s.old_ne_fresh _ _ _).symm
  · exact fun h => hi (s.fresh_injective.mp h).2
  · rw [s.base_twin_old]
    exact (s.old_ne_fresh _ _ _).symm
  · rw [s.base_twin_fresh]
    exact fun h => hi (s.fresh_injective.mp h).2

theorem twin_first : s.pairing.twin (s.old s.first) = s.fresh false 1 := by
  apply (s.firstPairing.splice_twin_unchanged s.second_fresh_label ?_ ?_ ?_ ?_).trans
    (s.basePairing.splice_twin_left (s.old_ne_fresh _ _ _) s.first_fresh_label)
  · exact fun h => s.first_ne_second (s.old_injective h)
  · exact s.old_ne_fresh _ _ _
  · rw [s.first_twin_old_second]
    exact fun h => s.first_ne_twin_second (s.old_injective h)
  · rw [s.first_twin_fresh_away false 2 (by decide +kernel)]
    exact s.old_ne_fresh _ _ _

theorem twin_second : s.pairing.twin (s.old s.second) = s.fresh false 2 :=
  s.firstPairing.splice_twin_left (s.old_ne_fresh _ _ _) s.second_fresh_label

theorem twin_partner_first : s.pairing.twin (s.old (G.pairing.twin s.first)) = s.fresh true 1 := by
  have hbase := s.basePairing.splice_twin_partner_left (s.old_ne_fresh s.first false 1) s.first_fresh_label
  rw [s.base_twin_old, s.base_twin_fresh] at hbase
  apply (s.firstPairing.splice_twin_unchanged s.second_fresh_label ?_ ?_ ?_ ?_).trans hbase
  · intro h
    have hh := congrArg G.pairing.twin (s.old_injective h)
    rw [G.pairing.involutive] at hh
    exact s.first_ne_twin_second hh
  · exact s.old_ne_fresh _ _ _
  · rw [s.first_twin_old_second]
    exact fun h => s.first_ne_second (G.pairing.involutive.injective (s.old_injective h))
  · rw [s.first_twin_fresh_away false 2 (by decide +kernel)]
    exact s.old_ne_fresh _ _ _

theorem twin_partner_second : s.pairing.twin (s.old (G.pairing.twin s.second)) = s.fresh true 2 := by
  have h := s.firstPairing.splice_twin_partner_left (s.old_ne_fresh s.second false 2) s.second_fresh_label
  rw [s.first_twin_old_second, s.first_twin_fresh_away false 2 (by decide +kernel)] at h
  exact h

theorem twin_spoke (b : Bool) : s.pairing.twin (s.fresh b 0) = s.fresh (!b) 0 := by
  apply (s.firstPairing.splice_twin_unchanged s.second_fresh_label ?_ ?_ ?_ ?_).trans
    (s.first_twin_fresh_away b 0 (by decide +kernel))
  · exact (s.old_ne_fresh _ _ _).symm
  · exact fun h => (by decide +kernel : (0 : Fin 3) ≠ 2) (s.fresh_injective.mp h).2
  · rw [s.first_twin_old_second]
    exact (s.old_ne_fresh _ _ _).symm
  · rw [s.first_twin_fresh_away false 2 (by decide +kernel)]
    exact fun h => (by decide +kernel : (0 : Fin 3) ≠ 2) (s.fresh_injective.mp h).2

theorem twin_old_away (x : G.Dart) (ha : x ≠ s.first) (hb : x ≠ s.second)
    (hpa : x ≠ G.pairing.twin s.first) (hpb : x ≠ G.pairing.twin s.second) :
    s.pairing.twin (s.old x) = s.old (G.pairing.twin x) := by
  have hfirst : s.firstPairing.twin (s.old x) = s.old (G.pairing.twin x) := by
    apply (s.basePairing.splice_twin_unchanged s.first_fresh_label ?_ ?_ ?_ ?_).trans (s.base_twin_old x)
    · exact fun h => ha (s.old_injective h)
    · exact s.old_ne_fresh _ _ _
    · rw [s.base_twin_old]
      exact fun h => hpa (s.old_injective h)
    · rw [s.base_twin_fresh]
      exact s.old_ne_fresh _ _ _
  apply (s.firstPairing.splice_twin_unchanged s.second_fresh_label ?_ ?_ ?_ ?_).trans hfirst
  · exact fun h => hb (s.old_injective h)
  · exact s.old_ne_fresh _ _ _
  · rw [s.first_twin_old_second]
    exact fun h => hpb (s.old_injective h)
  · rw [s.first_twin_fresh_away false 2 (by decide +kernel)]
    exact s.old_ne_fresh _ _ _

/-- The side parameter chooses the orientation of the first new vertex. -/
@[reducible] noncomputable def graph (side : Bool) : SolutionGroup.RowGraph A u v where
  Hub := G.Hub ⊕ Bool
  Joint := G.Joint
  hubLabel := s.hubLabel
  hubFlip := Sum.elim G.hubFlip (fun b => if b then !side else side)
  jointLabel := G.jointLabel
  pairing := s.pairing

theorem graph_hub_card (side : Bool) : Fintype.card (s.graph side).Hub = Fintype.card G.Hub + 2 := by
  change Fintype.card (G.Hub ⊕ Bool) = _
  simp

theorem graph_relations (side : Bool) :
    (∑ h : (s.graph side).Hub, ([(s.graph side).hubLabel h] : Multiset R)) =
      (∑ h : G.Hub, ([G.hubLabel h] : Multiset R)) + [s.row, s.row] := by
  change (∑ h : G.Hub ⊕ Bool, ([s.hubLabel h] : Multiset R)) = _
  simp only [Fintype.sum_sum_type, hubLabel, Sum.elim_inl, Sum.elim_inr, Fintype.sum_bool]
  rfl

theorem graph_character (side : Bool) (r : R) : (s.graph side).character r = G.character r := by
  rw [(s.graph side).character_eq_sum, G.character_eq_sum]
  change (∑ h : G.Hub ⊕ Bool, if s.hubLabel h = r then (1 : ZMod 2) else 0) = _
  rw [Fintype.sum_sum_type]
  change (∑ h : G.Hub, if G.hubLabel h = r then (1 : ZMod 2) else 0) +
    (∑ _ : Bool, if s.row = r then (1 : ZMod 2) else 0) = _
  rw [Fintype.sum_bool, InvolutionDerivation.parity_self_add, add_zero]

theorem graph_sign (side : Bool) : (s.graph side).sign = G.sign := by
  change (∑ h : G.Hub ⊕ Bool, (SolutionGroup.triangularPresentation A).parity (s.hubLabel h)) = _
  simp only [Fintype.sum_sum_type, hubLabel, Sum.elim_inl, Sum.elim_inr, Fintype.sum_bool,
    InvolutionDerivation.parity_self_add, add_zero]
  rfl

theorem graph_opposite_flips (side : Bool) :
    (s.graph side).hubFlip (.inr false) ≠ (s.graph side).hubFlip (.inr true) := by
  change side ≠ !side
  cases side <;> decide +kernel

end RowPairInsertion
end ThomGame.Pictures.PortGraph
