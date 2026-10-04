module

public import ThomGame.Pictures.GraphEdges

/-!
# Splicing two equally labelled ports

Conjugating an edge pairing by the transposition `(b, twin a)` makes `a`
and `b` a pair and joins their former partners. Restricting to the other
ports then removes the two-valent junction. If `a` and `b` were already
paired, the restriction deletes precisely that isolated pair.
-/

@[expose] public section
namespace ThomGame.Pictures.Pairing

open scoped Classical

variable {A S : Type*} {label : A → S} (p : Pairing label)

def restrict (keep : A → Prop) (stable : ∀ x, keep x → keep (p.twin x)) :
    Pairing (fun x : {x : A // keep x} => label x.val) where
  twin x := ⟨p.twin x.val, stable x.val x.property⟩
  involutive x := Subtype.ext (p.involutive x.val)
  ne_self x h := p.ne_self x.val (congrArg Subtype.val h)
  label_twin x := p.label_twin x.val

theorem label_swap [DecidableEq A] {a b : A} (h : label a = label b) (x : A) :
    label (Equiv.swap a b x) = label x := by
  by_cases hxa : x = a
  · subst x; simpa using h.symm
  by_cases hxb : x = b
  · subst x; simpa using h
  rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]

theorem twin_eq_of_edge_eq {a b : A} (h : p.edge a = p.edge b) (hne : a ≠ b) :
    p.twin a = b := by
  rcases (p.edge_eq_iff a b).mp h with h | h
  · exact (hne h).elim
  · rw [h, p.involutive]

theorem ext_twin {q : Pairing label} (h : p.twin = q.twin) : p = q := by
  cases p
  cases q
  cases h
  rfl

theorem ext_edge_relation {q : Pairing label}
    (h : ∀ a b, (p.edge a = p.edge b) ↔ (q.edge a = q.edge b)) : p = q := by
  apply p.ext_twin
  funext a
  exact (q.twin_eq_of_edge_eq ((h a (p.twin a)).mp (p.edge_twin a).symm)
    (p.ne_self a).symm).symm

/-- Rewire the two incident edges by an explicit permutation of their ends. -/
noncomputable def splice (a b : A) (hlabel : label a = label b) : Pairing label := by
  classical
  exact p.transport (Equiv.swap b (p.twin a)) label
    (label_swap (hlabel.symm.trans (p.label_twin a).symm))

theorem splice_twin (a b : A) (hlabel : label a = label b) (x : A) :
    (p.splice a b hlabel).twin x =
      Equiv.swap b (p.twin a) (p.twin (Equiv.swap b (p.twin a) x)) := by
  classical
  rfl

theorem splice_twin_left {a b : A} (hab : a ≠ b) (hlabel : label a = label b) :
    (p.splice a b hlabel).twin a = b := by
  classical
  rw [splice_twin, Equiv.swap_apply_of_ne_of_ne hab (p.ne_self a).symm,
    Equiv.swap_apply_right]

theorem splice_twin_right {a b : A} (hab : a ≠ b) (hlabel : label a = label b) :
    (p.splice a b hlabel).twin b = a := by
  calc
    (p.splice a b hlabel).twin b = (p.splice a b hlabel).twin ((p.splice a b hlabel).twin a) :=
      congrArg (p.splice a b hlabel).twin (p.splice_twin_left hab hlabel).symm
    _ = a := (p.splice a b hlabel).involutive a

theorem splice_twin_partner_left {a b : A} (hab : a ≠ b) (hlabel : label a = label b) :
    (p.splice a b hlabel).twin (p.twin a) = p.twin b := by
  classical
  rw [splice_twin, Equiv.swap_apply_right]
  apply Equiv.swap_apply_of_ne_of_ne (p.ne_self b)
  intro h
  have hba : b = a := p.involutive.injective h
  exact hab hba.symm

theorem splice_twin_partner_right {a b : A} (hab : a ≠ b) (hlabel : label a = label b) :
    (p.splice a b hlabel).twin (p.twin b) = p.twin a := by
  rw [← p.splice_twin_partner_left hab hlabel, (p.splice a b hlabel).involutive]

theorem splice_twin_unchanged {a b x : A} (hlabel : label a = label b)
    (hxa : x ≠ a) (hxb : x ≠ b) (hxpa : x ≠ p.twin a) (hxpb : x ≠ p.twin b) :
    (p.splice a b hlabel).twin x = p.twin x := by
  classical
  rw [splice_twin, Equiv.swap_apply_of_ne_of_ne hxb hxpa]
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    have hh := congrArg p.twin h
    rw [p.involutive] at hh
    exact hxpb hh
  · intro h
    exact hxa (p.involutive.injective h)

theorem splice_twin_of_paired {a b : A} (hlabel : label a = label b) (hp : p.twin a = b)
    (x : A) : (p.splice a b hlabel).twin x = p.twin x := by
  classical
  rw [splice_twin, hp]
  simp

/-- The surviving ports; neither the old junction nor its two slots is retained. -/
abbrev Away (a b : A) := {x : A // x ≠ a ∧ x ≠ b}

theorem splice_preserves_away {a b : A} (hab : a ≠ b) (hlabel : label a = label b)
    (x : A) (hx : x ≠ a ∧ x ≠ b) :
    (p.splice a b hlabel).twin x ≠ a ∧ (p.splice a b hlabel).twin x ≠ b := by
  constructor
  · intro h
    have hh := congrArg (p.splice a b hlabel).twin h
    rw [(p.splice a b hlabel).involutive, p.splice_twin_left hab hlabel] at hh
    exact hx.2 hh
  · intro h
    have hh := congrArg (p.splice a b hlabel).twin h
    rw [(p.splice a b hlabel).involutive, p.splice_twin_right hab hlabel] at hh
    exact hx.1 hh

noncomputable def smooth (a b : A) (hab : a ≠ b) (hlabel : label a = label b) :
    Pairing (fun x : Away a b => label x.val) :=
  (p.splice a b hlabel).restrict (fun x => x ≠ a ∧ x ≠ b)
    (p.splice_preserves_away hab hlabel)

theorem smooth_twin_val {a b : A} (hab : a ≠ b) (hlabel : label a = label b) (x : Away a b) :
    ((p.smooth a b hab hlabel).twin x).val = (p.splice a b hlabel).twin x.val := rfl

theorem partner_left_away {a b : A} (hp : p.twin a ≠ b) :
    p.twin a ≠ a ∧ p.twin a ≠ b := ⟨p.ne_self a, hp⟩

theorem partner_right_away {a b : A} (hp : p.twin a ≠ b) :
    p.twin b ≠ a ∧ p.twin b ≠ b := by
  refine ⟨?_, p.ne_self b⟩
  intro h
  have hh := congrArg p.twin h
  rw [p.involutive] at hh
  exact hp hh.symm

/-- The two old edge partners are paired after smoothing a non-loop junction. -/
theorem smooth_joins_partners {a b : A} (hab : a ≠ b) (hlabel : label a = label b)
    (hp : p.twin a ≠ b) :
    (p.smooth a b hab hlabel).twin ⟨p.twin a, p.partner_left_away hp⟩ =
      ⟨p.twin b, p.partner_right_away hp⟩ :=
  Subtype.ext (p.splice_twin_partner_left hab hlabel)

end ThomGame.Pictures.Pairing
