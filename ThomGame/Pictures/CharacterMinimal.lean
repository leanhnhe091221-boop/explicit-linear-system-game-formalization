module

public import ThomGame.Pictures.SunCharacter
public import ThomGame.Pictures.Surgery

/-!
# Character minimality and its specialization to suns

Character minimality fixes every relation count modulo two, not just the
sign. For sun diagrams the entire character is determined by the ordered
boundary. Thus character minimality, sign minimality, and minimum size
among all diagrams with that boundary coincide.
-/

@[expose] public section
namespace ThomGame.Pictures.Diagram

variable {R S : Type*} [DecidableEq R] {P : InvolutionPresentation R S} {u v : List S}

def CharacterMinimal (d : Diagram P u v) : Prop :=
  ∀ e : Diagram P u v, (∀ r, e.character r = d.character r) → d.size ≤ e.size

theorem exists_characterMinimal (d : Diagram P u v) :
    ∃ e : Diagram P u v, (∀ r, e.character r = d.character r) ∧ e.CharacterMinimal := by
  classical
  have h : ∃ n : Nat, ∃ e : Diagram P u v,
      (∀ r, e.character r = d.character r) ∧ e.size = n :=
    ⟨d.size, d, fun _ => rfl, rfl⟩
  obtain ⟨e, he, hn⟩ := Nat.find_spec h
  refine ⟨e, he, ?_⟩
  intro f hf
  rw [hn]
  exact Nat.find_min' h ⟨f, fun r => (hf r).trans (he r), rfl⟩

theorem sign_eq_of_character_eq [Fintype R] (d e : Diagram P u v)
    (h : ∀ r, d.character r = e.character r) : d.sign = e.sign := by
  simp_rw [sign_eq_character, h]

theorem Minimal.characterMinimal [Fintype R] {d : Diagram P u v}
    (h : d.Minimal) : d.CharacterMinimal :=
  fun e he => h e (e.sign_eq_of_character_eq d he)

variable {n : Nat} {b : Fin n → ZMod 2} {a c : List (Fin n ⊕ Fin n)}

theorem sun_character_eq (d e : Diagram (sunPresentation n b) a c) (j : Fin n) :
    d.character j = e.character j := by rw [d.sun_character, e.sun_character]

theorem sun_characterMinimal_iff (d : Diagram (sunPresentation n b) a c) :
    d.CharacterMinimal ↔ ∀ e : Diagram (sunPresentation n b) a c, d.size ≤ e.size := by
  constructor
  · intro h e
    exact h e (e.sun_character_eq d)
  · exact fun h e _ => h e

theorem sun_minimal_iff_characterMinimal (d : Diagram (sunPresentation n b) a c) :
    d.Minimal ↔ d.CharacterMinimal := by
  constructor
  · exact Minimal.characterMinimal
  · exact fun h e _ => (d.sun_characterMinimal_iff.mp h) e

theorem closed_sun_characterMinimal_size_zero (d : Diagram (sunPresentation n b) [] [])
    (h : d.CharacterMinimal) : d.size = 0 :=
  Nat.eq_zero_of_le_zero ((d.sun_characterMinimal_iff.mp h) (.identity []))

theorem closed_sun_minimal_size_zero (d : Diagram (sunPresentation n b) [] [])
    (h : d.Minimal) : d.size = 0 :=
  d.closed_sun_characterMinimal_size_zero h.characterMinimal

end ThomGame.Pictures.Diagram
