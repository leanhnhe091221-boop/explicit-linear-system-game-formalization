module

public import ThomGame.Pictures.TraceDiagram
public import ThomGame.Pictures.Surgery
public import ThomGame.Pictures.Duality
public import ThomGame.Groups.SolutionTrace

/-!
# Diagram syntax for the actual three-variable solution-group relations

Each relation vertex has the three ordered column labels of a matrix row.
The correspondence includes the exact central sign and the existence of
a minimum-size representative for any represented boundary equation.
-/

@[expose] public section
namespace ThomGame.SolutionGroup

open Pictures
open scoped BigOperators

variable {R C : Type*} (S : SparseSystem R C)

abbrev RowDiagram := Diagram (triangularPresentation S)

theorem word_eq_iff_diagram (w : List C) (a : ZMod 2) :
    (w.map (x S)).prod = (if a = 1 then J S else 1) ↔
      ∃ d : RowDiagram S w [], d.sign = a :=
  ((word_eq_iff_trace S w a).trans
    (InvolutionDerivation.word_eq_iff_trace (triangularPresentation S) w a).symm).trans
      (Pictures.word_eq_iff_diagram (triangularPresentation S) w a)

theorem word_eq_iff_minimal_diagram (w : List C) (a : ZMod 2) :
    (w.map (x S)).prod = (if a = 1 then J S else 1) ↔
      ∃ d : RowDiagram S w [], d.sign = a ∧ d.Minimal := by
  rw [word_eq_iff_diagram]
  constructor
  · rintro ⟨d, hd⟩
    obtain ⟨e, he, hmin⟩ := d.exists_minimal
    exact ⟨e, he.trans hd, hmin⟩
  · rintro ⟨d, hd, _⟩
    exact ⟨d, hd⟩

theorem J_eq_one_iff_closed_minimal_odd_diagram :
    J S = 1 ↔ ∃ d : RowDiagram S [] [], d.sign = 1 ∧ d.Minimal := by
  have h := word_eq_iff_minimal_diagram S [] 1
  change (1 : GroupOf S) = J S ↔ ∃ d : RowDiagram S [] [], d.sign = 1 ∧ d.Minimal at h
  exact eq_comm.trans h

theorem rowDiagram_sign [Fintype R] [DecidableEq R] {u v : List C} (d : RowDiagram S u v) :
    d.sign = ∑ r, d.character r * S.rhs r := d.sign_eq_character

end ThomGame.SolutionGroup
