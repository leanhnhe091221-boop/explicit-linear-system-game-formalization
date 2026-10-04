module

public import ThomGame.Construction.WheelTrace
public import ThomGame.Construction.CentralNontrivial
public import ThomGame.Pictures.SolutionDiagram

/-!
# Diagram obligations for the actual wheel embedding

The source K has no closed odd diagram, by its proved J nontriviality.
For the target Σ, J=1 is equivalent to the existence of a minimum-size
closed odd row diagram. Transferring a normalized target diagram back to K
is still required; no normalization property is assumed here.
-/

@[expose] public section
namespace ThomGame.Construction

abbrev SigmaDiagram := SolutionGroup.RowDiagram numberedSystem

theorem sigmaDiagram_sign {u v : List (Fin 1889684)} (d : SigmaDiagram u v) :
    d.sign = d.character (rowEquiv oddRow) := by
  rw [SolutionGroup.rowDiagram_sign]
  exact numbered_rhs_pairing d.character

theorem J_sigma_eq_one_iff_closed_minimal_odd_diagram :
    J_sigma = 1 ↔ ∃ d : SigmaDiagram [] [], d.sign = 1 ∧ d.Minimal :=
  SolutionGroup.J_eq_one_iff_closed_minimal_odd_diagram numberedSystem

theorem involution_no_closed_odd_diagram :
    ¬ ∃ d : Pictures.Diagram involutionPresentation [] [], d.sign = 1 := by
  intro h
  have hj := (Pictures.J_eq_one_iff_closed_odd_diagram involutionPresentation).mpr h
  exact J_star_ne_one hj

end ThomGame.Construction
