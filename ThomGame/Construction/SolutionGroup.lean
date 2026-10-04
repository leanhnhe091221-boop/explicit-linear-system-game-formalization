module

public import ThomGame.Construction.MatrixData
public import ThomGame.Groups.SolutionGroup
public import ThomGame.Groups.SolutionGroupReindex

/-!
# The solution group Σ of the concrete numbered system

This fixes the actual group and the distinguished central element used in
the main theorem. Proving that this central element is nontrivial remains a
separate embedding problem; it is not an assumption of these definitions.
-/

@[expose] public section
namespace ThomGame.Construction

abbrev SigmaGroup := SolutionGroup.GroupOf numberedSystem

def J_sigma : SigmaGroup := SolutionGroup.J numberedSystem

def observable (c : Fin 1889684) : SigmaGroup := SolutionGroup.x numberedSystem c

theorem J_sigma_square : J_sigma * J_sigma = 1 := SolutionGroup.J_sq numberedSystem

theorem observable_square (c : Fin 1889684) : observable c * observable c = 1 :=
  SolutionGroup.x_sq numberedSystem c

theorem J_sigma_central (g : SigmaGroup) : Commute J_sigma g :=
  SolutionGroup.J_commutes numberedSystem g

theorem observables_row_commute (r : Fin 1417152) (i j : Fin 3) :
    Commute (observable (numberedSystem.column r i)) (observable (numberedSystem.column r j)) :=
  SolutionGroup.row_commutes numberedSystem r i j

theorem observables_row_product (r : Fin 1417152) :
    observable (numberedSystem.column r 0) * observable (numberedSystem.column r 1) *
      observable (numberedSystem.column r 2) =
        if r.val + 1 = 1417141 then J_sigma else 1 := by
  have h := SolutionGroup.row_product numberedSystem r
  have hb := b_formula r
  change numberedSystem.rhs r = _ at hb
  by_cases hr : r.val + 1 = 1417141
  · have hb1 : numberedSystem.rhs r = 1 := by simpa [hr] using hb
    simpa [observable, J_sigma, hb1, hr] using h
  · have hb0 : numberedSystem.rhs r = 0 := by simpa [hr] using hb
    simpa [observable, J_sigma, hb0, hr] using h

theorem Sigma_presentation_finite : (SolutionGroup.relators numberedSystem).Finite :=
  SolutionGroup.relators_finite numberedSystem

/-- The abstract wheel-indexed group and the numbered matrix's group agree. -/
def wheelSolutionEquiv : SolutionGroup.GroupOf system ≃* SigmaGroup :=
  SolutionGroup.reindexEquiv system rowEquiv colEquiv

theorem wheelSolutionEquiv_J : wheelSolutionEquiv (SolutionGroup.J system) = J_sigma :=
  SolutionGroup.reindexEquiv_J system rowEquiv colEquiv

end ThomGame.Construction
