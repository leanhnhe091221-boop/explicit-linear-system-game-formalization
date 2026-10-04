module

public import ThomGame.Construction.SolutionGroup
public import ThomGame.Groups.SolutionGroupRowOrdering
public import ThomGame.Groups.PaperSolutionGroup

/-! The actual matrix system in increasing column order, and the paper's exact group. -/

@[expose] public section
namespace ThomGame.Construction

def paperSystem : SparseSystem (Fin 1417152) (Fin 1889684) := numberedSystem.ordered

theorem paperSystem_matrix : paperSystem.matrix = A := numberedSystem.ordered_matrix

theorem paperSystem_rhs : paperSystem.rhs = b := rfl

theorem paperSystem_strictMono (r : Fin 1417152) : StrictMono (paperSystem.column r) :=
  numberedSystem.ordered_strictMono r

theorem paperSystem_column_order (r : Fin 1417152) :
    paperSystem.column r 0 < paperSystem.column r 1 ∧
      paperSystem.column r 1 < paperSystem.column r 2 :=
  ⟨paperSystem_strictMono r (by decide), paperSystem_strictMono r (by decide)⟩

theorem paperSystem_support (r : Fin 1417152) (c : Fin 1889684) :
    A r c = 1 ↔ ∃ i, paperSystem.column r i = c := by
  rw [← paperSystem_matrix]
  exact paperSystem.matrix_eq_one_iff r c

theorem paperSystem_column_unique (r : Fin 1417152) (v : Fin 3 → Fin 1889684)
    (hv : StrictMono v) (hs : ∀ i, A r (v i) = 1) : v = paperSystem.column r :=
  numberedSystem.ordered_column_unique r v hv hs

theorem paperSystem_rhs_formula (r : Fin 1417152) :
    paperSystem.rhs r = if r.val + 1 = 1417141 then 1 else 0 := b_formula r

abbrev PaperSigmaGroup := SolutionGroup.Paper.GroupOf paperSystem

def paper_J_sigma : PaperSigmaGroup := SolutionGroup.Paper.J paperSystem

noncomputable def paperSigmaEquiv : PaperSigmaGroup ≃* SigmaGroup :=
  (SolutionGroup.Paper.solutionEquiv paperSystem).trans
    (SolutionGroup.rowPermutationEquiv numberedSystem.orderedPermutation)

theorem paperSigmaEquiv_J : paperSigmaEquiv paper_J_sigma = J_sigma := by
  change SolutionGroup.rowPermutationEquiv numberedSystem.orderedPermutation
    (SolutionGroup.Paper.solutionEquiv paperSystem (SolutionGroup.Paper.J paperSystem)) = _
  rw [SolutionGroup.Paper.solutionEquiv_J]
  exact SolutionGroup.rowPermutationEquiv_J _

theorem paperSigmaEquiv_x (c : Fin 1889684) :
    paperSigmaEquiv (SolutionGroup.Paper.x paperSystem c) = observable c := by
  change SolutionGroup.rowPermutationEquiv numberedSystem.orderedPermutation
    (SolutionGroup.Paper.solutionEquiv paperSystem (SolutionGroup.Paper.x paperSystem c)) = _
  rw [SolutionGroup.Paper.solutionEquiv_x]
  exact SolutionGroup.rowPermutationEquiv_x _ c

theorem paper_relators_finite : (SolutionGroup.Paper.relators paperSystem).Finite :=
  SolutionGroup.Paper.relators_finite paperSystem

end ThomGame.Construction
