module

public import ThomGame.Construction.PaperGame
public import ThomGame.Quantum.ClassicalIncidenceGame

/-! The exact classical value is an additional corollary of the existing
inconsistency certificate and the existing uniform-incidence game definition. -/

@[expose] public section
namespace ThomGame.Construction

open scoped BigOperators
open Quantum

/-- The unique row with right-hand side one; indices in the manuscript start at one. -/
def paperOddRow : Fin 1417152 := ⟨1417140, by omega⟩

theorem paperSystem_rhs_eq_oddRow (r : Fin 1417152) :
    paperSystem.rhs r = if r = paperOddRow then 1 else 0 := by
  rw [paperSystem_rhs_formula]
  have hr : r.val + 1 = 1417141 ↔ r = paperOddRow := by
    simp only [Fin.ext_iff, paperOddRow]
    omega
  simp only [hr]

/-- Bob always answers zero. Alice flips only the first slot of the unique odd row. -/
def paperClassicalAlice (r : Fin 1417152) (i : Fin 3) : ZMod 2 :=
  if r = paperOddRow ∧ i = 0 then 1 else 0

def paperClassicalBob (_c : Fin 1889684) : ZMod 2 := 0

theorem paperClassicalAlice_parity (r : Fin 1417152) :
    ∑ i, paperClassicalAlice r i = paperSystem.rhs r := by
  rw [paperSystem_rhs_eq_oddRow]
  by_cases hr : r = paperOddRow <;> simp [paperClassicalAlice, hr]

theorem paperClassical_unique_rejection (r : Fin 1417152) (i : Fin 3) :
    paperSystem.Accepts r i (paperClassicalAlice r)
      (paperClassicalBob (paperSystem.column r i)) ↔ (r, i) ≠ (paperOddRow, 0) := by
  simp only [SparseSystem.Accepts, paperClassicalAlice_parity, true_and]
  simp [paperClassicalAlice, paperClassicalBob, Prod.mk.injEq]

theorem paperClassical_success :
    paperGame.success (deterministicCorrelation paperClassicalAlice paperClassicalBob) =
      1 - (1 / 4251456 : ℝ) := by
  have h := paperSystem.incidenceGame_deterministic_eq_of_unique_rejection
    paperClassicalAlice paperClassicalBob paperOddRow 0 paperClassical_unique_rejection
  norm_num [paperGame] at h ⊢
  exact h

theorem paperSystem_no_perfect_deterministic :
    ¬ ∃ alice bob, paperSystem.PerfectDeterministic alice bob := by
  rintro ⟨alice, bob, h⟩
  exact numbered_no_solution ⟨bob,
    (numberedSystem.orderedPermutation.satisfies_iff bob).mp
      (paperSystem.satisfies_of_perfect h)⟩

theorem paper_deterministic_success_le
    (alice : Fin 1417152 → Fin 3 → ZMod 2) (bob : Fin 1889684 → ZMod 2) :
    paperGame.success (deterministicCorrelation alice bob) ≤ 1 - (1 / 4251456 : ℝ) := by
  have h := paperSystem.incidenceGame_deterministic_le_of_not_perfect alice bob
    (fun hp => paperSystem_no_perfect_deterministic ⟨alice, bob, hp⟩)
  norm_num [paperGame] at h ⊢
  exact h

/-- Exact classical value, allowing arbitrary shared randomness. -/
theorem paper_omegaC_eq : paperGame.omegaC = 1 - (1 / 4251456 : ℝ) := by
  apply le_antisymm
  · exact paperGame.omegaC_le_of_deterministic paper_deterministic_success_le
  · rw [← paperClassical_success]
    exact paperGame.deterministic_success_le_omegaC paperClassicalAlice paperClassicalBob

end ThomGame.Construction
