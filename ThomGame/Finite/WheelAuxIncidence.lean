module

public import ThomGame.Finite.WheelCentralRetract

/-! # The exact two endpoints of every auxiliary wheel edge -/

@[expose] public section
namespace ThomGame.Wheel.Family

variable {R V : Type*} (F : Family R V)

def auxEndpoints (r : R) (j : Fin (F.size r)) : Fin 4 → F.Row × F.Row :=
  ![(⟨r, j, 0⟩, ⟨r, (finRotate (F.size r)).symm j, 1⟩),
    (⟨r, j, 0⟩, ⟨r, j, 1⟩),
    (⟨r, j, 1⟩, ⟨r, j, 2⟩),
    (⟨r, j, 2⟩, ⟨r, (finRotate (F.size r)).symm j, 2⟩)]

theorem aux_incident (r : R) (j : Fin (F.size r)) (k : Fin 4) (row : F.Row) :
    F.aux r j k ∈ F.system.hypergraph.incidence row ↔
      row = (F.auxEndpoints r j k).1 ∨ row = (F.auxEndpoints r j k).2 := by
  classical
  rcases row with ⟨s, i, l⟩
  by_cases hsr : s = r
  · subst s
    have hn : j = finRotate (F.size r) i ↔ i = (finRotate (F.size r)).symm j := by
      rw [Equiv.eq_symm_apply]
      exact eq_comm
    simp only [finRotate_apply, finRotate_symm_apply] at hn
    fin_cases k <;> fin_cases l
    all_goals
      simp [auxEndpoints, SparseSystem.hypergraph, system, columns, aux, hn, eq_comm]
  · have hrs : r ≠ s := Ne.symm hsr
    fin_cases k <;> fin_cases l <;>
      simp [auxEndpoints, SparseSystem.hypergraph, system, columns, aux, hsr, hrs]

end ThomGame.Wheel.Family
