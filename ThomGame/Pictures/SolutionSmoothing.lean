module

public import ThomGame.Pictures.SmoothedWires
public import ThomGame.Pictures.SolutionGraph

/-! # Smoothed row graphs for actual solution-group equations -/

@[expose] public section
namespace ThomGame.SolutionGroup

open Pictures

variable {R C : Type*} (S : SparseSystem R C)

/-- The witness includes the source diagram and its actual smoothing trace. -/
theorem word_eq_iff_smoothed_graph (w : List C) (a : ZMod 2) :
    (w.map (x S)).prod = (if a = 1 then J S else 1) ↔
      ∃ (d : RowDiagram S w []) (H : RowGraph S w []) (circles : List C),
        Nonempty (Smoothing d.graph H circles) ∧ IsEmpty H.Joint ∧ H.sign = a := by
  rw [word_eq_iff_diagram]
  constructor
  · rintro ⟨d, hd⟩
    obtain ⟨H, circles, h, hempty, hsign, _⟩ := d.exists_smoothed_graph
    exact ⟨d, H, circles, h, hempty, hsign.trans hd⟩
  · rintro ⟨d, H, circles, ⟨h⟩, _, ha⟩
    exact ⟨d, d.graph_sign.symm.trans (h.sign.symm.trans ha)⟩

theorem J_eq_one_iff_closed_minimal_smoothed_graph :
    J S = 1 ↔
      ∃ (d : RowDiagram S [] []) (H : RowGraph S [] []) (circles : List C),
        d.Minimal ∧ Nonempty (Smoothing d.graph H circles) ∧ IsEmpty H.Joint ∧ H.sign = 1 := by
  rw [J_eq_one_iff_closed_minimal_odd_diagram]
  constructor
  · rintro ⟨d, hd, hmin⟩
    obtain ⟨H, circles, h, hempty, hsign, _⟩ := d.exists_smoothed_graph
    exact ⟨d, H, circles, hmin, h, hempty, hsign.trans hd⟩
  · rintro ⟨d, H, circles, hmin, ⟨h⟩, _, ha⟩
    exact ⟨d, d.graph_sign.symm.trans (h.sign.symm.trans ha), hmin⟩

end ThomGame.SolutionGroup
