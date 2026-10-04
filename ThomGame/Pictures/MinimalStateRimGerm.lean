module

public import ThomGame.Pictures.ClosedMinimalOddState
public import ThomGame.Pictures.MinimalRimGerm

/-! # Minimal stellar germs on actual odd row-graph states -/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.ClosedMinimalOddState

open scoped BigOperators

variable {R S : Type*} [DecidableEq R] [DecidableEq S] {A : SparseSystem R S}
    {G : SolutionGroup.RowGraph A [] []} (h : G.ClosedMinimalOddState)
    (C : Hypergraph.Cycle A.hypergraph) (a : G.RimDart C)

theorem exists_minimal_stellar_rim_germ (hc : C.Stellar A.rhs) :
    let D := G.rimSimpleCircuit C (by simp) (by simp) a
    ∃ s, ∃ g : SolutionGroup.RowDiagram A [] (D.frontierWord (!s)),
      (g.labels : Multiset R) =
        (∑ x : (D.germGraph h.dualEuler s).Hub,
          ([(D.germGraph h.dualEuler s).hubLabel x] : Multiset R)) ∧
      g.size = Fintype.card (D.germGraph h.dualEuler s).Hub ∧ g.sign = 0 ∧ g.Minimal ∧
      (D.germGraph h.dualEuler s).sign = 0 := by
  obtain ⟨s, g, hl, hn, hz, hm, hgs⟩ :=
    h.exists_minimal_zero_sign_germ (fun _ => by change 0 < 3; omega)
      (G.rimSimpleCircuit C (by simp) (by simp) a) (G.rimSimpleCircuit_stellar_sign C a hc)
  exact ⟨s, g, hl, hn, hz, hm, hgs⟩

end ThomGame.Pictures.PortGraph.ClosedMinimalOddState
