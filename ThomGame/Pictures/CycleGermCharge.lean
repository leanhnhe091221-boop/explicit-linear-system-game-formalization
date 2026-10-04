module

public import ThomGame.Pictures.CycleFrontier
public import ThomGame.Pictures.CircuitGermCharge

/-! # The zero-sign germ counting step for a stellar rim -/

@[expose] public section

theorem ThomGame.SolutionGroup.triangularPresentation_parity {R S : Type*} (A : ThomGame.SparseSystem R S) :
    (ThomGame.SolutionGroup.triangularPresentation A).parity = A.rhs := rfl

namespace ThomGame.Pictures.PortGraph

open scoped BigOperators Classical

variable {R S : Type*} [DecidableEq R] [DecidableEq S] {A : SparseSystem R S}
  (G : SolutionGroup.RowGraph A [] []) (C : Hypergraph.Cycle A.hypergraph)

theorem rimSimpleCircuit_hub_label (a : G.RimDart C) (h : G.Hub)
    (hh : (G.rimSimpleCircuit C (by simp) (by simp) a).OnCircuitVertex (.inr (.inl h))) :
    G.hubLabel h ∈ Set.range C.vertex := by
  obtain ⟨i, hi⟩ := hh
  have hr := G.rimSimpleCircuit_rim C (by simp) (by simp) a i
  cases he : (G.rimSimpleCircuit C (by simp) (by simp) a).dart i with
  | top j => exact j.elim0
  | bottom j => exact j.elim0
  | hub k j =>
    rw [he] at hi hr
    have hk : k = h := Sum.inl.inj (Sum.inr.inj hi)
    subst k
    apply C.closed hr
    exact (A.mem_hypergraph_incidence _ _).mpr
      ⟨j, (SolutionGroup.rowGraph_port_label A G h j).symm⟩
  | joint j b => rw [he] at hi; cases hi

theorem rimSimpleCircuit_stellar_sign (a : G.RimDart C) (hc : C.Stellar A.rhs) :
    (∑ h : (G.rimSimpleCircuit C (by simp) (by simp) a).CircuitHub,
      A.rhs (G.hubLabel h.val)) = 0 := by
  apply Finset.sum_eq_zero
  intro h _
  obtain ⟨i, hi⟩ := G.rimSimpleCircuit_hub_label C a h.val h.property
  rw [← hi]
  exact hc.rhs_zero i

variable (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
  2 * Nat.card (RibbonConnectivity.Component G.circuitStep G.pairing.perm))

include hEuler in
theorem rimSimpleCircuit_exists_germ_sign_zero (a : G.RimDart C) (hc : C.Stellar A.rhs)
    (hComponent : (∑ h : (G.rimSimpleCircuit C (by simp) (by simp) a).ComponentHub,
      A.rhs (G.hubLabel h.val)) = 1) :
    ∃ s, ((G.rimSimpleCircuit C (by simp) (by simp) a).germGraph hEuler s).sign = 0 :=
  (G.rimSimpleCircuit C (by simp) (by simp) a).exists_germGraph_sign_zero hEuler
    (G.rimSimpleCircuit_stellar_sign C a hc) hComponent

/-- The componentwise parity conclusion, with the actual germ and actual row signs. -/
def OddRimComponentHasZeroSignGerm (a : G.RimDart C) : Prop :=
  (∑ h : (G.rimSimpleCircuit C (by simp) (by simp) a).ComponentHub,
    A.rhs (G.hubLabel h.val)) = 1 →
      ∃ s, ((G.rimSimpleCircuit C (by simp) (by simp) a).germGraph hEuler s).sign = 0

include hEuler in
theorem stellar_oddRimComponentHasZeroSignGerm (a : G.RimDart C) (hc : C.Stellar A.rhs) :
    G.OddRimComponentHasZeroSignGerm C hEuler a :=
  G.rimSimpleCircuit_exists_germ_sign_zero C hEuler a hc

end ThomGame.Pictures.PortGraph
