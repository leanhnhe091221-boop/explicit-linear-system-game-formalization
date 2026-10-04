module

public import ThomGame.Pictures.RimNonfacialCount
public import ThomGame.Pictures.CircuitHubPorts
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Bounding the actual number of constellation rim components

Each restricted rim component contains a hub. Two components of the
same cycle cannot contain the same hub, by unique rim continuation.
Thus their count is bounded by the hub count, independently of circuit
enumeration, orientation, Euler saturation, or label coverage.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open RibbonConnectivity
open scoped Classical BigOperators

variable {R S : Type*} [DecidableEq R] [DecidableEq S] {A : SparseSystem R S}
  (G : SolutionGroup.RowGraph A [] []) [IsEmpty G.Joint]
  (γ : Hypergraph.Cycle A.hypergraph)

noncomputable def rimComponentHub
    (c : G.RimComponent γ (by simp) (by simp)) : G.Hub :=
  (G.rimSimpleCircuit γ (by simp) (by simp) c.out).hubAt 0

theorem rimComponentHub_vertex (c : G.RimComponent γ (by simp) (by simp)) :
    c.out.val.vertex = .inr (.inl (G.rimComponentHub γ c)) := by
  have he : (G.rimSimpleCircuit γ (by simp) (by simp) c.out).dart 0 = c.out.val :=
    congrArg Subtype.val (OrbitEnumeration.dart_zero (G.rimWalk γ (by simp) (by simp)) c.out)
  exact (congrArg Port.vertex he).symm.trans
    ((G.rimSimpleCircuit γ (by simp) (by simp) c.out).hubAt_vertex 0)

theorem rimComponentHub_injective : Function.Injective (G.rimComponentHub γ) := by
  intro c d he
  have hv : c.out.val.vertex = d.out.val.vertex :=
    (G.rimComponentHub_vertex γ c).trans
      ((congrArg (fun h : G.Hub => (Sum.inr (Sum.inl h) : G.Vertex)) he).trans
        (G.rimComponentHub_vertex γ d).symm)
  exact (Quotient.out_eq c).symm.trans
    ((G.rimComponent_vertex γ (by simp) (by simp) hv).trans (Quotient.out_eq d))

noncomputable def rimCount : Nat := Nat.card (G.RimComponent γ (by simp) (by simp))

theorem rimCount_le_hubs : G.rimCount γ ≤ Fintype.card G.Hub := by
  rw [rimCount, Nat.card_eq_fintype_card]
  exact Fintype.card_le_of_injective _ (G.rimComponentHub_injective γ)

variable {I : Type*} [Fintype I] (Φ : I → Hypergraph.Cycle A.hypergraph)

noncomputable def totalRimCount : Nat := ∑ i : I, G.rimCount (Φ i)

theorem totalRimCount_le_hubs : G.totalRimCount Φ ≤ Fintype.card I * Fintype.card G.Hub := by
  calc
    G.totalRimCount Φ ≤ ∑ _ : I, Fintype.card G.Hub :=
      Finset.sum_le_sum (fun i _ => G.rimCount_le_hubs (Φ i))
    _ = Fintype.card I * Fintype.card G.Hub := by simp

end ThomGame.Pictures.PortGraph
