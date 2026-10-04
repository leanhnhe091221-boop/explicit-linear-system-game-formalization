module

public import ThomGame.Pictures.CircuitGermDiagram

/-! # The stored forward germ becomes a correctly ordered top boundary -/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open CircularPartition

variable {R S : Type*} {P : InvolutionPresentation R S} {w : List S}
  (G : PortGraph P [] w)
  (hnext : ∀ i : Fin w.length, G.boundaryNext (.inr i) = .inr (finRotate _ i))

include hnext in
theorem forwardBottom_swapBoundary_next : G.swapBoundary.boundaryNext = boundaryCyclic w [] := by
  ext a
  cases a with
  | inl i =>
    rw [boundaryCyclic_top]
    have he := G.swapBoundary_next (.inr i)
    rw [hnext i] at he
    exact he
  | inr i => exact i.elim0

include hnext in
theorem forwardBottom_swapBoundary_noncrossing : G.swapBoundary.BoundaryNoncrossing := by
  change OrderedNoncrossing _ _ _
  rw [G.forwardBottom_swapBoundary_next hnext]
  exact ⟨follows_self _, fun a b _ _ _ _ _ _ => boundaryCyclic_sameCycle a b⟩

include hnext in
theorem forwardBottom_swapBoundary_sees : G.swapBoundary.BoundarySeesComponents := by
  apply G.swapBoundary.boundarySeesComponents_of_one_cycle
  intro a b
  rw [G.forwardBottom_swapBoundary_next hnext]
  exact boundaryCyclic_sameCycle a b

end ThomGame.Pictures.PortGraph
