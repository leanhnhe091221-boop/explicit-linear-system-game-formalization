module

public import ThomGame.Pictures.BoundaryQuadPath

/-! # Constructing an outer quadrilateral from its actual three face steps -/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.BoundaryQuadPath

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
  {G : PortGraph P u v}

def ofThreeSteps (hnext : G.boundaryNext = boundaryCyclic u v)
    (a b : BoundaryIndex u v) (h k : G.Hub)
    (i : Fin (P.word (G.hubLabel h)).length) (j : Fin (P.word (G.hubLabel k)).length)
    (h₁ : G.circuitStep (G.boundaryDart a) = .hub h i)
    (h₂ : G.circuitStep (.hub h i) = .hub k j)
    (h₃ : G.circuitStep (.hub k j) = G.boundaryDart b)
    (hhk : h ≠ k) : G.BoundaryQuadPath where
  start := a
  finish := b
  firstHub := h
  secondHub := k
  firstSlot := i
  secondSlot := j
  first_step := h₁
  second_step := h₂
  last_step := h₃
  boundary_adjacent := by
    rw [← hnext]
    apply G.boundaryNext_eq_of_first a b (n := 3) (by omega)
    · simp only [pow_succ', pow_zero, Equiv.Perm.one_apply, Equiv.Perm.mul_apply, h₁, h₂, h₃]
    · intro m hm hm₃
      have he : m = 1 ∨ m = 2 := by omega
      rcases he with rfl | rfl
      · rw [pow_one, h₁]; exact id
      · rw [pow_two, Equiv.Perm.mul_apply, h₁, h₂]; exact id
  ends_distinct := by
    intro hab
    have ht : G.pairing.twin (.hub k j) = G.boundaryDart b :=
      G.rotation.injective (h₃.trans (G.rotation_boundaryDart b).symm)
    have hv := (G.vertex_circuitStep (G.boundaryDart a)).symm.trans (congrArg Port.vertex h₁)
    rw [hab, ← ht, G.pairing.involutive] at hv
    exact hhk (Sum.inl.inj (Sum.inr.inj hv)).symm
  hubs_distinct := hhk

end ThomGame.Pictures.PortGraph.BoundaryQuadPath
