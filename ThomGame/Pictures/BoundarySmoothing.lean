module

public import ThomGame.Pictures.BoundaryReturn
public import ThomGame.Pictures.ReturnPaths
public import ThomGame.Pictures.CircuitSmoothing

/-!
# Smoothing preserves the exact boundary successor

Every boundary port survives smoothing. The unretained intermediate
point in a two-step return is a junction port, so it cannot be a boundary
point. Consequently the ordered visit from one boundary port to the next
is unchanged throughout any smoothing trace.
-/

@[expose] public section
namespace ThomGame.Pictures

open scoped Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}

namespace PortGraph

variable (G : PortGraph P u v)

theorem smooth_boundary_iff (j : G.Joint) (a : (G.smooth j).Dart) :
    G.IsBoundary (G.smoothPortEmbedding j a) ↔ (G.smooth j).IsBoundary a := by
  cases a <;> rfl

theorem boundary_survives (j : G.Joint) (a : G.Dart) (ha : G.IsBoundary a) :
    ∃ b : (G.smooth j).Dart, G.smoothPortEmbedding j b = a := by
  cases a with
  | top i => exact ⟨.top i, rfl⟩
  | bottom i => exact ⟨.bottom i, rfl⟩
  | hub h i => exact ha.elim
  | joint k side => exact ha.elim

theorem smooth_boundaryDart (j : G.Joint) (i : BoundaryIndex u v) :
    G.smoothPortEmbedding j ((G.smooth j).boundaryDart i) = G.boundaryDart i := by
  cases i <;> rfl

theorem smooth_boundaryNext (j : G.Joint) : (G.smooth j).boundaryNext = G.boundaryNext := by
  apply Equiv.ext
  intro i
  have he := MarkedReturn.perm_preserved G.circuitStep G.IsBoundary
    (G.smooth j).circuitStep (G.smooth j).IsBoundary (G.smoothPortEmbedding j)
    (G.smooth_circuit_advances j) (G.smooth_boundary_iff j) (G.boundary_survives j)
    ((G.smooth j).boundaryPorts i)
  have hi : (⟨G.smoothPortEmbedding j ((G.smooth j).boundaryPorts i).val,
      (G.smooth_boundary_iff j _).mpr ((G.smooth j).boundaryPorts i).property⟩ :
      {a : G.Dart // G.IsBoundary a}) = G.boundaryPorts i := by
    cases i <;> rfl
  rw [hi, (G.smooth j).boundaryPorts_next, G.boundaryPorts_next] at he
  apply G.boundaryDart.injective
  change G.smoothPortEmbedding j ((G.smooth j).boundaryDart ((G.smooth j).boundaryNext i)) =
    G.boundaryDart (G.boundaryNext i) at he
  rw [G.smooth_boundaryDart] at he
  exact he

end PortGraph

namespace Smoothing

variable {G H : PortGraph P u v} {circles : List S}

theorem boundaryNext (d : Smoothing G H circles) : H.boundaryNext = G.boundaryNext := by
  induction d with
  | refl _ => rfl
  | @step G H circles j tail ih => exact ih.trans (G.smooth_boundaryNext j)

theorem boundaryNext_pow (d : Smoothing G H circles) (n : Nat)
    (i : PortGraph.BoundaryIndex u v) :
    (H.boundaryNext ^ n) i = (G.boundaryNext ^ n) i := by rw [d.boundaryNext]

end Smoothing
end ThomGame.Pictures
