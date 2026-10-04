module

public import ThomGame.Pictures.BoundaryOrder
public import ThomGame.Pictures.BoundarySmoothing

/-! # Smoothing preserves the specified noncrossing boundary condition -/

@[expose] public section
namespace ThomGame.Pictures.Smoothing

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
variable {G H : PortGraph P u v} {circles : List S}

theorem boundaryNoncrossing_iff (d : Smoothing G H circles) :
    H.BoundaryNoncrossing ↔ G.BoundaryNoncrossing := by
  unfold PortGraph.BoundaryNoncrossing
  rw [d.boundaryNext]

end ThomGame.Pictures.Smoothing
