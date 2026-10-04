module

public import ThomGame.Pictures.DiagramBoundaryMoves
public import ThomGame.Pictures.CharacterMinimal

/-! # Reversing a lower boundary preserves labels and minimality -/

@[expose] public section
namespace ThomGame.Pictures.Diagram

variable {R S : Type*} {P : InvolutionPresentation R S} {w : List S}

def reverseBottom (d : Diagram P [] w) : Diagram P [] w.reverse :=
  d.adjoint.reverseDown.adjoint

theorem labels_reverseBottom_perm (d : Diagram P [] w) :
    d.reverseBottom.labels.Perm d.labels :=
  d.adjoint.reverseDown.labels_adjoint_perm.trans
    (d.adjoint.labels_reverseDown_perm.trans d.labels_adjoint_perm)

theorem size_reverseBottom (d : Diagram P [] w) : d.reverseBottom.size = d.size :=
  d.labels_reverseBottom_perm.length_eq

theorem sign_reverseBottom (d : Diagram P [] w) : d.reverseBottom.sign = d.sign :=
  (d.labels_reverseBottom_perm.map P.parity).sum_eq

theorem Minimal.reverseBottom {d : Diagram P [] w} (h : d.Minimal) : d.reverseBottom.Minimal := by
  intro e he
  let f : Diagram P [] w := e.reverseBottom.cast rfl (List.reverse_reverse w)
  have hs : f.sign = d.sign := by
    rw [sign_cast, sign_reverseBottom, he, sign_reverseBottom]
  have hn := h f hs
  simpa only [f, size_cast, size_reverseBottom] using hn

end ThomGame.Pictures.Diagram
