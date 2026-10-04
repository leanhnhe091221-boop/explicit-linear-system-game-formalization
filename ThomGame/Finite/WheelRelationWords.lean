module

public import ThomGame.Finite.WheelSystem
public import ThomGame.Groups.InvolutionPresentation
public import Mathlib.Data.List.OfFn

/-! # The original relation words recovered from an indexed wheel family -/

@[expose] public section
namespace ThomGame.Wheel.Family

variable {R V : Type*} (F : Family R V)

def presentation : InvolutionPresentation R V where
  word r := List.ofFn (F.letter r)
  parity := F.parity

def presentationIndex (r : R) : Fin (F.presentation.word r).length ≃ Fin (F.size r) :=
  finCongr (by exact List.length_ofFn)

theorem presentation_get (r : R) (i : Fin (F.presentation.word r).length) :
    (F.presentation.word r)[i] = F.letter r (F.presentationIndex r i) := by
  exact List.get_ofFn (F.letter r) i

theorem finCongr_rotate {m n : Nat} (h : m = n) (i : Fin m) :
    finCongr h (finRotate m i) = finRotate n (finCongr h i) := by
  subst n
  rfl

theorem finCongr_rotate_symm {m n : Nat} (h : m = n) (i : Fin m) :
    finCongr h ((finRotate m).symm i) = (finRotate n).symm (finCongr h i) := by
  subst n
  rfl

theorem presentationIndex_rotate (r : R) (i : Fin (F.presentation.word r).length) :
    F.presentationIndex r (finRotate _ i) = finRotate (F.size r) (F.presentationIndex r i) :=
  finCongr_rotate _ i

theorem presentationIndex_rotate_symm (r : R) (i : Fin (F.presentation.word r).length) :
    F.presentationIndex r ((finRotate _).symm i) = (finRotate (F.size r)).symm (F.presentationIndex r i) :=
  finCongr_rotate_symm _ i

end ThomGame.Wheel.Family
