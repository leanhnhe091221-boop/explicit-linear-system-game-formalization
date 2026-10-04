module

public import ThomGame.Finite.Words
public import Mathlib.GroupTheory.PresentedGroup

/-! Relating word evaluation to the universal quotient map of a presentation. -/

@[expose] public section

namespace ThomGame.Word

theorem eval_presented {α : Type*} (rels : Set (FreeGroup α)) (r : Word α) :
    eval (PresentedGroup.of (rels := rels)) r = PresentedGroup.mk rels (FreeGroup.mk r) := by
  have hlift : FreeGroup.lift (PresentedGroup.of (rels := rels)) = PresentedGroup.mk rels := by
    apply FreeGroup.ext_hom
    intro a
    simp [PresentedGroup.of]
  unfold eval
  rw [hlift]

end ThomGame.Word
