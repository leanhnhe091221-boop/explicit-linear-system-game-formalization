module

public import ThomGame.Pictures.SlotErasureEuler
public import ThomGame.Pictures.RotationEulerGraph

/-!
# Contracting regions by first return of the dual rotation

Retain an invariant set of paired darts, return the old face permutation
to that set, and multiply by the retained edge pairing. The result is an
actual vertex permutation whose face permutation is exactly that return.
Euler saturation is preserved by the proved dual deletion theorem.
-/

@[expose] public section
namespace ThomGame.Pictures.FaceReturnContraction

open Equiv RibbonConnectivity RotationEuler
open scoped Classical

variable {D : Type*} [Finite D] (f t : Perm D) (M : D → Prop)
  (hM : ∀ x, M (t x) ↔ M x)

noncomputable def rotation : Perm (Subtype M) :=
  MarkedReturn.perm f M * t.subtypePerm hM

theorem face_eq (ht : Function.Involutive t) :
    rotation f t M hM * t.subtypePerm hM = MarkedReturn.perm f M := by
  apply Equiv.ext
  intro x
  change MarkedReturn.perm f M ((t.subtypePerm hM) ((t.subtypePerm hM) x)) = _
  have he : (t.subtypePerm hM) ((t.subtypePerm hM) x) = x := Subtype.ext (ht x.val)
  rw [he]

theorem saturated (ht : Function.Involutive t)
    (he : count f t = 2 * Nat.card (Component f t)) :
    count (rotation f t M hM) (t.subtypePerm hM) =
      2 * Nat.card (Component (rotation f t M hM) (t.subtypePerm hM)) := by
  have hs := firstReturnRotation_saturated f M t hM ht he
  have hi : Function.Involutive (t.subtypePerm hM) := fun x => Subtype.ext (ht x.val)
  have hc := Nat.card_congr (dualComponentEquiv (MarkedReturn.perm f M) (t.subtypePerm hM) hi)
  change count (MarkedReturn.perm f M * t.subtypePerm hM) (t.subtypePerm hM) = _
  rw [dual_count _ _ hi, hs]
  exact congrArg (fun n : Nat => (2 : Int) * n) hc

end ThomGame.Pictures.FaceReturnContraction
