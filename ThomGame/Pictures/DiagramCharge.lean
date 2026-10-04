module

public import ThomGame.Pictures.Diagram

/-!
# Boundary charge and relation multiplicities

An arbitrary mod-two weight on edge labels gives a conservation law:
the sum of incident charges at all relation vertices is the total charge
of the two boundaries. This follows from the actual diagram constructors.
-/

@[expose] public section
namespace ThomGame.Pictures

open InvolutionDerivation
open scoped BigOperators

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}

theorem Diagram.charge_balance (d : Diagram P u v) (χ : S → ZMod 2) :
    (d.labels.map (fun r => ((P.word r).map χ).sum)).sum = (u.map χ).sum + (v.map χ).sum := by
  induction d with
  | identity w => simp [Diagram.labels, parity_self_add]
  | cap s => simp [Diagram.labels, parity_self_add]
  | cup s => simp [Diagram.labels, parity_self_add]
  | down r => simp [Diagram.labels]
  | up r => simp [Diagram.labels]
  | @comp u v w d e ihd ihe =>
    simp only [Diagram.labels, List.map_append, List.sum_append, ihd, ihe]
    rw [add_assoc, ← add_assoc ((v.map χ).sum), parity_self_add, zero_add]
  | tensor d e ihd ihe =>
    simp only [Diagram.labels, List.map_append, List.sum_append, ihd, ihe]
    simp only [add_assoc, add_left_comm]

theorem sum_indicator_eq_count [BEq S] [LawfulBEq S] [DecidableEq S] (w : List S) (s : S) :
    (w.map (fun x => if x = s then (1 : ZMod 2) else 0)).sum = (w.count s : ZMod 2) := by
  induction w with
  | nil => simp
  | cons x w ih =>
    by_cases h : x = s
    · subst x
      simp [ih, add_comm]
    · simp [h, ih]

end ThomGame.Pictures
