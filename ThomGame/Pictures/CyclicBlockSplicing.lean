module

public import ThomGame.Pictures.DiagramSplicing
public import ThomGame.Pictures.PermutationSurgery
public import Mathlib.GroupTheory.Perm.List

/-!
# The cyclic word produced by joining two vertex blocks

The target swap used in edge contraction concatenates the two rooted
cyclic words in exactly the order used by diagram port splicing. Erasing
the two selected port occurrences leaves the concatenated tails. Ports
are separate objects, so repeated generator labels cause no ambiguity.
-/

@[expose] public section
namespace ThomGame.Pictures

open Equiv CycleSurgery

namespace CyclicBlock

variable {D : Type*} [DecidableEq D]

theorem formPerm_join (a b : D) (u v : List D) (hb : b ∉ a :: u) :
    ((a :: u) ++ (b :: v)).formPerm =
      splice ((a :: u).formPerm * (b :: v).formPerm) a b := by
  induction u generalizing a with
  | nil => simp [splice, List.formPerm_cons_cons]
  | cons x u ih =>
    have hba : b ≠ a := fun he => hb (he ▸ List.mem_cons_self)
    have hbx : b ≠ x := fun he => hb (List.mem_cons_of_mem _ (he ▸ List.mem_cons_self))
    have hbu : b ∉ x :: u := fun he => hb (List.mem_cons_of_mem _ he)
    have hs : swap a x * swap x b = swap a b * swap a x := by
      rw [mul_swap_eq_swap_mul, swap_apply_right,
        swap_apply_of_ne_of_ne hba hbx]
    simp only [List.cons_append, List.formPerm_cons_cons] at ih ⊢
    rw [ih x hbu]
    change swap a x * (swap x b * ((x :: u).formPerm * (b :: v).formPerm)) =
      swap a b * (swap a x * (x :: u).formPerm * (b :: v).formPerm)
    rw [← mul_assoc (swap a x) (swap x b), hs]
    simp only [mul_assoc]

theorem filter_join (a b : D) (u v : List D)
    (ha : a ∉ u ++ v) (hb : b ∉ u ++ v) :
    (((a :: u) ++ (b :: v)).filter (fun x => x ≠ a ∧ x ≠ b)) = u ++ v := by
  have hu : ∀ x ∈ u, x ≠ a ∧ x ≠ b := by
    intro x hx
    constructor
    · intro he; subst x; exact ha (List.mem_append_left _ hx)
    · intro he; subst x; exact hb (List.mem_append_left _ hx)
  have hv : ∀ x ∈ v, x ≠ a ∧ x ≠ b := by
    intro x hx
    constructor
    · intro he; subst x; exact ha (List.mem_append_right _ hx)
    · intro he; subst x; exact hb (List.mem_append_right _ hx)
  simp only [List.filter_append, List.filter_cons, ne_eq, not_true_eq_false, false_and,
    and_false, decide_false, Bool.false_eq_true, ↓reduceIte]
  rw [List.filter_eq_self.mpr (by simpa using hu), List.filter_eq_self.mpr (by simpa using hv)]

end CyclicBlock

namespace Diagram

variable {R S D : Type*} {P : InvolutionPresentation R S}

/-- The two selected occurrences have the same edge label; their tails
are read in the order of `CyclicBlock.formPerm_join`. -/
def joinLabelledBlocks (label : D → S) {a b : D} {u v : List D}
    (hab : label a = label b)
    (d : Diagram P ((a :: u).map label) []) (e : Diagram P ((b :: v).map label) []) :
    Diagram P ((u ++ v).map label) [] :=
  let e' : Diagram P (label a :: v.map label) [] := e.cast (by simp [hab]) rfl
  (d.glueFirst e').cast (by simp) rfl

theorem labels_joinLabelledBlocks (label : D → S) {a b : D} {u v : List D}
    (hab : label a = label b)
    (d : Diagram P ((a :: u).map label) []) (e : Diagram P ((b :: v).map label) []) :
    (joinLabelledBlocks label hab d e).labels = d.labels ++ e.labels := by
  simp only [joinLabelledBlocks, labels_cast, labels_glueFirst]

end Diagram
end ThomGame.Pictures
