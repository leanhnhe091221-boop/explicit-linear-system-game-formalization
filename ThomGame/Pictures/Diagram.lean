module

public import ThomGame.Groups.InvolutionTrace

/-!
# Planar diagram syntax with ordered top and bottom boundaries

The primitives are parallel identity wires, a cup or cap joining two
adjacent equal labels, and a single relation vertex with its ordered ports.
Vertical and horizontal composition introduce no crossing primitive.
This file defines the syntax and its algebraic interpretation, not an
embedding into the plane or the constellation normalization theorem.
-/

@[expose] public section
namespace ThomGame.Pictures

open InvolutionDerivation
open scoped BigOperators

variable {R S : Type*} (P : InvolutionPresentation R S)

inductive Diagram : List S → List S → Type (max u_1 u_2)
  | identity (w : List S) : Diagram w w
  | cap (s : S) : Diagram [s, s] []
  | cup (s : S) : Diagram [] [s, s]
  | down (r : R) : Diagram (P.word r) []
  | up (r : R) : Diagram [] (P.word r)
  | comp {u v w : List S} (d : Diagram u v) (e : Diagram v w) : Diagram u w
  | tensor {u v w z : List S} (d : Diagram u v) (e : Diagram w z) : Diagram (u ++ w) (v ++ z)

namespace Diagram

variable {P} {u v w z : List S}

def labels : {u v : List S} → Diagram P u v → List R
  | _, _, .identity _ => []
  | _, _, .cap _ => []
  | _, _, .cup _ => []
  | _, _, .down r => [r]
  | _, _, .up r => [r]
  | _, _, .comp d e => d.labels ++ e.labels
  | _, _, .tensor d e => d.labels ++ e.labels

def size (d : Diagram P u v) : Nat := d.labels.length

def sign (d : Diagram P u v) : ZMod 2 := (d.labels.map P.parity).sum

theorem size_comp (d : Diagram P u v) (e : Diagram P v w) : (d.comp e).size = d.size + e.size := by
  simp [size, labels]

theorem size_tensor (d : Diagram P u v) (e : Diagram P w z) : (d.tensor e).size = d.size + e.size := by
  simp [size, labels]

theorem sign_comp (d : Diagram P u v) (e : Diagram P v w) : (d.comp e).sign = d.sign + e.sign := by
  simp [sign, labels]

theorem sign_tensor (d : Diagram P u v) (e : Diagram P w z) : (d.tensor e).sign = d.sign + e.sign := by
  simp [sign, labels]

def cast (d : Diagram P u v) {u' v' : List S} (hu : u = u') (hv : v = v') : Diagram P u' v' :=
  hu ▸ hv ▸ d

theorem labels_cast (d : Diagram P u v) {u' v' : List S} (hu : u = u') (hv : v = v') :
    (d.cast hu hv).labels = d.labels := by subst u'; subst v'; rfl

theorem sign_cast (d : Diagram P u v) {u' v' : List S} (hu : u = u') (hv : v = v') :
    (d.cast hu hv).sign = d.sign := by simp only [sign, labels_cast]

theorem size_cast (d : Diagram P u v) {u' v' : List S} (hu : u = u') (hv : v = v') :
    (d.cast hu hv).size = d.size := by simp only [size, labels_cast]

def context (d : Diagram P u v) (l r : List S) : Diagram P (l ++ u ++ r) (l ++ v ++ r) :=
  ((identity l).tensor d).tensor (identity r)

theorem labels_context (d : Diagram P u v) (l r : List S) : (d.context l r).labels = d.labels := by
  simp [context, labels]

theorem sign_context (d : Diagram P u v) (l r : List S) : (d.context l r).sign = d.sign := by
  simp only [sign, labels_context]

theorem size_context (d : Diagram P u v) (l r : List S) : (d.context l r).size = d.size := by
  simp only [size, labels_context]

def contextDown (d : Diagram P u []) (l r : List S) : Diagram P (l ++ u ++ r) (l ++ r) :=
  (d.context l r).cast rfl (by simp)

def contextUp (d : Diagram P [] v) (l r : List S) : Diagram P (l ++ r) (l ++ v ++ r) :=
  (d.context l r).cast (by simp) rfl

theorem labels_contextDown (d : Diagram P u []) (l r : List S) :
    (d.contextDown l r).labels = d.labels := by
  rw [contextDown, labels_cast, labels_context]

theorem labels_contextUp (d : Diagram P [] v) (l r : List S) :
    (d.contextUp l r).labels = d.labels := by
  rw [contextUp, labels_cast, labels_context]

/-- Every diagram gives a finite local rewrite sequence with exactly its vertex sign. -/
theorem steps (d : Diagram P u v) : Steps P (state u 0) (state v d.sign) := by
  induction d with
  | identity w =>
    change Steps P (state w 0) (state w 0)
    exact Relation.ReflTransGen.refl
  | cap s =>
    have h := Step.eraseSquare (P := P) [] [] s 0
    apply Relation.ReflTransGen.single
    simpa only [sign, labels, List.map_nil, List.sum_nil, List.nil_append, List.append_nil] using h
  | cup s =>
    have h := Step.insertSquare (P := P) [] [] s 0
    apply Relation.ReflTransGen.single
    simpa only [sign, labels, List.map_nil, List.sum_nil, List.nil_append, List.append_nil] using h
  | down r =>
    have h := Step.eraseRelation (P := P) [] [] r 0
    apply Relation.ReflTransGen.single
    simpa [sign, labels] using h
  | up r =>
    have h := Step.insertRelation (P := P) [] [] r (P.parity r)
    apply Relation.ReflTransGen.single
    simpa [sign, labels, parity_self_add] using h
  | @comp u v w d e ihd ihe =>
    have h := steps_mul_right P ihe (state [] d.sign)
    have hh : Steps P (state v d.sign) (state w (d.sign + e.sign)) := by
      simpa only [state_mul, List.append_nil, zero_add, add_comm] using h
    simpa only [sign_comp] using ihd.trans hh
  | tensor d e ihd ihe =>
    have h := steps_mul P ihd ihe
    simpa only [state_mul, zero_add, sign_tensor] using h

theorem boundary_eq (d : Diagram P u v) :
    (u.map (InvolutionPresentation.x P)).prod =
      (v.map (InvolutionPresentation.x P)).prod *
        (if d.sign = 1 then InvolutionPresentation.J P else 1) := by
  have h := (eval_eq_iff_steps P _ _).mpr d.steps
  simpa [eval_state] using h

def character [DecidableEq R] (d : Diagram P u v) (r : R) : ZMod 2 := (d.labels.count r : Nat)

theorem sign_eq_character [Fintype R] [DecidableEq R] (d : Diagram P u v) :
    d.sign = ∑ r, d.character r * P.parity r :=
  sum_parities_eq_counts P d.labels

end Diagram
end ThomGame.Pictures
