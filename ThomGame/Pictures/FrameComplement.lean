module

public import ThomGame.Pictures.Surgery
public import ThomGame.Pictures.DiagramBoundaryMoves

/-!
# Removing a typed hole from a closed diagram

Word cups and caps close the left or right wires of a rectangle. These
partial traces turn a frame with an outside filling into a diagram on the
opposite boundary of its hole. Every surrounding relation occurrence is
preserved. The construction uses only the existing planar syntax.
-/

@[expose] public section
namespace ThomGame.Pictures

variable {R S : Type*} {P : InvolutionPresentation R S}

namespace Diagram

variable {u v w : List S}

def traceLeft (w : List S) (d : Diagram P (w ++ u) (w ++ v)) : Diagram P u v :=
  ((((cupWord P w.reverse).tensor (identity u)).cast (by simp)
      (by simp [List.append_assoc])).comp
    ((identity w.reverse).tensor d)).comp
      (((capWord P w.reverse).tensor (identity v)).cast
        (by simp [List.append_assoc]) (by simp))

theorem labels_traceLeft (w : List S) (d : Diagram P (w ++ u) (w ++ v)) :
    (d.traceLeft w).labels = d.labels := by
  simp [traceLeft, labels_cast, labels, labels_cupWord, labels_capWord]

def traceRight (w : List S) (d : Diagram P (u ++ w) (v ++ w)) : Diagram P u v :=
  ((((identity u).tensor (cupWord P w)).cast (by simp)
      (by simp [List.append_assoc])).comp
    (d.tensor (identity w.reverse))).comp
      (((identity v).tensor (capWord P w)).cast
        (by simp [List.append_assoc]) (by simp))

theorem labels_traceRight (w : List S) (d : Diagram P (u ++ w) (v ++ w)) :
    (d.traceRight w).labels = d.labels := by
  simp [traceRight, labels_cast, labels, labels_cupWord, labels_capWord]

end Diagram

namespace Frame

variable {a b u v : List S}

def labels : {u v : List S} → Frame P a b u v → List R
  | _, _, .hole => []
  | _, _, .pre d c => d.labels ++ c.labels
  | _, _, .post c d => c.labels ++ d.labels
  | _, _, .left d c => d.labels ++ c.labels
  | _, _, .right c d => c.labels ++ d.labels

theorem labels_fill (c : Frame P a b u v) (d : Diagram P a b) :
    ((c.fill d).labels : Multiset R) = (c.labels : Multiset R) + d.labels := by
  induction c with
  | hole => simp [fill, labels]
  | pre e c ih => simp only [fill, labels, Diagram.labels, ← Multiset.coe_add, ih]; ac_rfl
  | post c e ih => simp only [fill, labels, Diagram.labels, ← Multiset.coe_add, ih]; ac_rfl
  | left e c ih => simp only [fill, labels, Diagram.labels, ← Multiset.coe_add, ih]; ac_rfl
  | right c e ih => simp only [fill, labels, Diagram.labels, ← Multiset.coe_add, ih]; ac_rfl

def complement : {u v : List S} → Frame P a b u v → Diagram P v u → Diagram P b a
  | _, _, .hole, d => d
  | _, _, .pre e c, d => c.complement (d.comp e)
  | _, _, .post c e, d => c.complement (e.comp d)
  | _, _, @Frame.left _ _ _ _ _ u _ _ z e c, d =>
      c.complement (((e.tensor (.identity z)).comp d).traceLeft u)
  | _, _, @Frame.right _ _ _ _ _ _ v w _ c e, d =>
      c.complement ((((Diagram.identity v).tensor e).comp d).traceRight w)

theorem labels_complement (c : Frame P a b u v) (d : Diagram P v u) :
    ((c.complement d).labels : Multiset R) = (c.labels : Multiset R) + d.labels := by
  induction c with
  | hole => simp [complement, labels]
  | pre e c ih =>
    simp only [complement, ih, labels, Diagram.labels, ← Multiset.coe_add]
    ac_rfl
  | post c e ih =>
    simp only [complement, ih, labels, Diagram.labels, ← Multiset.coe_add]
    ac_rfl
  | left e c ih =>
    simp only [complement, ih, labels, Diagram.labels_traceLeft, Diagram.labels,
      List.append_nil, ← Multiset.coe_add]
    ac_rfl
  | right c e ih =>
    simp only [complement, ih, labels, Diagram.labels_traceRight, Diagram.labels,
      List.nil_append, ← Multiset.coe_add]
    ac_rfl

def puncture (c : Frame P a b [] []) : Diagram P b a := c.complement (.identity [])

theorem labels_puncture (c : Frame P a b [] []) :
    c.puncture.labels.Perm c.labels := by
  apply Multiset.coe_eq_coe.mp
  simpa only [puncture, Diagram.labels, Multiset.coe_nil, add_zero] using
    c.labels_complement (.identity [])

end Frame
end ThomGame.Pictures
