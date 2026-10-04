module

public import ThomGame.Pictures.CyclicBlockWords
public import ThomGame.Pictures.EdgeContractionEuler

/-!
# Diagram witnesses attached to cyclic vertex blocks

Each block carries a genuine diagram on its moving ports. Cyclic shifts
preserve the complete relation list. Contracting an edge between two
blocks joins their diagrams and concatenates those relation lists;
every other block is transported unchanged.
-/

@[expose] public section
namespace ThomGame.Pictures

open Equiv CycleSurgery

namespace CyclicBlock

variable {D : Type*} [DecidableEq D]

def moving (t : Perm D) (x : D) : Bool := decide (t x ≠ x)

omit [DecidableEq D] in
theorem filter_isRotated {u v : List D} (h : u.IsRotated v) (p : D → Bool) :
    (u.filter p).IsRotated (v.filter p) := by
  obtain ⟨n, hn, rfl⟩ := List.isRotated_iff_mod.mp h
  rw [List.rotate_eq_drop_append_take hn, List.filter_append]
  have he : u.filter p = (u.take n).filter p ++ (u.drop n).filter p := by
    rw [← List.filter_append, List.take_append_drop]
  rw [he]
  exact List.isRotated_append

theorem moving_removed_away (t : Perm D) (ht : Function.Involutive t) (a x : D)
    (hxa : x ≠ a) (hxb : x ≠ t a) :
    moving (splice t a (t a)) x = moving t x := by
  have hta : t x ≠ a := fun he => hxb ((ht x).symm.trans (congrArg t he))
  have htb : t x ≠ t a := t.injective.ne hxa
  simp only [moving, splice_apply, swap_apply_of_ne_of_ne hta htb]

theorem filter_moving_away (t : Perm D) (ht : Function.Involutive t) (a : D)
    (w : List D) (ha : a ∉ w) (hb : t a ∉ w) :
    w.filter (moving (splice t a (t a))) = w.filter (moving t) := by
  apply List.filter_congr
  intro x hx
  exact moving_removed_away t ht a x (fun he => ha (he ▸ hx)) (fun he => hb (he ▸ hx))

end CyclicBlock

namespace Diagram

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}

theorem exists_cyclic_shift (d : Diagram P u []) (h : u.IsRotated v) :
    ∃ e : Diagram P v [], e.labels = d.labels := by
  obtain ⟨n, hn, rfl⟩ := List.isRotated_iff_mod.mp h
  let d' : Diagram P (u.take n ++ u.drop n) [] := d.cast (by simp) rfl
  refine ⟨(rotatePrefix (u.take n) (u.drop n) d').cast
    (List.rotate_eq_drop_append_take hn).symm rfl, ?_⟩
  rw [labels_cast, labels_rotatePrefix]
  exact labels_cast _ _ _

end Diagram

open CyclicBlock

variable {R S D : Type*} [DecidableEq D] (P : InvolutionPresentation R S)
    (label : D → S) (r t : Perm D)

structure DiagramBlock where
  ports : List D
  cyclic : IsCycleWord r ports
  diagram : Diagram P ((ports.filter (moving t)).map label) []

structure RootedBlock (a : D) where
  tail : List D
  cyclic : IsCycleWord r (a :: tail)
  diagram : Diagram P (((a :: tail).filter (moving t)).map label) []

variable {P label r t}

namespace DiagramBlock

theorem exists_rooted (B : DiagramBlock P label r t) (a : D) (ha : a ∈ B.ports) :
    ∃ C : RootedBlock P label r t a,
      B.ports.IsRotated (a :: C.tail) ∧ C.diagram.labels = B.diagram.labels := by
  obtain ⟨l, u, hports⟩ := List.mem_iff_append.mp ha
  have hr : B.ports.IsRotated (a :: (u ++ l)) := by
    rw [hports]
    simpa using (List.isRotated_append (l := l) (l' := a :: u))
  obtain ⟨d, hd⟩ := B.diagram.exists_cyclic_shift ((filter_isRotated hr (moving t)).map label)
  exact ⟨⟨u ++ l, B.cyclic.rotated hr, d⟩, hr, hd⟩

noncomputable def root (B : DiagramBlock P label r t) (a : D) (ha : a ∈ B.ports) :
    RootedBlock P label r t a := (B.exists_rooted a ha).choose

theorem root_rotated (B : DiagramBlock P label r t) (a : D) (ha : a ∈ B.ports) :
    B.ports.IsRotated (a :: (B.root a ha).tail) := (B.exists_rooted a ha).choose_spec.1

theorem root_labels (B : DiagramBlock P label r t) (a : D) (ha : a ∈ B.ports) :
    (B.root a ha).diagram.labels = B.diagram.labels := (B.exists_rooted a ha).choose_spec.2

def untouched (B : DiagramBlock P label r t) (ht : Function.Involutive t) (a : D)
    (ha : a ∉ B.ports) (hb : t a ∉ B.ports) :
    DiagramBlock P label (splice r a (t a)) (splice t a (t a)) where
  ports := B.ports
  cyclic := B.cyclic.untouched a (t a) ha hb
  diagram := B.diagram.cast (by rw [filter_moving_away t ht a B.ports ha hb]) rfl

theorem untouched_labels (B : DiagramBlock P label r t) (ht : Function.Involutive t) (a : D)
    (ha : a ∉ B.ports) (hb : t a ∉ B.ports) :
    (B.untouched ht a ha hb).diagram.labels = B.diagram.labels := by
  simp only [untouched, Diagram.labels_cast]

end DiagramBlock

namespace RootedBlock

variable [Finite D] {a : D} (A : RootedBlock P label r t a)
    (B : RootedBlock P label r t (t a)) (ht : Function.Involutive t)
    (hr : ¬ r.SameCycle a (t a))

include hr in
theorem tails_away : a ∉ A.tail ∧ t a ∉ A.tail ∧ a ∉ B.tail ∧ t a ∉ B.tail := by
  have hd := A.cyclic.disjoint B.cyclic List.mem_cons_self List.mem_cons_self hr
  exact ⟨(List.nodup_cons.mp A.cyclic.nodup).1,
    fun hx => hd (List.mem_cons_of_mem _ hx) List.mem_cons_self,
    fun hx => hd List.mem_cons_self (List.mem_cons_of_mem _ hx),
    (List.nodup_cons.mp B.cyclic.nodup).1⟩

include ht hr in
theorem merged_filter :
    (((a :: A.tail) ++ (t a :: B.tail)).filter (moving (splice t a (t a)))) =
      A.tail.filter (moving t) ++ B.tail.filter (moving t) := by
  obtain ⟨ha, hb, hc, hd⟩ := tails_away A B hr
  simp only [List.filter_append, List.filter_cons, moving, splice_apply, swap_apply_right,
    ht a, swap_apply_left, ne_self_iff_false, decide_false, Bool.false_eq_true, ↓reduceIte]
  exact congrArg₂ List.append (filter_moving_away t ht a A.tail ha hb)
    (filter_moving_away t ht a B.tail hc hd)

def merge (hl : label a = label (t a)) :
    DiagramBlock P label (splice r a (t a)) (splice t a (t a)) where
  ports := (a :: A.tail) ++ (t a :: B.tail)
  cyclic := A.cyclic.join B.cyclic hr
  diagram := by
    have hm : t a ≠ a := fun he => hr (he.symm.sameCycle r)
    let d : Diagram P ((a :: A.tail.filter (moving t)).map label) [] :=
      A.diagram.cast (by simp [moving, hm]) rfl
    let e : Diagram P ((t a :: B.tail.filter (moving t)).map label) [] :=
      B.diagram.cast (by simp [moving, ht a, hm.symm]) rfl
    exact (Diagram.joinLabelledBlocks label hl d e).cast
      (by rw [merged_filter A B ht hr]) rfl

theorem merge_labels (hl : label a = label (t a)) :
    (merge A B ht hr hl).diagram.labels = A.diagram.labels ++ B.diagram.labels := by
  simp only [merge, Diagram.labels_cast, Diagram.labels_joinLabelledBlocks]

end RootedBlock
end ThomGame.Pictures
