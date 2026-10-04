module

public import ThomGame.Pictures.FullCycleMatching
public import ThomGame.Pictures.EnumeratedCycleWord

/-!
# Restricting a diagram block to an invariant port subset

The block's ordered list is lifted position by position. Rotation,
moving-port filtering, and every relation occurrence are preserved.
The subset may contain other blocks as well.
-/

@[expose] public section
namespace ThomGame.Pictures

open Equiv CyclicBlock

namespace CyclicBlock

variable {D : Type*} [DecidableEq D] (w : List D) (M : D → Prop)
    (hm : ∀ x ∈ w, M x)

def subtypePorts : List (Subtype M) :=
  List.ofFn (fun i : Fin w.length => ⟨w.get i, hm _ (List.get_mem w i)⟩)

omit [DecidableEq D] in
theorem subtypePorts_map : (subtypePorts w M hm).map Subtype.val = w := by
  rw [subtypePorts, List.map_ofFn]
  exact List.ofFn_get w

omit [DecidableEq D] in
theorem mem_subtypePorts (x : Subtype M) : x ∈ subtypePorts w M hm ↔ x.val ∈ w := by
  rw [subtypePorts, List.mem_ofFn]
  constructor
  · rintro ⟨i, hi⟩
    have he := congrArg Subtype.val hi
    exact he ▸ List.get_mem w i
  · intro hx
    obtain ⟨i, hi⟩ := List.get_of_mem hx
    exact ⟨i, Subtype.ext hi⟩

theorem subtypePorts_cyclic {r : Perm D} (h : IsCycleWord r w)
    (hr : ∀ x, M (r x) ↔ M x) :
    IsCycleWord (r.subtypePerm hr) (subtypePorts w M hm) := by
  apply IsCycleWord.ofFn
  · intro i j he
    exact h.nodup.injective_get (congrArg Subtype.val he)
  · exact List.length_pos_iff.mpr h.nonempty
  · intro i
    apply Subtype.ext
    exact (h.rotation _ (List.get_mem w i)).trans (formPerm_get_next h.nodup i)

theorem subtypePorts_filtered_label {S : Type*} (t : Perm D)
    (ht : ∀ x, M (t x) ↔ M x) (label : D → S) :
    ((subtypePorts w M hm).filter (moving (t.subtypePerm ht))).map (fun x => label x.val) =
      (w.filter (moving t)).map label := by
  have hp : moving (t.subtypePerm ht) = moving t ∘ Subtype.val := by
    funext x
    simp only [moving, ne_eq, Subtype.ext_iff]
    rfl
  change ((subtypePorts w M hm).filter (moving (t.subtypePerm ht))).map
    (label ∘ Subtype.val) = _
  rw [← List.map_map, hp, ← List.filter_map, subtypePorts_map]

end CyclicBlock

namespace DiagramBlock

variable {R S D : Type*} [DecidableEq D] {P : InvolutionPresentation R S}
    {label : D → S} {r t : Perm D} (B : DiagramBlock P label r t)
    (M : D → Prop) (hr : ∀ x, M (r x) ↔ M x) (ht : ∀ x, M (t x) ↔ M x)
    (hm : ∀ x ∈ B.ports, M x)

def restrict : DiagramBlock P (fun x : Subtype M => label x.val)
    (r.subtypePerm hr) (t.subtypePerm ht) where
  ports := subtypePorts B.ports M hm
  cyclic := subtypePorts_cyclic B.ports M hm B.cyclic hr
  diagram := B.diagram.cast (subtypePorts_filtered_label B.ports M hm t ht label).symm rfl

theorem restrict_labels : (B.restrict M hr ht hm).diagram.labels = B.diagram.labels := by
  simp only [restrict, Diagram.labels_cast]

theorem restrict_mem (x : Subtype M) :
    x ∈ (B.restrict M hr ht hm).ports ↔ x.val ∈ B.ports :=
  mem_subtypePorts B.ports M hm x

end DiagramBlock
end ThomGame.Pictures
