module

public import ThomGame.Pictures.BlockReplacement

/-!
# A relation-free block for opposite equally labelled triangles

Contracting the shared edge concatenates the two actual vertex cycles.
When their remaining labels occur in opposite orders, the four moving
ports are filled by the genuine cap diagram. The two contracted ports
remain explicit fixed points of the pairing.
-/

@[expose] public section
namespace ThomGame.Pictures

open Equiv CyclicBlock CycleSurgery RibbonConnectivity
open scoped Classical

variable {R S D : Type*} [DecidableEq D] [Finite D]
  (P : InvolutionPresentation R S) (label : D → S) (r t : Perm D)
  (ht : Function.Involutive t) (hm : ∀ x, t x ≠ x)
  (a x y z v : D) (hA : IsCycleWord r [a, x, y]) (hB : IsCycleWord r [t a, z, v])
  (hr : ¬ r.SameCycle a (t a))

include ht hm hA hB hr in
theorem triangle_contracted_filter :
    ([a, x, y, t a, z, v].filter (moving (splice t a (t a)))) = [x, y, z, v] := by
  have hd := hA.disjoint hB (by simp) (by simp) hr
  have haa : a ∉ [x, y] := (List.nodup_cons.mp hA.nodup).1
  have hbb : t a ∉ [z, v] := (List.nodup_cons.mp hB.nodup).1
  have hab : t a ∉ [x, y] := fun h => hd (List.mem_cons_of_mem _ h) (by simp)
  have hba : a ∉ [z, v] := fun h => hd (by simp) (List.mem_cons_of_mem _ h)
  have hfilter (w : List D) : w.filter (moving t) = w := by
    apply List.filter_eq_self.mpr
    intro d _
    exact decide_eq_true (hm d)
  change ((a :: [x, y]) ++ (t a :: [z, v])).filter (moving (splice t a (t a))) = _
  rw [List.filter_append]
  have hfa : moving (splice t a (t a)) a = false := by simp [moving, splice_apply]
  have hfb : moving (splice t a (t a)) (t a) = false := by simp [moving, splice_apply, ht a]
  have hfa' : ¬ moving (splice t a (t a)) a = true := by rw [hfa]; decide
  have hfb' : ¬ moving (splice t a (t a)) (t a) = true := by rw [hfb]; decide
  rw [List.filter_cons_of_neg hfa', List.filter_cons_of_neg hfb']
  rw [filter_moving_away t ht a [x, y] haa hab, filter_moving_away t ht a [z, v] hba hbb,
    hfilter, hfilter]
  rfl

noncomputable def triangleCancellationBlock (hx : label x = label v) (hy : label y = label z) :
    DiagramBlock P label (splice r a (t a)) (splice t a (t a)) where
  ports := [a, x, y, t a, z, v]
  cyclic := hA.join hB hr
  diagram := (Diagram.capWord P [label x, label y]).cast (by
    rw [triangle_contracted_filter r t ht hm a x y z v hA hB hr]
    simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, hx, hy]) rfl

theorem triangleCancellationBlock_labels (hx : label x = label v) (hy : label y = label z) :
    (triangleCancellationBlock P label r t ht hm a x y z v hA hB hr hx hy).diagram.labels = [] := by
  simp only [triangleCancellationBlock, Diagram.labels_cast, Diagram.labels_capWord]

end ThomGame.Pictures
