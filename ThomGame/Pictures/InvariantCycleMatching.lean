module

public import ThomGame.Pictures.FullCycleMatching
public import ThomGame.Pictures.InvariantEuler

/-!
# Closing the matching on a single invariant vertex orbit

A cyclic block need not contain every port in the ambient map. If its
ports are invariant under the edge involution, Euler saturation restricts
to those ports and gives the same relation-free matching diagram on the
literal filtered block word.
-/

@[expose] public section
namespace ThomGame.Pictures.CyclicBlock.IsCycleWord

open Equiv RibbonConnectivity

variable {D : Type*} [DecidableEq D] [Finite D] {r : Perm D} {w : List D}
    (h : IsCycleWord r w)

include h in
theorem rotation_mem_iff (x : D) : r x ∈ w ↔ x ∈ w := by
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ h.nonempty
  rw [h.mem_iff_sameCycle ha, h.mem_iff_sameCycle ha]
  have hx : r.SameCycle x (r x) := ⟨1, by simp⟩
  exact ⟨fun hr => hr.trans hx.symm, fun hr => hr.trans hx⟩

noncomputable def memberEnumeration : Fin w.length ≃ {x : D // x ∈ w} :=
  Equiv.ofBijective (fun i => ⟨w.get i, List.get_mem w i⟩) ⟨by
    intro i j he
    exact h.nodup.injective_get (congrArg Subtype.val he), by
    intro x
    obtain ⟨i, hi⟩ := List.get_of_mem x.property
    exact ⟨i, Subtype.ext hi⟩⟩

omit [Finite D] in
theorem memberEnumeration_list :
    (List.ofFn h.memberEnumeration).map Subtype.val = w := by
  rw [List.map_ofFn]
  exact List.ofFn_get w

include h in
theorem exists_filtered_diagram_of_invariant {R S : Type*} (P : InvolutionPresentation R S)
    (t : Perm D) (ht : Function.Involutive t) (label : D → S)
    (hl : ∀ x, label (t x) = label x)
    (hm : ∀ x, t x ∈ w ↔ x ∈ w)
    (hEuler : RotationEuler.count r t = 2 * Nat.card (Component r t)) :
    ∃ d : Diagram P ((w.filter (moving t)).map label) [], d.labels = [] := by
  classical
  let r' := r.subtypePerm h.rotation_mem_iff
  let t' := t.subtypePerm hm
  let e := h.memberEnumeration
  let q : Perm (Fin w.length) := (e.trans t').trans e.symm
  have hq (i : Fin w.length) : e (q i) = t' (e i) := e.apply_symm_apply _
  have hti : Function.Involutive t' := fun x => Subtype.ext (ht x.val)
  have hqi : Function.Involutive q := by
    intro i
    apply e.injective
    rw [hq, hq, hti]
  have hr (i : Fin w.length) : r' (e i) = e (finRotate _ i) := by
    apply Subtype.ext
    exact (h.rotation _ (List.get_mem w i)).trans (formPerm_get_next h.nodup i)
  have hE : RotationEuler.count (finRotate _) q =
      2 * Nat.card (Component (finRotate _) q) := by
    rw [RotationEuler.count_congr _ _ r' t' e hr (fun i => (hq i).symm),
      Nat.card_congr (componentCongrEquiv _ _ r' t' e hr (fun i => (hq i).symm))]
    exact RotationEuler.subtype_saturated r t (fun x => x ∈ w) h.rotation_mem_iff hm ht hEuler
  have hql (i : Fin w.length) : label (e (q i)).val = label (e i).val := by
    rw [hq]
    exact hl _
  obtain ⟨d, hd⟩ := ResidualMatching.exists_diagram_of_euler q hqi
    (fun i => label (e i).val) hql P hE
  have hmoving (x : {x : D // x ∈ w}) : moving t' x = moving t x.val := by
    simp only [moving, ne_eq, Subtype.ext_iff]
    rfl
  have hw : ResidualMatching.word q (fun i => label (e i).val) =
      (w.filter (moving t)).map label := by
    rw [ResidualMatching.word_transport q t' e hq (fun x => label x.val)]
    change ((List.ofFn e).filter (moving t')).map (label ∘ Subtype.val) = _
    rw [← List.map_map]
    have hmf : moving t' = moving t ∘ Subtype.val := funext hmoving
    rw [hmf, ← List.filter_map]
    rw [h.memberEnumeration_list]
  exact ⟨d.cast hw rfl, (Diagram.labels_cast _ _ _).trans hd⟩

end ThomGame.Pictures.CyclicBlock.IsCycleWord
