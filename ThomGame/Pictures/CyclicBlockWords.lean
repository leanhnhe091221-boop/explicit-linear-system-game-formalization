module

public import ThomGame.Pictures.CyclicBlockSplicing
public import ThomGame.Pictures.OrbitEnumeration

/-!
# Actual cyclic words for vertex orbits

A cycle word lists one whole orbit without repetition and agrees with
the actual rotation on every listed port. Two such words meeting at a
port differ only by a cyclic shift. Target swaps join distinct cycle
words in the order already used by diagram splicing.
-/

@[expose] public section
namespace ThomGame.Pictures.CyclicBlock

open Equiv CycleSurgery

variable {D : Type*} [DecidableEq D]

structure IsCycleWord (r : Perm D) (w : List D) : Prop where
  nodup : w.Nodup
  nonempty : w ≠ []
  rotation : ∀ x ∈ w, r x = w.formPerm x

theorem formPerm_sameCycle {w : List D} (hw : w.Nodup) {a b : D}
    (ha : a ∈ w) (hb : b ∈ w) : w.formPerm.SameCycle a b := by
  cases w with
  | nil => cases ha
  | cons z w =>
    have from_head (x : D) (hx : x ∈ z :: w) : (z :: w).formPerm.SameCycle z x := by
      obtain ⟨i, hi, he⟩ := List.getElem_of_mem hx
      refine ⟨(i : Int), ?_⟩
      rw [zpow_natCast, List.formPerm_pow_apply_head z w hw]
      simpa only [Nat.mod_eq_of_lt hi] using he
    exact (from_head a ha).symm.trans (from_head b hb)

namespace IsCycleWord

variable {r : Perm D} {w v : List D} (h : IsCycleWord r w)

include h

theorem rotation_mem {x : D} (hx : x ∈ w) : r x ∈ w := by
  rw [h.rotation x hx]
  exact List.formPerm_apply_mem_of_mem hx

theorem pow_mem {x : D} (hx : x ∈ w) (n : Nat) : (r ^ n) x ∈ w := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply]
    exact h.rotation_mem ih

theorem pow_eq {x : D} (hx : x ∈ w) (n : Nat) : (r ^ n) x = (w.formPerm ^ n) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, h.rotation _ (h.pow_mem hx n), ih,
      pow_succ', Perm.mul_apply]

theorem rotated (hv : w.IsRotated v) : IsCycleWord r v where
  nodup := hv.nodup_iff.mp h.nodup
  nonempty he := h.nonempty (List.isRotated_nil_iff.mp (he ▸ hv))
  rotation x hx := (h.rotation x (hv.mem_iff.mpr hx)).trans
    (congrArg (fun p : Perm D => p x) (List.formPerm_eq_of_isRotated h.nodup hv))

variable [Finite D]

theorem mem_iff_sameCycle {a : D} (ha : a ∈ w) (x : D) : x ∈ w ↔ r.SameCycle a x := by
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := (formPerm_sameCycle h.nodup ha hx).exists_nat_pow_eq
    exact ⟨(n : Int), by rw [zpow_natCast, h.pow_eq ha n]; exact hn⟩
  · intro hx
    obtain ⟨n, rfl⟩ := hx.exists_nat_pow_eq
    exact h.pow_mem ha n

theorem sameCycle_of_mem {a b : D} (ha : a ∈ w) (hb : b ∈ w) : r.SameCycle a b :=
  (h.mem_iff_sameCycle ha b).mp hb

theorem disjoint (hv : IsCycleWord r v) {a b : D} (ha : a ∈ w) (hb : b ∈ v)
    (hab : ¬ r.SameCycle a b) : List.Disjoint w v := by
  intro x hx hy
  exact hab ((h.sameCycle_of_mem ha hx).trans (hv.sameCycle_of_mem hb hy).symm)

theorem rotated_of_common (hv : IsCycleWord r v) {a : D} (ha : a ∈ w) (hb : a ∈ v) :
    w.IsRotated v := by
  have hm (x : D) : x ∈ w ↔ x ∈ v :=
    (h.mem_iff_sameCycle ha x).trans (hv.mem_iff_sameCycle hb x).symm
  have he : w.formPerm = v.formPerm := by
    ext x
    by_cases hx : x ∈ w
    · exact (h.rotation x hx).symm.trans (hv.rotation x ((hm x).mp hx))
    · rw [List.formPerm_apply_of_notMem hx,
        List.formPerm_apply_of_notMem (fun hmem => hx ((hm x).mpr hmem))]
  rcases (List.formPerm_eq_formPerm_iff h.nodup hv.nodup).mp he with hr | ⟨hl, hl'⟩
  · exact hr
  · have singleton {l : List D} (hmem : a ∈ l) (hlen : l.length ≤ 1) : l = [a] := by
      cases l with
      | nil => cases hmem
      | cons x xs =>
        have hn : xs = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hlen; omega)
        subst xs
        exact congrArg (fun z => [z]) (List.mem_singleton.mp hmem).symm
    rw [singleton ha hl, singleton hb hl']

omit h in
theorem join {a b : D} {u v : List D}
    (hu : IsCycleWord r (a :: u)) (hv : IsCycleWord r (b :: v))
    (hab : ¬ r.SameCycle a b) :
    IsCycleWord (splice r a b) ((a :: u) ++ (b :: v)) := by
  have hd := hu.disjoint hv List.mem_cons_self List.mem_cons_self hab
  have hb : b ∉ a :: u := fun hm => hd hm List.mem_cons_self
  refine ⟨List.nodup_append.mpr ⟨hu.nodup, hv.nodup, ?_⟩, by simp, ?_⟩
  · intro x hx y hy he
    subst y
    exact hd hx hy
  intro x hx
  rw [formPerm_join a b u v hb, splice_apply, splice_apply]
  apply congrArg (swap a b)
  rcases List.mem_append.mp hx with hx | hx
  · rw [Perm.mul_apply, List.formPerm_apply_of_notMem (fun he => hd hx he)]
    exact hu.rotation x hx
  · have hrot : (b :: v).formPerm x ∈ b :: v := List.formPerm_apply_mem_of_mem hx
    rw [Perm.mul_apply, List.formPerm_apply_of_notMem (fun he => hd he hrot)]
    exact hv.rotation x hx

omit [Finite D] in
theorem untouched (a b : D) (ha : a ∉ w) (hb : b ∉ w) :
    IsCycleWord (splice r a b) w where
  nodup := h.nodup
  nonempty := h.nonempty
  rotation x hx := by
    have hxa : r x ≠ a := fun he => ha (he ▸ h.rotation_mem hx)
    have hxb : r x ≠ b := fun he => hb (he ▸ h.rotation_mem hx)
    rw [splice_apply, swap_apply_of_ne_of_ne hxa hxb]
    exact h.rotation x hx

end IsCycleWord
end ThomGame.Pictures.CyclicBlock
