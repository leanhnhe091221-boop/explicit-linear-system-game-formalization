module

public import ThomGame.Pictures.SpliceReturn
public import ThomGame.Pictures.CircularSeparation
public import ThomGame.Pictures.FinCirclePaths

/-!
# Merging adjacent boundary blocks does not interlace them

The proof uses the actual orbit relation of target transposition. For a
pair in different old orbits, only these two orbits are merged. Every
retained endpoint pair sees the adjacent seam points on the same side.
This is sufficient to exclude alternating new orbits after deletion.
The direction of the first-return permutation is a separate assertion.
-/

@[expose] public section
namespace ThomGame.Pictures.CircularPartition

open Equiv MarkedReturn CycleSurgery

variable {A : Type*} [DecidableEq A] [Finite A] [CircularOrder A]

namespace NonInterlacing

variable {f : Perm A} (h : NonInterlacing (sbtw : A → A → A → Prop) f)
variable {a b : A} (hab : ¬ f.SameCycle a b)

include h hab

/-- A distinct merged orbit remains on one side of an old endpoint
pair whenever that pair sees the two seam points on the same side. -/
theorem arc_join_iff {x y u v : A} (hxy : f.SameCycle x y)
    (hxu : ¬ (splice f a b).SameCycle x u)
    (huv : (splice f a b).SameCycle u v)
    (hseam : sbtw x a y ↔ sbtw x b y) : sbtw x u y ↔ sbtw x v y := by
  have hxz : ∀ z, (splice f a b).SameCycle u z → ¬ f.SameCycle x z := by
    intro z huz hxz
    exact hxu ((oldCycle_in_join f hab hxz).trans huz.symm)
  rcases (sameCycle_join_iff f hab u v).mp huv with huv' | ⟨hua, hvb⟩ | ⟨hub, hva⟩
  · exact h.arc_membership_iff hxy (hxz u Perm.SameCycle.rfl) huv'
  · exact (h.arc_membership_iff hxy (hxz u Perm.SameCycle.rfl) hua).trans
      (hseam.trans (h.arc_membership_iff hxy (hxz v huv) hvb).symm)
  · exact (h.arc_membership_iff hxy (hxz u Perm.SameCycle.rfl) hub).trans
      (hseam.symm.trans (h.arc_membership_iff hxy (hxz v huv) hva).symm)

theorem no_alternating_join_of_old_pair {u v x y : A}
    (huv : f.SameCycle u v) (hxy : (splice f a b).SameCycle x y)
    (hux : ¬ (splice f a b).SameCycle u x)
    (hseam : sbtw u a v ↔ sbtw u b v)
    (huxv : sbtw u x v) (huvy : sbtw u v y) : False := by
  have huyv := (h.arc_join_iff hab huv hux hxy hseam).mp huxv
  exact huyv.not_sbtw huvy.cyclic_left

/-- Restrict the actual spliced permutation to retained boundary points.
The hypothesis only concerns the circular positions of the two seam
points relative to retained endpoints. -/
theorem splice_restrict_of_arc_iff (p : A → Prop)
    (hseam : ∀ x y : Subtype p, sbtw x.val a y.val ↔ sbtw x.val b y.val) :
    NonInterlacing (fun x y z : Subtype p => sbtw x.val y.val z.val)
      (perm (splice f a b) p) := by
  intro u x v y huxv huvy huv hxy
  apply (sameCycle_iff (splice f a b) p u x).mpr
  have huv' := (sameCycle_iff (splice f a b) p u v).mp huv
  have hxy' := (sameCycle_iff (splice f a b) p x y).mp hxy
  by_contra hux
  by_cases huv0 : f.SameCycle u.val v.val
  · exact h.no_alternating_join_of_old_pair hab huv0 hxy' hux (hseam u v) huxv huvy
  by_cases hxy0 : f.SameCycle x.val y.val
  · have hxv : ¬ (splice f a b).SameCycle x.val v.val :=
      fun hxv => hux (huv'.trans hxv.symm)
    have hxvy : sbtw x.val v.val y.val := (huvy.cyclic_right.trans_left huxv).cyclic_left
    have hxyu : sbtw x.val y.val u.val := huxv.cyclic_left.trans_left huvy.cyclic_left
    exact h.no_alternating_join_of_old_pair hab hxy0 huv'.symm hxv (hseam x y) hxvy hxyu
  have merged : ∀ s t, (splice f a b).SameCycle s t → ¬ f.SameCycle s t →
      (splice f a b).SameCycle s a := by
    intro s t hst hst0
    rcases (sameCycle_join_iff f hab s t).mp hst with hst | ⟨hsa, _⟩ | ⟨hsb, _⟩
    · exact (hst0 hst).elim
    · exact oldCycle_in_join f hab hsa
    · exact (oldCycle_in_join f hab hsb).trans (joins f hab).symm
  exact hux ((merged _ _ huv' huv0).trans (merged _ _ hxy' hxy0).symm)

end NonInterlacing

section Numbered

variable {n : Nat}

/-- Adjacent numbered points lie on the same side of every endpoint
pair that omits them. This includes adjacency across the end of `Fin n`.
-/
theorem adjacent_arc_iff (a : Fin n) {x y : Fin n}
    (hxa : x ≠ a) (hxb : x ≠ finRotate n a)
    (hya : y ≠ a) (hyb : y ≠ finRotate n a) :
    sbtw x a y ↔ sbtw x (finRotate n a) y := by
  let : NeZero n := a.neZero
  have hxav : x.val ≠ a.val := fun he => hxa (Fin.ext he)
  have hxbv : x.val ≠ (finRotate n a).val := fun he => hxb (Fin.ext he)
  have hyav : y.val ≠ a.val := fun he => hya (Fin.ext he)
  have hybv : y.val ≠ (finRotate n a).val := fun he => hyb (Fin.ext he)
  have hr := FinCircle.rotate_val a
  have hx := x.isLt
  have hy := y.isLt
  simp only [Fin.sbtw_iff, Fin.lt_def]
  split_ifs at hr <;> omega

theorem NonInterlacing.splice_restrict_adjacent
    {f : Perm (Fin n)} (h : NonInterlacing (sbtw : Fin n → Fin n → Fin n → Prop) f)
    (a : Fin n) (hab : ¬ f.SameCycle a (finRotate n a)) :
    NonInterlacing (fun x y z : {x : Fin n // x ≠ a ∧ x ≠ finRotate n a} =>
        sbtw x.val y.val z.val)
      (perm (splice f a (finRotate n a)) (fun x => x ≠ a ∧ x ≠ finRotate n a)) := by
  apply h.splice_restrict_of_arc_iff hab
  intro x y
  exact adjacent_arc_iff a x.property.1 x.property.2 y.property.1 y.property.2

end Numbered
end ThomGame.Pictures.CircularPartition
