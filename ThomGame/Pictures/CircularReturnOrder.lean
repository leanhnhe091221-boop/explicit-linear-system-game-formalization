module

public import ThomGame.Pictures.FinCirclePaths
public import ThomGame.Pictures.CircularPartition

/-!
# Circular intervals and genuine first-return paths

For two different numbered points, being the next marked point is
equivalent to having no marked point in the intervening open circular
interval. The forward implication checks every skipped successor; the
reverse implication constructs the path, including a possible wrap.
-/

@[expose] public section
namespace ThomGame.Pictures

open Equiv MarkedReturn

namespace FinCircle

variable {n : Nat} {p : Fin n → Prop}

theorem hit_of_no_between {x y : Fin n} (hne : x ≠ y)
    (h : ∀ z, sbtw x z y → ¬ p z) : Hit (finRotate n) p x y := by
  let : NeZero n := x.neZero
  by_cases hxy : x < y
  · exact hit_of_lt p x y hxy (fun z hxz hzy => h z (Fin.sbtw_iff.mpr (Or.inl ⟨hxz, hzy⟩)))
  · have hyx : y < x := lt_of_le_of_ne (le_of_not_gt hxy) (Ne.symm hne)
    apply hit_wrap
    · intro z hxz
      exact h z (Fin.sbtw_iff.mpr (Or.inr (Or.inr ⟨hyx, hxz⟩)))
    · intro z hzy
      exact h z (Fin.sbtw_iff.mpr (Or.inr (Or.inl ⟨hzy, hyx⟩)))

theorem no_between_of_hit {x y : Fin n} (h : Hit (finRotate n) p x y)
    (hy : p y) : ∀ z, sbtw x z y → ¬ p z := by
  induction h with
  | direct x =>
    intro z hxz
    let : NeZero n := x.neZero
    have hr := rotate_val x
    have hx := x.isLt
    have hz := z.isLt
    simp only [Fin.sbtw_iff, Fin.lt_def] at hxz
    split_ifs at hr <;> omega
  | @skip x y hx tail ih =>
    intro z hxz hpz
    let : NeZero n := x.neZero
    have hzy : (finRotate n x).val ≠ y.val := by
      intro he
      exact hx ((Fin.ext he).symm ▸ hy)
    have hzz : z.val ≠ (finRotate n x).val := by
      intro he
      exact hx (Fin.ext he ▸ hpz)
    have hznext : sbtw (finRotate n x) z y := by
      have hr := rotate_val x
      have hz := z.isLt
      have hy' := y.isLt
      simp only [Fin.sbtw_iff, Fin.lt_def] at hxz ⊢
      split_ifs at hr <;> omega
    exact ih hy z hznext hpz

theorem hit_iff_no_between {x y : Fin n} (hne : x ≠ y) (hy : p y) :
    Hit (finRotate n) p x y ↔ ∀ z, sbtw x z y → ¬ p z :=
  ⟨fun h => no_between_of_hit h hy, hit_of_no_between hne⟩

end FinCircle

namespace CircularPartition

variable {n : Nat}

theorem Follows.no_between {f : Perm (Fin n)} (h : Follows (finRotate n) f)
    (x z : Fin n) (hxz : f.SameCycle x z) : ¬ sbtw x z (f x) := by
  intro hz
  exact FinCircle.no_between_of_hit (h.at_self x) Perm.SameCycle.rfl.apply_right z hz hxz

/-- The direction of a permutation can be checked by its actual
successors and orbit membership, including singleton orbits. -/
theorem follows_of_no_between {f : Perm (Fin n)}
    (h : ∀ x z, f.SameCycle x z → ¬ sbtw x z (f x)) : Follows (finRotate n) f := by
  intro x y hxy
  by_cases hy : y = f y
  · have hsingle : ∀ z, f.SameCycle x z → z = y := by
      intro z hxz
      exact ((hxy.symm.trans hxz).eq_of_left hy.symm).symm
    have hr := hit_perm (finRotate n) (f.SameCycle x) ⟨y, hxy⟩
    have he := hsingle _ (perm (finRotate n) (f.SameCycle x) ⟨y, hxy⟩).property
    rw [he] at hr
    change Hit (finRotate n) (f.SameCycle x) y y at hr
    exact hy ▸ hr
  · apply FinCircle.hit_of_no_between hy
    intro z hyz hxz
    exact h y z (hxy.symm.trans hxz) hyz

end CircularPartition
end ThomGame.Pictures
