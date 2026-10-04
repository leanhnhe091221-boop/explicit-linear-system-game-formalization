module

public import ThomGame.Pictures.AdjacentFollows
public import ThomGame.Pictures.CircularCombination
public import Mathlib.Data.Fintype.Sort

/-!
# Increasing numbering of a retained boundary circle

Every retained subset, including the empty subset, has an increasing
finite enumeration. Under this enumeration the genuine first return of
the ambient circle is exactly `finRotate`. This makes the adjacent
deletion theorem reusable on the successively smaller circles.
-/

@[expose] public section
namespace ThomGame.Pictures.CircularPartition

open Equiv MarkedReturn CycleSurgery
open scoped Classical

variable {m n : Nat} {p : Fin n → Prop}

theorem increasing_return (e : Fin m ≃ Subtype p)
    (he : StrictMono (fun i => (e i).val)) (i : Fin m) :
    perm (finRotate n) p (e i) = e (finRotate m i) := by
  apply Subtype.ext
  exact (eq_perm_of_hit (finRotate n) p (e i) (e (finRotate m i)).property
    ((FinCircle.hit_image_next (fun i => (e i).val) he i).weaken (by
      intro z hz
      refine ⟨e.symm ⟨z, hz⟩, ?_⟩
      exact congrArg Subtype.val (e.apply_symm_apply ⟨z, hz⟩)))).symm

/-- The increasing enumeration is constructed from the actual subset,
not supplied as an extra existence hypothesis. -/
noncomputable def subsetEnumeration (p : Fin n → Prop) :
    Fin (Nat.card (Subtype p)) ≃o Subtype p :=
  monoEquivOfFin _ Fintype.card_eq_nat_card

theorem subsetEnumeration_strictMono (p : Fin n → Prop) :
    StrictMono (fun i => (subsetEnumeration p i).val) :=
  (subsetEnumeration p).strictMono

theorem subsetEnumeration_return (p : Fin n → Prop) (i : Fin (Nat.card (Subtype p))) :
    perm (finRotate n) p (subsetEnumeration p i) =
      subsetEnumeration p (finRotate _ i) :=
  increasing_return (subsetEnumeration p).toEquiv (subsetEnumeration_strictMono p) i

/-- Express a permutation of retained points in their increasing numeric
order. -/
noncomputable def renumber (e : Fin m ≃ Subtype p) (f : Perm (Subtype p)) : Perm (Fin m) :=
  (e.trans f).trans e.symm

theorem renumber_apply (e : Fin m ≃ Subtype p) (f : Perm (Subtype p)) (i : Fin m) :
    renumber e f i = e.symm (f (e i)) := rfl

theorem OrderedNoncrossing.renumber
    {f : Perm (Subtype p)}
    (h : OrderedNoncrossing (perm (finRotate n) p)
      (fun x y z : Subtype p => sbtw x.val y.val z.val) f)
    (e : Fin m ≃ Subtype p) (he : StrictMono (fun i => (e i).val)) :
    OrderedNoncrossing (finRotate m) (sbtw : Fin m → Fin m → Fin m → Prop)
      (renumber e f) := by
  apply h.transport e.symm
  · intro x
    have hr := increasing_return e he (e.symm x)
    simpa only [e.apply_symm_apply, e.symm_apply_apply] using
      (congrArg e.symm hr).symm
  · intro x
    simp only [renumber_apply, e.apply_symm_apply]
  · intro x y z
    have ho := strictMono_sbtw (fun i => (e i).val) he (e.symm x) (e.symm y) (e.symm z)
    simpa only [e.apply_symm_apply] using ho.symm

/-- One adjacent deletion, followed by the actual increasing numbering
of every remaining point, produces another ordered noncrossing
permutation on a numbered circle. -/
theorem OrderedNoncrossing.splice_restrict_renumber
    {f : Perm (Fin n)}
    (h : OrderedNoncrossing (finRotate n) (sbtw : Fin n → Fin n → Fin n → Prop) f)
    (a : Fin n) (p : Fin n → Prop) (ha : ¬ p a) (hb : ¬ p (finRotate n a)) :
    OrderedNoncrossing (finRotate (Nat.card (Subtype p)))
      (sbtw : Fin (Nat.card (Subtype p)) → Fin (Nat.card (Subtype p)) →
        Fin (Nat.card (Subtype p)) → Prop)
      (CircularPartition.renumber (subsetEnumeration p).toEquiv
        (perm (splice f a (finRotate n a)) p)) :=
  (h.splice_restrict_adjacent a p ha hb).renumber
    (subsetEnumeration p).toEquiv (subsetEnumeration_strictMono p)

end ThomGame.Pictures.CircularPartition
