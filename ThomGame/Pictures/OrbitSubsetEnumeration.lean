module

public import ThomGame.Pictures.OrbitEnumeration
public import ThomGame.Pictures.CircularSubsets
public import Mathlib.Data.List.OfFn

/-!
# An ordered enumeration of a retained part of one permutation orbit

Retained points are numbered in increasing iterate order from the given
base point. Their cyclic successor is the actual first-return map of the
original permutation. Empty retained sets are allowed.
-/

@[expose] public section
namespace ThomGame.Pictures.OrbitEnumeration

open Equiv MarkedReturn CircularPartition

variable {D : Type*} [Finite D] (f : Perm D) (a : D) (p : D → Prop)

def Retained (b : D) : Prop := f.SameCycle a b ∧ p b

noncomputable def retainedIndices (i : Fin (length f a)) : Prop := p (dart f a i)

noncomputable def retainedLength : Nat := Nat.card (Subtype (retainedIndices f a p))

noncomputable def indexToRetained :
    Subtype (retainedIndices f a p) ≃ Subtype (Retained f a p) :=
  Equiv.ofBijective (fun i => ⟨dart f a i.val, dart_sameCycle f a i.val, i.property⟩)
    ⟨fun _ _ h => Subtype.ext ((dart f a).injective (congrArg Subtype.val h)), by
      rintro ⟨b, hb, hp⟩
      obtain ⟨i, hi⟩ := (dart_range f a b).mpr hb
      refine ⟨⟨i, ?_⟩, Subtype.ext hi⟩
      change p (dart f a i)
      rwa [hi]⟩

noncomputable def retainedEnumeration :
    Fin (retainedLength f a p) ≃ Subtype (Retained f a p) :=
  (subsetEnumeration (retainedIndices f a p)).toEquiv.trans (indexToRetained f a p)

theorem retainedEnumeration_val (i : Fin (retainedLength f a p)) :
    (retainedEnumeration f a p i).val =
      dart f a (subsetEnumeration (retainedIndices f a p) i).val := rfl

theorem retainedEnumeration_injective :
    Function.Injective (fun i => (retainedEnumeration f a p i).val) :=
  Subtype.val_injective.comp (retainedEnumeration f a p).injective

theorem retainedEnumeration_range (b : D) :
    (∃ i, (retainedEnumeration f a p i).val = b) ↔ Retained f a p b := by
  constructor
  · rintro ⟨i, rfl⟩
    exact (retainedEnumeration f a p i).property
  · intro hb
    obtain ⟨i, hi⟩ := (retainedEnumeration f a p).surjective ⟨b, hb⟩
    exact ⟨i, congrArg Subtype.val hi⟩

theorem retainedEnumeration_return (i : Fin (retainedLength f a p)) :
    perm f (Retained f a p) (retainedEnumeration f a p i) =
      retainedEnumeration f a p (finRotate (retainedLength f a p) i) := by
  apply Subtype.ext
  let x := subsetEnumeration (retainedIndices f a p) i
  have hm : ∀ j, Retained f a p (dart f a j) ↔ retainedIndices f a p j :=
    fun j => ⟨And.right, fun hj => ⟨dart_sameCycle f a j, hj⟩⟩
  have hp := perm_preserved_of_commutes f (Retained f a p) (finRotate (length f a))
    (retainedIndices f a p) (dart f a) (fun j => (dart_next f a j).symm) hm x
  have hr := congrArg (fun z : Subtype (retainedIndices f a p) => dart f a z.val)
    (subsetEnumeration_return (retainedIndices f a p) i)
  exact hp.symm.trans hr

noncomputable def retainedList : List D :=
  List.ofFn (fun i => (retainedEnumeration f a p i).val)

theorem retainedList_length : (retainedList f a p).length = retainedLength f a p := List.length_ofFn

theorem mem_retainedList (b : D) : b ∈ retainedList f a p ↔ Retained f a p b := by
  rw [retainedList, List.mem_ofFn]
  exact retainedEnumeration_range f a p b

theorem retainedList_nodup : (retainedList f a p).Nodup := by
  apply List.nodup_ofFn.mpr
  exact retainedEnumeration_injective f a p

end ThomGame.Pictures.OrbitEnumeration
