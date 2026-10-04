module

public import ThomGame.Pictures.ResidualMatching
public import Mathlib.Data.List.Sort

/-!
# Increasing subset enumeration is literal position filtering

The increasing enumeration of selected finite indices yields exactly the
filtered original list, in the same order. This identifies the residual
matching word with the boundary carried by a contracted diagram block.
-/

@[expose] public section
namespace ThomGame.Pictures.CircularPartition

open scoped Classical

variable {n : Nat}

theorem subsetEnumeration_list (p : Fin n → Prop) :
    List.ofFn (fun i => (subsetEnumeration p i).val) =
      (List.finRange n).filter (fun i => p i) := by
  apply List.Pairwise.eq_of_mem_iff
    (List.pairwise_ofFn.mpr (subsetEnumeration_strictMono p))
    ((List.sortedLT_finRange n).pairwise.filter _)
  intro x
  simp only [List.mem_ofFn, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi⟩
    exact hi ▸ (subsetEnumeration p i).property
  · intro hx
    exact ⟨(subsetEnumeration p).symm ⟨x, hx⟩,
      congrArg Subtype.val ((subsetEnumeration p).apply_symm_apply ⟨x, hx⟩)⟩

theorem ofFn_subset_filter {A : Type*} (f : Fin n → A) (p : A → Bool) :
    List.ofFn (fun i => f (subsetEnumeration (fun j => p (f j) = true) i).val) =
      (List.ofFn f).filter p := by
  rw [List.ofFn_comp' _ f, subsetEnumeration_list]
  simp only [List.ofFn_eq_map, List.filter_map, Function.comp_def, Bool.decide_coe]

end ThomGame.Pictures.CircularPartition
