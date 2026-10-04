module

public import ThomGame.Finite.Words
public import Mathlib.Algebra.Group.Subgroup.Finite

/-! A word in subgroup generators evaluates in that subgroup, for either sign. -/

@[expose] public section
namespace ThomGame.Word

theorem eval_mem {α G : Type*} [Group G] (H : Subgroup G) (f : α → G) (w : Word α)
    (hw : ∀ a ∈ w, f a.1 ∈ H) : eval f w ∈ H := by
  rw [eval, FreeGroup.lift_mk]
  apply H.list_prod_mem
  intro x hx
  obtain ⟨⟨g, b⟩, ha, rfl⟩ := List.mem_map.mp hx
  cases b with
  | false => exact H.inv_mem (hw _ ha)
  | true => exact hw _ ha

end ThomGame.Word
