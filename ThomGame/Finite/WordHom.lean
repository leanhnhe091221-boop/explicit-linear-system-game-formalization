module

public import ThomGame.Finite.Words

/-! Word evaluation commutes with group homomorphisms. -/

@[expose] public section
namespace ThomGame.Word

theorem eval_map_generators {α β G : Type*} [Group G]
    (f : β → G) (σ : α → β) (w : Word α) :
    eval f (w.map (fun a => (σ a.1, a.2))) = eval (fun a => f (σ a)) w := by
  simp [eval, FreeGroup.lift_mk, List.map_map, Function.comp_def]

theorem map_eval {α G H : Type*} [Group G] [Group H]
    (φ : G →* H) (f : α → G) (w : Word α) :
    φ (eval f w) = eval (fun a => φ (f a)) w := by
  have h : φ.comp (FreeGroup.lift f) = FreeGroup.lift (fun a => φ (f a)) := by
    apply FreeGroup.ext_hom
    intro a
    simp
  exact DFunLike.congr_fun h (FreeGroup.mk w)

end ThomGame.Word
