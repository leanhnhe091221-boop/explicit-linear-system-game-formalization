module

public import ThomGame.Finite.InvolutionWords

/-!
# Evaluation of the substitution by pairs of involutions

The substitution on syntax agrees in every target group with assigning
the original generator g to (u_g v_g)^2. The square relations on u and v
are needed to interpret a reversed block as the inverse.
-/

@[expose] public section
namespace ThomGame.InvolutionWords

variable {α G : Type*} [Group G]

def generatorImage (f : Generator α → G) (g : α) : G := (f (g, false) * f (g, true)) ^ 2

theorem block_product (f : Generator α → G) (g : α) :
    ((block g).map f).prod = generatorImage f g := by
  simp [block, pair, generatorImage, pow_two, mul_assoc]

theorem letterBlock_product (f : Generator α → G) (hf : ∀ s, f s * f s = 1)
    (a : α × Bool) :
    ((letterBlock a).map f).prod =
      if a.2 then generatorImage f a.1 else (generatorImage f a.1)⁻¹ := by
  have hinv (s : Generator α) : (f s)⁻¹ = f s := inv_eq_of_mul_eq_one_left (hf s)
  rcases a with ⟨g, positive⟩
  cases positive <;>
    simp [letterBlock, block, pair, generatorImage, pow_two, mul_inv_rev, hinv, mul_assoc]

theorem substitute_product (f : Generator α → G) (hf : ∀ s, f s * f s = 1)
    (w : Word α) :
    ((substitute w).map f).prod = Word.eval (generatorImage f) w := by
  induction w with
  | nil => simp [substitute]
  | cons a w ih =>
    change ((letterBlock a ++ substitute w).map f).prod =
      Word.eval (generatorImage f) ([a] ++ w)
    rw [List.map_append, List.prod_append, letterBlock_product f hf,
      ih, Word.eval_append]
    congr 1
    simp [Word.eval, FreeGroup.lift_mk]

end ThomGame.InvolutionWords
