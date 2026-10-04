module

public import ThomGame.Pictures.BlockFamily
public import ThomGame.Pictures.EdgeContractionTrace

/-!
# Assembling all block diagrams along an actual contraction trace

The entire finite family is carried through each contraction step. Its
relation multiset is preserved exactly, including multiplicities. No
graph realization or relation-count premise is substituted for the
constructed diagram witnesses at the terminal blocks.
-/

@[expose] public section
namespace ThomGame.Pictures

open Equiv CycleSurgery RotationEuler

namespace EdgeContraction

variable {R S D : Type*} [DecidableEq D] [Finite D]
    {P : InvolutionPresentation R S} {label : D → S}
    {r t r' t' : Perm D} {k : Nat}

theorem exists_blockFamily (c : EdgeContraction r t r' t' k) :
    Function.Involutive t → (∀ x, label (t x) = label x) →
      ∀ F : BlockFamily P label r t,
        ∃ F' : BlockFamily P label r' t', F'.relations = F.relations := by
  induction c with
  | refl => intro _ _ F; exact ⟨F, rfl⟩
  | @step r t r' t' k a hr tail ih =>
    intro ht hl F
    have hl' (x : D) : label (splice t a (t a) x) = label x := by
      rcases removed_pair_value t ht a x with hx | hx
      · rw [hx]
      · rw [hx, hl]
    obtain ⟨F', hF'⟩ := ih (removed_pair_involutive t ht a) hl' (F.merge ht hl a hr)
    exact ⟨F', hF'.trans (F.merge_relations ht hl a hr)⟩

end EdgeContraction

namespace BlockFamily

variable {R S D : Type*} [DecidableEq D] [Finite D]
    {P : InvolutionPresentation R S} {label : D → S} {r t : Perm D}

theorem exists_terminal (F : BlockFamily P label r t) (ht : Function.Involutive t)
    (hl : ∀ x, label (t x) = label x) :
    ∃ r' t' k, ∃ (_c : EdgeContraction r t r' t' k) (F' : BlockFamily P label r' t'),
      (∀ a, r'.SameCycle a (t' a)) ∧ F'.relations = F.relations := by
  obtain ⟨r', t', k, ⟨c⟩, hterm⟩ := EdgeContraction.exists_terminal r t ht
  obtain ⟨F', hF'⟩ := c.exists_blockFamily ht hl F
  exact ⟨r', t', k, c, F', hterm, hF'⟩

end BlockFamily
end ThomGame.Pictures
