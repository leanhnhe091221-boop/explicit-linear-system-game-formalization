module

public import ThomGame.Pictures.CircuitPullback
public import ThomGame.Pictures.ClosedGluingCovers

/-!
# A circuit avoiding interface joints lies in one gluing input

Edge reversal preserves the original summand. Equality of incident
vertices preserves it at terminals. Consequently every circuit made
entirely of original terminals lies wholly in the left or right input,
where it pulls back with the same length and indexed ports.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv

variable {R S : Type*} {P : InvolutionPresentation R S} {w : List S}
  (G : PortGraph P [] w) (H : PortGraph P w [])

def compSide (x : (G.comp H).Dart) : Bool :=
  match (compPorts G H).symm x with
  | .inl _ => false
  | .inr _ => true

theorem compSide_left (x : G.Dart) : compSide G H (compLeftEmbedding G H x) = false := by
  change (match (compPorts G H).symm (compPorts G H (.inl x)) with
    | .inl _ => false | .inr _ => true) = false
  rw [Equiv.symm_apply_apply]

theorem compSide_right (x : H.Dart) : compSide G H (compRightEmbedding G H x) = true := by
  change (match (compPorts G H).symm (compPorts G H (.inr x)) with
    | .inl _ => false | .inr _ => true) = true
  rw [Equiv.symm_apply_apply]

theorem compSide_twin (x : (G.comp H).Dart) : compSide G H ((G.comp H).pairing.twin x) = compSide G H x := by
  obtain ⟨x, rfl⟩ := (compPorts G H).surjective x
  rw [twin_compPorts]
  rcases x with x | x
  · exact (compSide_left G H (G.pairing.twin x)).trans (compSide_left G H x).symm
  · exact (compSide_right G H (H.pairing.twin x)).trans (compSide_right G H x).symm

theorem compSide_of_terminal_vertex (x y : (G.comp H).Dart)
    (hx : (G.comp H).Terminal x) (he : x.vertex = y.vertex) : compSide G H x = compSide G H y := by
  cases x with
  | top i => exact i.elim0
  | bottom i => exact i.elim0
  | joint j side => exact hx.elim
  | hub h p =>
    cases y with
    | top i => exact i.elim0
    | bottom i => exact i.elim0
    | joint j side => cases he
    | hub k q =>
      have hh : h = k := Sum.inl.inj (Sum.inr.inj he)
      subst k
      cases h <;> rfl

theorem compSide_false_range (x : (G.comp H).Dart) (hx : compSide G H x = false) :
    x ∈ Set.range (compLeftEmbedding G H) := by
  obtain ⟨x, rfl⟩ := (compPorts G H).surjective x
  rcases x with x | x
  · exact ⟨x, rfl⟩
  · have he : true = false := (compSide_right G H x).symm.trans hx
    cases he

theorem compSide_true_range (x : (G.comp H).Dart) (hx : compSide G H x = true) :
    x ∈ Set.range (compRightEmbedding G H) := by
  obtain ⟨x, rfl⟩ := (compPorts G H).surjective x
  rcases x with x | x
  · have he : false = true := (compSide_left G H x).symm.trans hx
    cases he
  · exact ⟨x, rfl⟩

namespace SimpleCircuit

variable {G H} (C : (G.comp H).SimpleCircuit)
  (hT : ∀ i : Fin C.length, (G.comp H).Terminal (C.dart i))

include hT in
theorem compSide_constant (i : Fin C.length) : compSide G H (C.dart i) = compSide G H (C.dart 0) := by
  have hs (j : Fin C.length) : compSide G H (C.dart (finRotate C.length j)) = compSide G H (C.dart j) :=
    (compSide_of_terminal_vertex G H _ _ (hT _) (C.next_vertex j)).trans (compSide_twin G H (C.dart j))
  obtain ⟨m, hm⟩ := (finRotate_sameCycle (0 : Fin C.length) i).exists_nat_pow_eq
  rw [← hm]
  clear hm
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ', Perm.mul_apply, hs]
    exact ih

include hT in
theorem lies_in_one_input :
    (∀ i : Fin C.length, C.dart i ∈ Set.range (compLeftEmbedding G H)) ∨
      (∀ i : Fin C.length, C.dart i ∈ Set.range (compRightEmbedding G H)) := by
  cases hs : compSide G H (C.dart 0)
  · exact Or.inl (fun i => compSide_false_range G H _ ((C.compSide_constant hT i).trans hs))
  · exact Or.inr (fun i => compSide_true_range G H _ ((C.compSide_constant hT i).trans hs))

include hT in
theorem exists_input_circuit :
    (∃ D : G.SimpleCircuit, ∃ hlen : D.length = C.length,
      ∀ x : Fin D.length × Bool, compLeftEmbedding G H (D.port x) =
        C.port (finCongr hlen x.1, x.2)) ∨
    (∃ D : H.SimpleCircuit, ∃ hlen : D.length = C.length,
      ∀ x : Fin D.length × Bool, compRightEmbedding G H (D.port x) =
        C.port (finCongr hlen x.1, x.2)) := by
  rcases C.lies_in_one_input hT with hleft | hright
  · exact Or.inl ⟨C.pullback (compLeftEmbedding G H) (compLeftEmbedding_vertex G H)
      (compLeftEmbedding_twin G H) hleft, rfl,
      C.pullback_port (compLeftEmbedding G H) (compLeftEmbedding_vertex G H) (compLeftEmbedding_twin G H) hleft⟩
  · exact Or.inr ⟨C.pullback (compRightEmbedding G H) (compRightEmbedding_vertex G H)
      (compRightEmbedding_twin G H) hright, rfl,
      C.pullback_port (compRightEmbedding G H) (compRightEmbedding_vertex G H) (compRightEmbedding_twin G H) hright⟩

end SimpleCircuit
end ThomGame.Pictures.PortGraph
