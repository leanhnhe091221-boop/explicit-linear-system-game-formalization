module

public import ThomGame.Finite.WordNormalization

/-!
# Cyclic adjacency of words

`CyclicChain` includes the edge from the final letter back to the first.
For signed free-group words the relation forbids inverse cancellation;
for words in involutions it is inequality of successive generators.
-/

@[expose] public section
namespace ThomGame

def CyclicChain {α : Type*} (R : α → α → Prop) (w : List α) : Prop :=
  w.IsChain R ∧ ∀ a ∈ w.getLast?, ∀ b ∈ w.head?, R a b

namespace CyclicChain

variable {α β : Type*} {R : α → α → Prop}

theorem append_comm (u v : List α) :
    CyclicChain R (u ++ v) ↔ CyclicChain R (v ++ u) := by
  by_cases hu : u = []
  · simp [hu]
  by_cases hv : v = []
  · simp [hv]
  simp only [CyclicChain, List.isChain_append,
    List.getLast?_append_of_ne_nil _ hu, List.getLast?_append_of_ne_nil _ hv,
    List.head?_append_of_ne_nil _ hu, List.head?_append_of_ne_nil _ hv]
  tauto

theorem rotate {w : List α} (h : CyclicChain R w) (k : Nat) :
    CyclicChain R (w.rotate k) := by
  rw [List.rotate_eq_drop_append_take_mod, append_comm, List.take_append_drop]
  exact h

theorem reverse {w : List α} (h : CyclicChain R w) :
    CyclicChain (fun a b => R b a) w.reverse := by
  refine ⟨?_, ?_⟩
  · simpa only [List.isChain_reverse] using h.1
  · simpa only [List.getLast?_reverse, List.head?_reverse] using
      (fun b hb a ha => h.2 a ha b hb)

theorem map {S : β → β → Prop} (f : α → β)
    (hf : ∀ a b, R a b → S (f a) (f b))
    {w : List α} (h : CyclicChain R w) : CyclicChain S (w.map f) := by
  refine ⟨List.isChain_map_of_isChain f hf h.1, ?_⟩
  intro a ha b hb
  simp only [List.getLast?_map, List.head?_map] at ha hb
  cases he : w.getLast? with
  | none => simp [he] at ha
  | some c =>
    cases hd : w.head? with
    | none => simp [hd] at hb
    | some d =>
      have ha' : f c = a := by simpa [he] using ha
      have hb' : f d = b := by simpa [hd] using hb
      rw [← ha', ← hb']
      exact hf c d (h.2 c he d hd)

end CyclicChain

namespace Word

variable {α : Type*}

theorem cyclicallyReduced_rotate {w : Word α} (h : FreeGroup.IsCyclicallyReduced w)
    (k : Nat) : FreeGroup.IsCyclicallyReduced (w.rotate k) :=
  CyclicChain.rotate h k

theorem cyclicallyReduced_inverse {w : Word α} (h : FreeGroup.IsCyclicallyReduced w) :
    FreeGroup.IsCyclicallyReduced (inverse w) := by
  simp only [inverse, FreeGroup.invRev, ← List.map_reverse]
  change CyclicChain _ (w.reverse.map fun a => (a.1, !a.2))
  apply CyclicChain.map _ _ (CyclicChain.reverse h)
  intro a b hab heq
  exact congrArg Bool.not (hab heq.symm).symm

end Word
end ThomGame
