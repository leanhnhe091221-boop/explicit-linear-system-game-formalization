module

public import ThomGame.Analysis.UnitaryHilbertSchmidt
public import ThomGame.Groups.LambdaNormalization

/-! Free/cyclic reduction, rotation and inversion preserve the actual normalized
Hilbert--Schmidt relator defect, with no quantitative loss. -/

@[expose] public section
namespace ThomGame.Analysis

variable {A : Type*} {d : ℕ}

theorem unitaryLength_eval_rotation (f : A → UnitaryMatrix d) (u v : Word A) :
    unitaryLength (Word.eval f (u ++ v)) = unitaryLength (Word.eval f (v ++ u)) := by
  simp only [Word.eval_append]
  have he : Word.eval f u * (Word.eval f v * Word.eval f u) * (Word.eval f u)⁻¹ =
      Word.eval f u * Word.eval f v := by group
  rw [← he, unitaryLength_conj]

theorem unitaryLength_eval_rotate (f : A → UnitaryMatrix d) (r : Word A) (k : ℕ) :
    unitaryLength (Word.eval f (r.rotate k)) = unitaryLength (Word.eval f r) := by
  rw [List.rotate_eq_drop_append_take_mod, unitaryLength_eval_rotation, List.take_append_drop]

theorem unitaryLength_eval_reduceCyclically [DecidableEq A]
    (f : A → UnitaryMatrix d) (r : Word A) :
    unitaryLength (Word.eval f (FreeGroup.reduceCyclically r)) = unitaryLength (Word.eval f r) := by
  let c := FreeGroup.reduceCyclically.conjugator r
  let v := FreeGroup.reduceCyclically r
  have hs := congrArg (Word.eval f)
    (FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically r)
  change Word.eval f (c ++ v ++ Word.inverse c) = Word.eval f r at hs
  simp only [Word.eval_append, Word.eval_inverse] at hs
  rw [← hs, unitaryLength_conj]

theorem unitaryLength_eval_canonical (f : Lambda.Generator → UnitaryMatrix d)
    (r : Word Lambda.Generator) :
    unitaryLength (Word.eval f (Lambda.canonical r)) = unitaryLength (Word.eval f r) := by
  let v := FreeGroup.reduceCyclically (FreeGroup.reduce r)
  let candidates := (List.range v.length).flatMap fun k =>
    [v.rotate k, (Word.inverse v).rotate k]
  have hbase : unitaryLength (Word.eval f v) = unitaryLength (Word.eval f r) := by
    dsimp [v]
    rw [unitaryLength_eval_reduceCyclically, Word.eval_reduce]
  have hcandidates : ∀ c ∈ candidates,
      unitaryLength (Word.eval f c) = unitaryLength (Word.eval f r) := by
    intro c hc
    obtain ⟨k, _, hk⟩ := List.mem_flatMap.mp hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · exact (unitaryLength_eval_rotate f v k).trans hbase
    · rw [unitaryLength_eval_rotate, Word.eval_inverse, unitaryLength_inv]
      exact hbase
  have hfold (xs : List (Word Lambda.Generator))
      (hx : ∀ c ∈ xs, unitaryLength (Word.eval f c) = unitaryLength (Word.eval f r))
      (initial : Word Lambda.Generator)
      (hi : unitaryLength (Word.eval f initial) = unitaryLength (Word.eval f r)) :
      unitaryLength (Word.eval f (xs.foldl (fun best candidate =>
        if Lambda.signedNumbers candidate < Lambda.signedNumbers best then candidate else best)
          initial)) = unitaryLength (Word.eval f r) := by
    induction xs generalizing initial with
    | nil => exact hi
    | cons c xs ih =>
      apply ih (fun c hc => hx c (List.mem_cons_of_mem _ hc))
      dsimp only
      split
      · exact hx c List.mem_cons_self
      · exact hi
  exact hfold candidates hcandidates v hbase

end ThomGame.Analysis
