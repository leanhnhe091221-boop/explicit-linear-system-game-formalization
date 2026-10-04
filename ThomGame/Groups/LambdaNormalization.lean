module

public import ThomGame.Groups.LambdaPresentation
public import ThomGame.Finite.WordNormalization
public import ThomGame.Finite.CyclicWords
public import ThomGame.Finite.EraseReps
public import ThomGame.Finite.PresentedWords

/-!
# Correctness of canonicalizing an individual Λ relation

The proof is uniform over all target groups and all input words. It is
independent of the executable comparison with the archived word list.
-/

@[expose] public section

namespace ThomGame.Lambda

private theorem fold_choose_preserves {α : Type*} (pick : α → α → α) (P : α → Prop)
    (hpick : ∀ a b, P a → P b → P (pick a b))
    (xs : List α) (initial : α) (hi : P initial) (hx : ∀ x ∈ xs, P x) :
    P (xs.foldl pick initial) := by
  induction xs generalizing initial with
  | nil => exact hi
  | cons x xs ih =>
    apply ih (pick initial x) (hpick initial x hi (hx x (by simp)))
    intro y hy
    exact hx y (by simp [hy])

theorem canonical_eval_eq_one_iff {G : Type*} [Group G]
    (f : Generator → G) (r : Word Generator) :
    Word.eval f (canonical r) = 1 ↔ Word.eval f r = 1 := by
  let v := FreeGroup.reduceCyclically (FreeGroup.reduce r)
  let candidates := (List.range v.length).flatMap fun k ↦
    [v.rotate k, (Word.inverse v).rotate k]
  have hbase : Word.eval f v = 1 ↔ Word.eval f r = 1 := by
    dsimp [v]
    rw [Word.eval_reduceCyclically_eq_one_iff, Word.eval_reduce]
  have hcandidates : ∀ c ∈ candidates, Word.eval f c = 1 ↔ Word.eval f r = 1 := by
    intro c hc
    obtain ⟨k, _, hk⟩ := List.mem_flatMap.mp hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · exact (Word.eval_rotate_eq_one_iff f v k).trans hbase
    · rw [Word.eval_rotate_eq_one_iff, Word.eval_inverse, inv_eq_one]
      exact hbase
  apply fold_choose_preserves
    (fun best candidate ↦ if signedNumbers candidate < signedNumbers best then candidate else best)
    (fun c ↦ Word.eval f c = 1 ↔ Word.eval f r = 1) _ candidates v hbase hcandidates
  intro a b ha hb
  split <;> assumption

/-- Exact membership characterization, including deletion of the empty relator. -/
theorem mem_normalizedRelators (s : Word Generator) :
    s ∈ normalizedRelators ↔ ∃ r ∈ rawRelators, canonical r = s ∧ s ≠ [] := by
  rw [normalizedRelators, mem_eraseReps, KernelSort.mem_sort]
  constructor
  · intro hs
    obtain ⟨hmap, hnonempty⟩ := List.mem_filter.mp hs
    obtain ⟨r, hr, heq⟩ := List.mem_map.mp hmap
    refine ⟨r, hr, heq, ?_⟩
    intro hempty
    simp [hempty] at hnonempty
  · rintro ⟨r, hr, rfl, hnonempty⟩
    apply List.mem_filter.mpr
    exact ⟨List.mem_map.mpr ⟨r, hr, rfl⟩, by simpa using hnonempty⟩

/-- The normalizer produces cyclically reduced words, including when its
lexicographic minimum is an inverse rotation of the initial reduction. -/
theorem canonical_cyclicallyReduced (r : Word Generator) :
    FreeGroup.IsCyclicallyReduced (canonical r) := by
  let v := FreeGroup.reduceCyclically (FreeGroup.reduce r)
  have hv : FreeGroup.IsCyclicallyReduced v :=
    FreeGroup.reduceCyclically.isCyclicallyReduced
      (FreeGroup.IsReduced.of_reduce_eq (FreeGroup.reduce.idem (L := r)))
  refine fold_choose_preserves
    (fun best candidate ↦ if signedNumbers candidate < signedNumbers best then candidate else best)
    FreeGroup.IsCyclicallyReduced ?_ _ v hv ?_
  · intro a b ha hb
    split <;> assumption
  · intro c hc
    obtain ⟨k, _, hk⟩ := List.mem_flatMap.mp hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · exact Word.cyclicallyReduced_rotate hv k
    · exact Word.cyclicallyReduced_rotate (Word.cyclicallyReduced_inverse hv) k

theorem normalized_cyclicallyReduced (s : Word Generator) (hs : s ∈ normalizedRelators) :
    FreeGroup.IsCyclicallyReduced s := by
  obtain ⟨r, _, rfl, _⟩ := (mem_normalizedRelators s).mp hs
  exact canonical_cyclicallyReduced r

/-- Every group assignment satisfies precisely the same relations before and
after canonicalization, sorting, removal of empty words, and deduplication. -/
theorem all_normalized_iff_all_raw {G : Type*} [Group G] (f : Generator → G) :
    (∀ r ∈ normalizedRelators, Word.eval f r = 1) ↔
      (∀ r ∈ rawRelators, Word.eval f r = 1) := by
  constructor
  · intro hn r hr
    apply (canonical_eval_eq_one_iff f r).mp
    by_cases hc : canonical r = []
    · simp [hc]
    · exact hn (canonical r) ((mem_normalizedRelators _).mpr ⟨r, hr, rfl, hc⟩)
  · intro hr s hs
    obtain ⟨r, hmem, rfl, _⟩ := (mem_normalizedRelators s).mp hs
    exact (canonical_eval_eq_one_iff f r).mpr (hr r hmem)

/-- Canonicalization generates exactly the same normal subgroup of the free group. -/
theorem normalClosure_eq :
    Subgroup.normalClosure rawRelationSet = Subgroup.normalClosure normalizedRelationSet := by
  have satisfies (rs : List (Word Generator)) :
      ∀ r ∈ rs, Word.eval
        (PresentedGroup.of (rels := FreeGroup.mk '' {w | w ∈ rs})) r = 1 := by
    intro r hr
    rw [Word.eval_presented]
    exact PresentedGroup.one_of_mem ⟨r, hr, rfl⟩
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨r, hr, rfl⟩
    apply PresentedGroup.mk_eq_one_iff.mp
    rw [← Word.eval_presented]
    exact (all_normalized_iff_all_raw _).mp (satisfies normalizedRelators) r hr
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨r, hr, rfl⟩
    apply PresentedGroup.mk_eq_one_iff.mp
    rw [← Word.eval_presented]
    exact (all_normalized_iff_all_raw _).mpr (satisfies rawRelators) r hr

/-- The explicit equivalence between the raw and normalized presented groups. -/
def normalizationEquiv : GroupLambda ≃* NormalizedGroupLambda :=
  QuotientGroup.congr _ _ (MulEquiv.refl _) (by simpa using normalClosure_eq)

/-- The equivalence fixes each generator, in particular the specified J. -/
theorem normalizationEquiv_of (g : Generator) :
    normalizationEquiv (PresentedGroup.of (rels := rawRelationSet) g) =
      PresentedGroup.of (rels := normalizedRelationSet) g := by
  rfl

end ThomGame.Lambda
