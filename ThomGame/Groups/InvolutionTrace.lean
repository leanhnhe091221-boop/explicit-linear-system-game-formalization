module

public import ThomGame.Groups.InvolutionRewriting
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.List.Count

/-!
# Explicit finite rewrite certificates and their relation characters

A certificate is a list of concrete moves. Validity compares each move's
source with the preceding state and checks the final state. Only the two
local syntactic relations are available. The sign is the sum of parities
of the actual relation occurrences, counting both insertion and deletion.
-/

@[expose] public section
namespace ThomGame.InvolutionDerivation

open scoped BigOperators

inductive Move (R S : Type*)
  | eraseSquare (l r : List S) (s : S) (a : ZMod 2)
  | insertSquare (l r : List S) (s : S) (a : ZMod 2)
  | eraseRelation (l r : List S) (i : R) (a : ZMod 2)
  | insertRelation (l r : List S) (i : R) (a : ZMod 2)

variable {R S : Type*} (P : InvolutionPresentation R S)

def Move.source : Move R S → State S
  | .eraseSquare l r s a => state (l ++ [s, s] ++ r) a
  | .insertSquare l r _ a => state (l ++ r) a
  | .eraseRelation l r i a => state (l ++ P.word i ++ r) a
  | .insertRelation l r i a => state (l ++ r) (P.parity i + a)

def Move.target : Move R S → State S
  | .eraseSquare l r _ a => state (l ++ r) a
  | .insertSquare l r s a => state (l ++ [s, s] ++ r) a
  | .eraseRelation l r i a => state (l ++ r) (P.parity i + a)
  | .insertRelation l r i a => state (l ++ P.word i ++ r) a

def Move.label : Move R S → Option R
  | .eraseSquare _ _ _ _ | .insertSquare _ _ _ _ => none
  | .eraseRelation _ _ i _ | .insertRelation _ _ i _ => some i

def Move.parity (m : Move R S) : ZMod 2 :=
  match m.label with
  | none => 0
  | some i => P.parity i

theorem Move.step (m : Move R S) : Step P (m.source P) (m.target P) := by
  cases m with
  | eraseSquare l r s a => exact Step.eraseSquare l r s a
  | insertSquare l r s a => exact Step.insertSquare l r s a
  | eraseRelation l r i a => exact Step.eraseRelation l r i a
  | insertRelation l r i a => exact Step.insertRelation l r i a

theorem Step.exists_move {u v : State S} (h : Step P u v) :
    ∃ m : Move R S, m.source P = u ∧ m.target P = v := by
  cases h with
  | eraseSquare l r s a => exact ⟨.eraseSquare l r s a, rfl, rfl⟩
  | insertSquare l r s a => exact ⟨.insertSquare l r s a, rfl, rfl⟩
  | eraseRelation l r i a => exact ⟨.eraseRelation l r i a, rfl, rfl⟩
  | insertRelation l r i a => exact ⟨.insertRelation l r i a, rfl, rfl⟩

theorem parity_self_add (a : ZMod 2) : a + a = 0 := by
  have h : ∀ a : ZMod 2, a + a = 0 := by decide +kernel
  exact h a

theorem Move.parity_target (m : Move R S) :
    Multiplicative.toAdd (m.target P).2 = m.parity P + Multiplicative.toAdd (m.source P).2 := by
  cases m with
  | eraseSquare l r s a => simp [Move.source, Move.target, Move.parity, Move.label, state]
  | insertSquare l r s a => simp [Move.source, Move.target, Move.parity, Move.label, state]
  | eraseRelation l r i a => rfl
  | insertRelation l r i a =>
    change a = P.parity i + (P.parity i + a)
    rw [← add_assoc, parity_self_add, zero_add]

def Valid : List (Move R S) → State S → State S → Prop
  | [], u, v => u = v
  | m :: ms, u, v => m.source P = u ∧ Valid ms (m.target P) v

theorem valid_steps {ms : List (Move R S)} {u v : State S} (h : Valid P ms u v) : Steps P u v := by
  induction ms generalizing u with
  | nil =>
    change u = v at h
    subst v
    exact Relation.ReflTransGen.refl
  | cons m ms ih =>
    rcases h with ⟨rfl, h⟩
    exact Relation.ReflTransGen.head (m.step P) (ih h)

theorem steps_exists_valid {u v : State S} (h : Steps P u v) :
    ∃ ms : List (Move R S), Valid P ms u v := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], rfl⟩
  | head hstep hrest ih =>
    obtain ⟨m, hs, ht⟩ := Step.exists_move P hstep
    obtain ⟨ms, hms⟩ := ih
    refine ⟨m :: ms, hs, ?_⟩
    rw [ht]
    exact hms

theorem steps_iff_exists_valid (u v : State S) :
    Steps P u v ↔ ∃ ms : List (Move R S), Valid P ms u v :=
  ⟨steps_exists_valid P, fun ⟨_, h⟩ => valid_steps P h⟩

def sign (ms : List (Move R S)) : ZMod 2 := (ms.map (Move.parity P)).sum

def relationUses (ms : List (Move R S)) : List R := ms.filterMap Move.label

theorem sign_eq_relation_sum (ms : List (Move R S)) :
    sign P ms = ((relationUses ms).map P.parity).sum := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    cases m <;> simp [sign, relationUses, Move.parity, Move.label] at ih ⊢ <;> exact ih

theorem valid_sign {ms : List (Move R S)} {u v : State S} (h : Valid P ms u v) :
    Multiplicative.toAdd v.2 = sign P ms + Multiplicative.toAdd u.2 := by
  induction ms generalizing u with
  | nil =>
    change u = v at h
    subst v
    simp [sign]
  | cons m ms ih =>
    rcases h with ⟨rfl, h⟩
    rw [ih h, m.parity_target P]
    simp [sign, add_assoc, add_left_comm]

theorem valid_word_sign {ms : List (Move R S)} {w : List S} {a : ZMod 2}
    (h : Valid P ms (state w 0) (state [] a)) : sign P ms = a := by
  have hh := valid_sign P h
  change a = sign P ms + 0 at hh
  simpa only [add_zero] using hh.symm

def character [DecidableEq R] (ms : List (Move R S)) (r : R) : ZMod 2 :=
  ((relationUses ms).count r : ℕ)

theorem sum_parities_eq_counts [Fintype R] [DecidableEq R] (rs : List R) :
    (rs.map P.parity).sum = ∑ r, (rs.count r : ZMod 2) * P.parity r := by
  induction rs with
  | nil => simp
  | cons i rs ih =>
    have hc (r : R) : ((i :: rs).count r : ZMod 2) = (if r = i then 1 else 0) + (rs.count r : ZMod 2) := by
      by_cases h : r = i
      · subst r
        simp [Nat.cast_add, add_comm]
      · have hi : i ≠ r := Ne.symm h
        simp [h, hi]
    simp only [List.map_cons, List.sum_cons, hc, add_mul, Finset.sum_add_distrib]
    rw [ih]
    simp

theorem sign_eq_character [Fintype R] [DecidableEq R] (ms : List (Move R S)) :
    sign P ms = ∑ r, character ms r * P.parity r := by
  rw [sign_eq_relation_sum]
  exact sum_parities_eq_counts P (relationUses ms)

theorem word_eq_iff_trace (w : List S) (a : ZMod 2) :
    (w.map (InvolutionPresentation.x P)).prod = (if a = 1 then InvolutionPresentation.J P else 1) ↔
      ∃ ms : List (Move R S), Valid P ms (state w 0) (state [] a) :=
  (word_eq_iff_steps P w a).trans (steps_iff_exists_valid P _ _)

theorem word_eq_iff_signed_trace (w : List S) (a : ZMod 2) :
    (w.map (InvolutionPresentation.x P)).prod = (if a = 1 then InvolutionPresentation.J P else 1) ↔
      ∃ ms : List (Move R S), Valid P ms (state w 0) (state [] a) ∧ sign P ms = a := by
  rw [word_eq_iff_trace]
  exact ⟨fun ⟨ms, h⟩ => ⟨ms, h, valid_word_sign P h⟩, fun ⟨ms, h, _⟩ => ⟨ms, h⟩⟩

instance stateDecidableEq [DecidableEq S] : DecidableEq (State S) := by
  letI : DecidableEq (FreeMonoid S) := fun u v =>
    decidable_of_iff (u.toList = v.toList) FreeMonoid.toList.injective.eq_iff
  infer_instance

def check [DecidableEq S] : List (Move R S) → State S → State S → Bool
  | [], u, v => decide (u = v)
  | m :: ms, u, v => decide (m.source P = u) && check ms (m.target P) v

theorem check_eq_true [DecidableEq S] (ms : List (Move R S)) (u v : State S) :
    check P ms u v = true ↔ Valid P ms u v := by
  induction ms generalizing u with
  | nil => simp [check, Valid]
  | cons m ms ih => simp [check, Valid, ih]

end ThomGame.InvolutionDerivation
