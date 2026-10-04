module

public import ThomGame.Groups.LambdaNormalization
public import ThomGame.Finite.InvolutionWords
public import ThomGame.Finite.InvolutionCyclic
public import ThomGame.Finite.WheelSystem
public import Mathlib.Data.Fintype.Option

/-!
# The paper's actual family of wheels

The ordinary wheels come from every normalized Λ relation with parity zero.
The distinguished final wheel comes from J and has parity one. `none` labels
that final wheel; a later numerical encoding places it after the ordinary
wheels, as in the supplied matrix files.
-/

@[expose] public section

namespace ThomGame.Construction

open scoped BigOperators

abbrev Ordinary := InvolutionWords.Generator Lambda.Generator
abbrev WheelIndex := Option (Fin Lambda.normalizedRelators.length)

/-- A parameterized selector keeps finite-sum proofs independent of evaluating
the large concrete normalized list. -/
def indexedSourceWord (rs : List (Word Lambda.Generator)) (j : Word Lambda.Generator) :
    Option (Fin rs.length) → Word Lambda.Generator
  | none => j
  | some i => rs[i.val]'i.isLt

def sourceWord : WheelIndex → Word Lambda.Generator :=
  indexedSourceWord Lambda.normalizedRelators Lambda.J

theorem sourceWord_some (i : Fin Lambda.normalizedRelators.length) :
    sourceWord (some i) = Lambda.normalizedRelators[i.val]'i.isLt := rfl

def wheelWord (r : WheelIndex) : List Ordinary := InvolutionWords.substitute (sourceWord r)

theorem sourceWord_nonempty (r : WheelIndex) : sourceWord r ≠ [] := by
  cases r with
  | none => decide
  | some i =>
    have h := (Lambda.mem_normalizedRelators Lambda.normalizedRelators[i]).mp
      (List.getElem_mem i.isLt)
    exact h.choose_spec.2.2

theorem sourceWord_cyclicallyReduced (r : WheelIndex) :
    FreeGroup.IsCyclicallyReduced (sourceWord r) := by
  cases r with
  | none => exact FreeGroup.IsCyclicallyReduced.singleton
  | some i =>
    exact Lambda.normalized_cyclicallyReduced _ (List.getElem_mem i.isLt)

theorem wheelWord_cyclicallyReduced (r : WheelIndex) :
    InvolutionWords.IsCyclicallyReduced (wheelWord r) :=
  InvolutionWords.substitute_cyclicallyReduced (sourceWord_cyclicallyReduced r)

theorem wheelWord_count_even (r : WheelIndex) (g : Ordinary) :
    Even ((wheelWord r).count g) := InvolutionWords.substitute_count_even _ _

theorem wheelWord_length_ge_four (r : WheelIndex) : 4 ≤ (wheelWord r).length := by
  rw [wheelWord, InvolutionWords.substitute_length]
  have h := sourceWord_nonempty r
  have hpos : 0 < (sourceWord r).length := List.length_pos_iff.mpr h
  omega

def wheelFamily : Wheel.Family WheelIndex Ordinary where
  size r := (wheelWord r).length
  size_ge_two r := by have := wheelWord_length_ge_four r; omega
  letter r j := (wheelWord r)[j]
  parity r := match r with | none => 1 | some _ => 0

theorem wheel_size_eq (r : WheelIndex) :
    wheelFamily.size r = 4 * (sourceWord r).length :=
  InvolutionWords.substitute_length (sourceWord r)

theorem wheel_size_none : wheelFamily.size none = 4 := rfl

theorem wheel_size_some (i : Fin Lambda.normalizedRelators.length) :
    wheelFamily.size (some i) = 4 * (Lambda.normalizedRelators[i.val]'i.isLt).length := by
  rw [wheel_size_eq, sourceWord_some]

theorem wheel_size_some_substitute (i : Fin Lambda.normalizedRelators.length) :
    wheelFamily.size (some i) =
      (InvolutionWords.substitute (Lambda.normalizedRelators[i.val]'i.isLt)).length := rfl

abbrev Row := wheelFamily.Row
abbrev Col := wheelFamily.Col

def system : SparseSystem Row Col := wheelFamily.system

/-- The published one-based identifier of an ordinary involution. -/
def ordinaryNumber (g : Ordinary) : Nat := 2 * g.1.val + (if g.2 then 2 else 1)

theorem final_word_numbers : (wheelWord none).map ordinaryNumber = [145, 146, 145, 146] := by
  decide

theorem final_letter_sum (x : Ordinary → ZMod 2) :
    ∑ j, x (wheelFamily.letter none j) = 0 := by
  change ∑ j : Fin 4, Wheel.doubledPair (x (72, false)) (x (72, true)) j = 0
  exact Wheel.sum_doubledPair _ _

/-- The actual sparse system constructed from Λ has no classical solution. -/
theorem no_solution : ¬ ∃ x, system.Satisfies x :=
  wheelFamily.no_solution_of_odd_zero_sum none rfl final_letter_sum

/-- The actual incidence game has no perfect deterministic strategy. -/
theorem no_perfect_deterministic : ¬ ∃ alice bob, system.PerfectDeterministic alice bob :=
  wheelFamily.no_perfect_of_odd_zero_sum none rfl final_letter_sum

end ThomGame.Construction
