module

public import ThomGame.Groups.CompressorChecks
public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
public import Mathlib.Data.List.Lex
public import Mathlib.Data.List.Sort
public import ThomGame.Finite.KernelSort

/-!
# The raw and canonical finite presentations of Λ

All `Fin 74` values are zero-based internally. Exported signed integers are
one-based, so `J` has number 73 and `z` has number 74.

The definitions here specify the group and its deterministic normalization.
The identification of the raw presentation with the HNN construction and
the equivalence of the normalized presentation are separate proof obligations.
-/

@[expose] public section

namespace ThomGame.Lambda

abbrev Generator := Fin 74

/-- One-based map from the two Q generator lists into the amalgam's 72 generators. -/
def copyNumber (second : Bool) : Compressor.Generator → Nat
  | .inl (r, none) => 4 * Compressor.roots.idxOf r + 1
  | .inl (r, some (c, true)) => 4 * Compressor.roots.idxOf r + c.val + 2
  | .inl (r, some (c, false)) =>
      (if second then 48 else 24) + 3 * Compressor.roots.idxOf r + c.val + 1
  | .inr r => (if second then 48 else 24) + 19 + Compressor.roots.idxOf r

theorem copyNumber_range :
    ∀ second g, 1 ≤ copyNumber second g ∧ copyNumber second g ≤ 72 := by decide +kernel

def copyGenerator (second : Bool) (g : Compressor.Generator) : Generator :=
  ⟨copyNumber second g - 1, by have := copyNumber_range second g; omega⟩

def copyWord (second : Bool) (w : Word Compressor.Generator) : Word Generator :=
  w.map fun (g, positive) ↦ (copyGenerator second g, positive)

def h : Word Generator := Word.generator 2
def t₁ : Word Generator := Word.generator 42
def t₂ : Word Generator := Word.generator 66
def J : Word Generator := Word.generator 72
def z : Word Generator := Word.generator 73

def w : Word Generator := Word.commutator h (t₂ ++ Word.inverse t₁)

def amalgamGenerators : List Generator :=
  (List.finRange 72).map fun g ↦ g.castLE (by decide : 72 ≤ 74)

def rawRelators : List (Word Generator) :=
  Compressor.rawRelators.map (copyWord false) ++
  Compressor.rawRelators.map (copyWord true) ++
  [J ++ J] ++
  amalgamGenerators.map (fun g ↦ Word.commutator J (Word.generator g)) ++
  [Word.commutator J z,
   Word.equation (z ++ w ++ Word.inverse z) (w ++ J)]

def rawRelationSet : Set (FreeGroup Generator) := FreeGroup.mk '' {r | r ∈ rawRelators}

def GroupLambda := PresentedGroup rawRelationSet
  deriving Group

def signedNumbers (r : Word Generator) : List Int :=
  r.map fun (g, positive) ↦ if positive then (g.val + 1 : Nat) else -(g.val + 1 : Int)

/-- Lexicographic minimization over cyclic rotations and inverse rotations,
after free and cyclic reduction. -/
def canonical (r : Word Generator) : Word Generator :=
  let v := FreeGroup.reduceCyclically (FreeGroup.reduce r)
  let candidates := (List.range v.length).flatMap fun k ↦
    [v.rotate k, (Word.inverse v).rotate k]
  candidates.foldl (fun best candidate ↦
    if signedNumbers candidate < signedNumbers best then candidate else best) v

/-- Sorting before removing consecutive duplicates avoids quadratic deduplication. -/
def normalizedRelators : List (Word Generator) :=
  (KernelSort.sort (fun a b ↦ decide (signedNumbers a ≤ signedNumbers b))
    ((rawRelators.map canonical).filter fun r ↦ !r.isEmpty)).eraseReps

def normalizedRelationSet : Set (FreeGroup Generator) :=
  FreeGroup.mk '' {r | r ∈ normalizedRelators}

def NormalizedGroupLambda := PresentedGroup normalizedRelationSet
  deriving Group

set_option maxRecDepth 60000 in
set_option maxHeartbeats 4000000 in
theorem raw_relator_count : rawRelators.length = 15533 := by decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 8000000 in
theorem raw_relator_total_length : (rawRelators.map List.length).sum = 137733 := by decide +kernel

theorem obstruction_word_numbers : signedNumbers w = [3, 67, -43, -3, 43, -67] := by decide
theorem central_generator_number : signedNumbers J = [73] := by decide
theorem stable_letter_number : signedNumbers z = [74] := by decide

end ThomGame.Lambda
