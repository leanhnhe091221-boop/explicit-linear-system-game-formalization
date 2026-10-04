module

public import ThomGame.Finite.Words
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sum

/-!
# The complete finite presentation of the compressor group Q

This is the ordered construction in Section 2 of the paper. Root coordinates
are internally zero-based. A coefficient is either `none` (the constant 1),
or a variable axis together with a Boolean exponent sign. This coefficient
sign is independent of the inverse sign of a group-word letter.

The order of `roots`, `coefficients`, and the families below agrees with
`sources/thom_game/generate_game.py`. File equality is audited separately.
-/

@[expose] public section

namespace ThomGame.Compressor

abbrev Axis := Fin 3
abbrev Root := {ij : Axis × Axis // ij.1 ≠ ij.2}
abbrev Coeff := Option (Axis × Bool)
abbrev Generator := (Root × Coeff) ⊕ Root

def roots : List Root :=
  [⟨(0, 1), by decide⟩, ⟨(0, 2), by decide⟩,
   ⟨(1, 0), by decide⟩, ⟨(1, 2), by decide⟩,
   ⟨(2, 0), by decide⟩, ⟨(2, 1), by decide⟩]

def coefficients : List Coeff :=
  [none, some (0, true), some (1, true), some (2, true),
   some (0, false), some (1, false), some (2, false)]

def source (r : Root) : Axis := r.val.1
def target (r : Root) : Axis := r.val.2

/-- In `Fin 3`, the three distinct coordinates sum to zero. -/
def third (r : Root) : Axis := -(source r + target r)

theorem third_ne_source : ∀ r : Root, third r ≠ source r := by decide
theorem third_ne_target : ∀ r : Root, third r ≠ target r := by decide

def across (r : Root) : Root := ⟨(source r, third r), (third_ne_source r).symm⟩
def right (r : Root) : Root := ⟨(target r, third r), (third_ne_target r).symm⟩
def reverse (r : Root) : Root := ⟨(target r, source r), r.property.symm⟩

def separated (r s : Root) : Prop := source r ≠ target s ∧ source s ≠ target r

instance (r s : Root) : Decidable (separated r s) := inferInstanceAs
  (Decidable (source r ≠ target s ∧ source s ≠ target r))

def X (r : Root) (m : Coeff) : Word Generator := Word.generator (.inl (r, m))
def shear (r : Root) : Word Generator := Word.generator (.inr r)

def signed (w : Word Generator) (positive : Bool) : Word Generator :=
  if positive then w else Word.inverse w

def power (w : Word Generator) (n : ℕ) : Word Generator :=
  (List.replicate n w).flatten

def conjugate (u v : Word Generator) : Word Generator := u ++ v ++ Word.inverse u

def e0 : List (Word Generator) :=
  roots.flatMap fun r ↦ coefficients.map fun m ↦ power (X r m) 5

def e1 : List (Word Generator) :=
  roots.flatMap fun r ↦ roots.flatMap fun s ↦
    if separated r s then
      coefficients.flatMap fun m ↦ coefficients.map fun n ↦
        Word.commutator (X r m) (X s n)
    else []

def e2e3 : List (Word Generator) :=
  roots.flatMap fun r ↦ coefficients.flatMap fun m ↦
    [Word.equation (Word.commutator (X r m) (X (right r) none)) (X (across r) m),
     Word.equation (Word.commutator (X r none) (X (right r) m)) (X (across r) m)]

def e4 : List (Word Generator) :=
  roots.flatMap fun r ↦ roots.flatMap fun s ↦
    if separated (across r) s then
      coefficients.flatMap fun m ↦ coefficients.flatMap fun n ↦ coefficients.map fun l ↦
        Word.commutator (Word.commutator (X r m) (X (right r) n)) (X s l)
    else []

def shearComm : List (Word Generator) :=
  roots.flatMap fun r ↦ roots.flatMap fun s ↦
    if separated r s then [Word.commutator (shear r) (shear s)] else []

def shearRoot : List (Word Generator) :=
  roots.map fun r ↦
    Word.equation (Word.commutator (shear r) (shear (right r))) (shear (across r))

def root12 : Root := ⟨(0, 1), by decide⟩

def shearTorsion : List (Word Generator) :=
  [power (shear root12 ++ Word.inverse (shear (reverse root12)) ++ shear root12) 4]

/-- Multiplication of signs, with `true` denoting +1. -/
def signMul (ε σ : Bool) : Bool := if ε then σ else !σ

/-- The right-hand side of the shear action, including the fixed generators. -/
def actionTarget (s r : Root) (ε : Bool) (m : Coeff) : Word Generator :=
  match m with
  | none => X r none
  | some (c, σ) =>
    if c = target s then
      Word.commutator (X (across r) m)
        (X (reverse (right r)) (some (source s, signMul ε σ)))
    else X r m

def actionRelations : List (Word Generator) :=
  roots.flatMap fun s ↦ [true, false].flatMap fun ε ↦
    roots.flatMap fun r ↦ coefficients.map fun m ↦
      Word.equation (conjugate (signed (shear s) ε) (X r m)) (actionTarget s r ε m)

theorem axis_ne_next : ∀ c : Axis, c ≠ finRotate 3 c := by decide

def cyclicRoot (c : Axis) : Root := ⟨(c, finRotate 3 c), axis_ne_next c⟩

def recoveryWord (c : Axis) : Word Generator :=
  let r := cyclicRoot c
  power (shear r ++ Word.inverse (shear (reverse r)) ++ shear r) 2

def negativeRecovery : List (Word Generator) :=
  (List.finRange 3).flatMap fun c ↦ roots.map fun r ↦
    Word.equation (conjugate (recoveryWord c) (X r (some (c, true))))
      (X r (some (c, false)))

/-- All raw relations, with precisely the family's generation order in the source. -/
def rawRelators : List (Word Generator) :=
  e0 ++ e1 ++ e2e3 ++ e4 ++ shearComm ++ shearRoot ++ shearTorsion ++
    actionRelations ++ negativeRecovery

/-- The relation set in the free group; repetitions in the raw list have no effect. -/
def relators : Set (FreeGroup Generator) := FreeGroup.mk '' {w | w ∈ rawRelators}

/-- The group Q is a concrete quotient of the free group on its 48 generators. -/
def GroupQ := PresentedGroup relators
  deriving Group

theorem root_card : Fintype.card Root = 6 := by decide
theorem coeff_card : Fintype.card Coeff = 7 := by decide

theorem generator_card : Fintype.card Generator = 48 := by
  change Fintype.card ((Root × Coeff) ⊕ Root) = 48
  rw [Fintype.card_sum, Fintype.card_prod, root_card, coeff_card]

/-- The published one-based numerical ID of an unsigned generator. -/
def generatorNumber : Generator → Nat
  | .inl (r, m) => 7 * roots.idxOf r + coefficients.idxOf m + 1
  | .inr r => 43 + roots.idxOf r

/-- The signed-integer word convention used by the supplied JSON files. -/
def signedNumbers (w : Word Generator) : List Int :=
  w.map fun (g, positive) ↦
    if positive then (generatorNumber g : Int) else -(generatorNumber g : Int)

end ThomGame.Compressor
