module

public import ThomGame.Finite.InvolutionCyclic
public import ThomGame.Finite.PresentedWords
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.DeriveFintype

/-!
# Presentations by involutions with a distinguished central involution

Each indexed relation says that the product of an unsigned word is J to
its parity. J is a fresh generator, separate from every ordinary generator.
The quotient includes all square and centrality relations explicitly.
-/

@[expose] public section
namespace ThomGame

structure InvolutionPresentation (R S : Type*) where
  word : R → List S
  parity : R → ZMod 2

namespace InvolutionPresentation

variable {R S : Type*}

/-- Unordered adjacency, including the cyclic edge from last to first. -/
def Adjacent (w : List S) (s t : S) : Prop :=
  s ≠ t ∧ ((∃ u v, w = u ++ s :: t :: v ∨ w = u ++ t :: s :: v) ∨
    (s ∈ w.getLast? ∧ t ∈ w.head?) ∨ (t ∈ w.getLast? ∧ s ∈ w.head?))

/-- The word form of Slofstra's collegial conditions. The length bound excludes
the empty and one-letter relations; cyclic reduction already rules out a
one-letter word. Finiteness concerns the presentation, not its quotient group. -/
structure Collegial [DecidableEq S] (P : InvolutionPresentation R S) : Prop where
  finite_generators : Finite S
  finite_relations : Finite R
  cyclically_reduced : ∀ r, InvolutionWords.IsCyclicallyReduced (P.word r)
  length_ge_two : ∀ r, 2 ≤ (P.word r).length
  parity_rule : ∀ r₀ s, Odd ((P.word r₀).count s) →
    ∀ r₁ t, Adjacent (P.word r₁) s t → ∀ r, Even ((P.word r).count t)

theorem collegial_of_even [Finite R] [Finite S] [DecidableEq S]
    (P : InvolutionPresentation R S)
    (hc : ∀ r, InvolutionWords.IsCyclicallyReduced (P.word r))
    (hl : ∀ r, 2 ≤ (P.word r).length)
    (he : ∀ r s, Even ((P.word r).count s)) : P.Collegial where
  finite_generators := inferInstance
  finite_relations := inferInstance
  cyclically_reduced := hc
  length_ge_two := hl
  parity_rule r s ho := False.elim ((Nat.not_odd_iff_even.mpr (he r s)) ho)

abbrev Generator (S : Type*) := Option S

inductive RelationTag (R S : Type*)
  | centralSquare
  | variableSquare (s : S)
  | centralCommutes (s : S)
  | equation (r : R)
  deriving DecidableEq, Fintype

def centralWord : Word (Generator S) := Word.generator none

def variableWord (s : S) : Word (Generator S) := Word.generator (some s)

def unsignedWord (w : List S) : Word (Generator S) := w.map fun s => (some s, true)

def rhsWord (P : InvolutionPresentation R S) (r : R) : Word (Generator S) :=
  if P.parity r = 1 then centralWord else []

def relatorWord (P : InvolutionPresentation R S) : RelationTag R S → Word (Generator S)
  | .centralSquare => centralWord ++ centralWord
  | .variableSquare s => variableWord s ++ variableWord s
  | .centralCommutes s => Word.commutator centralWord (variableWord s)
  | .equation r => Word.equation (unsignedWord (P.word r)) (rhsWord P r)

def relators (P : InvolutionPresentation R S) : Set (FreeGroup (Generator S)) :=
  Set.range fun tag => FreeGroup.mk (relatorWord P tag)

abbrev GroupOf (P : InvolutionPresentation R S) := PresentedGroup (relators P)

def J (P : InvolutionPresentation R S) : GroupOf P := PresentedGroup.of none

def x (P : InvolutionPresentation R S) (s : S) : GroupOf P := PresentedGroup.of (some s)

theorem eval_unsignedWord {G : Type*} [Group G] (f : Generator S → G) (w : List S) :
    Word.eval f (unsignedWord w) = (w.map (fun s => f (some s))).prod := by
  simp [Word.eval, FreeGroup.lift_mk, unsignedWord, List.map_map, Function.comp_def]

theorem eval_relation (P : InvolutionPresentation R S) (tag : RelationTag R S) :
    Word.eval (PresentedGroup.of (rels := relators P)) (relatorWord P tag) = 1 := by
  rw [Word.eval_presented]
  exact PresentedGroup.one_of_mem ⟨tag, rfl⟩

theorem J_sq (P : InvolutionPresentation R S) : J P * J P = 1 := by
  simpa [relatorWord, centralWord, J] using eval_relation P .centralSquare

theorem x_sq (P : InvolutionPresentation R S) (s : S) : x P s * x P s = 1 := by
  simpa [relatorWord, variableWord, x] using eval_relation P (.variableSquare s)

theorem J_commutes_x (P : InvolutionPresentation R S) (s : S) : Commute (J P) (x P s) := by
  have h := eval_relation P (.centralCommutes s)
  simp only [relatorWord, Word.eval_commutator, centralWord, variableWord,
    Word.eval_generator, mul_inv_eq_iff_eq_mul] at h
  exact h

theorem J_commutes (P : InvolutionPresentation R S) (g : GroupOf P) : Commute (J P) g := by
  have hgen : ∀ a : Generator S, PresentedGroup.of (rels := relators P) a ∈
      Subgroup.centralizer ({J P} : Set (GroupOf P)) := by
    intro a
    rw [Subgroup.mem_centralizer_singleton_iff]
    cases a with
    | none => rfl
    | some s => exact (J_commutes_x P s).eq.symm
  have h := PresentedGroup.generated_by (relators P)
    (Subgroup.centralizer ({J P} : Set (GroupOf P))) hgen g
  exact (Subgroup.mem_centralizer_singleton_iff.mp h).symm

theorem word_product (P : InvolutionPresentation R S) (r : R) :
    ((P.word r).map (x P)).prod = if P.parity r = 1 then J P else 1 := by
  have h := eval_relation P (.equation r)
  rw [relatorWord, Word.eval_equation_eq_one_iff, eval_unsignedWord] at h
  change ((P.word r).map (x P)).prod =
    Word.eval (PresentedGroup.of (rels := relators P)) (rhsWord P r) at h
  by_cases hp : P.parity r = 1 <;>
    simpa [rhsWord, hp, centralWord, J] using h

theorem relators_finite [Finite R] [Finite S] (P : InvolutionPresentation R S) :
    (relators P).Finite := by
  let := Fintype.ofFinite R
  let := Fintype.ofFinite S
  exact Set.finite_range _

/-- An assignment in a target group satisfying all the defining relations. -/
structure Model (P : InvolutionPresentation R S) (G : Type*) [Group G] where
  j : G
  x : S → G
  j_square : j * j = 1
  x_square : ∀ s, x s * x s = 1
  j_commutes : ∀ s, Commute j (x s)
  word_product : ∀ r, ((P.word r).map x).prod = if P.parity r = 1 then j else 1

namespace Model

variable {P : InvolutionPresentation R S} {G : Type*} [Group G] (M : Model P G)

def assignment : Generator S → G
  | none => M.j
  | some s => M.x s

theorem eval_relator (tag : RelationTag R S) :
    Word.eval M.assignment (relatorWord P tag) = 1 := by
  cases tag with
  | centralSquare => simpa [relatorWord, centralWord, assignment] using M.j_square
  | variableSquare s => simpa [relatorWord, variableWord, assignment] using M.x_square s
  | centralCommutes s =>
    rw [relatorWord, Word.eval_commutator, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    simpa [centralWord, variableWord, assignment] using (M.j_commutes s).eq
  | equation r =>
    rw [relatorWord, Word.eval_equation_eq_one_iff, eval_unsignedWord]
    by_cases hp : P.parity r = 1 <;>
      simpa [rhsWord, hp, centralWord, assignment] using M.word_product r

def toHom : GroupOf P →* G :=
  PresentedGroup.toGroup (f := M.assignment) (rels := relators P) (by
    rintro _ ⟨tag, rfl⟩
    exact M.eval_relator tag)

theorem toHom_J : M.toHom (J P) = M.j := PresentedGroup.toGroup.of _

theorem toHom_x (s : S) : M.toHom (InvolutionPresentation.x P s) = M.x s :=
  PresentedGroup.toGroup.of _

end Model

theorem hom_ext {P : InvolutionPresentation R S} {G : Type*} [Group G]
    {φ ψ : GroupOf P →* G} (hJ : φ (J P) = ψ (J P))
    (hx : ∀ s, φ (x P s) = ψ (x P s)) : φ = ψ := by
  apply PresentedGroup.ext
  intro a
  cases a with
  | none => exact hJ
  | some s => exact hx s

theorem Model.toHom_unique {P : InvolutionPresentation R S} {G : Type*} [Group G]
    (M : Model P G) (φ : GroupOf P →* G)
    (hJ : φ (J P) = M.j) (hx : ∀ s, φ (InvolutionPresentation.x P s) = M.x s) :
    φ = M.toHom := by
  apply hom_ext
  · exact hJ.trans M.toHom_J.symm
  · intro s
    exact (hx s).trans (M.toHom_x s).symm

end InvolutionPresentation
end ThomGame
